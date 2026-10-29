import type { Expression, Node, SequenceExpression, Statement } from "../core/ast.js";
import { isJump } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import { constantEnv } from "../core/constants.js";
import type { EvaluateEnv, Evaluation, Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import { deadRemainder, hoistedNames, isPlaceholder, placeholderDeclaration } from "../core/hoisting.js";
import type { ScopeInfo } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Path } from "../core/traverse.js";
import type { Facts } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

/** Constant bindings are only copied into their uses when the copy is small. */
const MAX_PROPAGATED_STRING = 64;

/** Expression types worth trying to fold (others either can't evaluate or are already literals). */
const FOLDABLE = new Set(["Identifier", "BinaryExpression", "UnaryExpression", "LogicalExpression", "ConditionalExpression", "TemplateLiteral", "MemberExpression", "SequenceExpression"]);

/** Whether `node` already is the canonical expression for `value` (`3`, `-1`, `undefined`, `NaN`, `Infinity`). */
const isCanonical = (node: Node, value: Value): boolean => {
    switch (node.type) {
        case "Literal":
            return Object.is(node.value, value);
        case "Identifier":
            return (node.name === "undefined" && value === undefined) || (node.name === "NaN" && Number.isNaN(value)) || (node.name === "Infinity" && value === Number.POSITIVE_INFINITY);
        case "UnaryExpression":
            return node.operator === "-" && typeof value === "number" && (value < 0 || Object.is(value, -0)) && isCanonical(node.argument, -value);
        default:
            return false;
    }
};

/** Statements of a taken branch, inlined where block scoping allows. */
const branchStatements = (branch: Statement | null | undefined): Statement[] => {
    if (branch === null || branch === undefined) return [];
    if (branch.type !== "BlockStatement") return [branch];
    const scoped = branch.body.some((s) => (s.type === "VariableDeclaration" && s.kind !== "var") || s.type === "ClassDeclaration" || s.type === "FunctionDeclaration");
    return scoped ? [branch] : branch.body;
};

/** Replace a statement by zero or more statements doing what it did, wherever it sits, and tell `facts`. */
const replaceStatement = (path: Path, statements: Statement[], facts: Facts): void => {
    const original = path.node;
    if (path.isInStatementList()) {
        facts.replaced([original], statements);
        const [first, ...rest] = statements;
        if (first === undefined) {
            path.remove();
            return;
        }
        path.replace(first);
        path.insertAfter(rest);
        return;
    }
    const replacement = statements.length === 1 && statements[0] !== undefined ? statements[0] : at<Statement>({ type: "BlockStatement", body: statements }, original);
    facts.replaced([original], [replacement]);
    path.replace(replacement);
};

const sequence = (expressions: Expression[], origin: Node): SequenceExpression => at<SequenceExpression>({ type: "SequenceExpression", expressions }, origin);
const prefixAndLast = (s: SequenceExpression): [Expression[], Expression] => [s.expressions.slice(0, -1), s.expressions.at(-1) as Expression];

/** Callee of a call or tag of a tagged template: positions where the callee's reference decides `this`. */
const isCallee = (path: Path): boolean => (path.parent?.type === "CallExpression" && path.key === "callee") || (path.parent?.type === "TaggedTemplateExpression" && path.key === "tag");

/**
 * Where an expression's reference-ness matters, so a bare `e` and `(0, e)` differ: as a callee or tag (`this`, direct
 * `eval`) and under `typeof`/`delete` (an undeclared name, a deletable binding).
 */
const keepsSequence = (path: Path, last: Expression): boolean => {
    if (isCallee(path)) return last.type === "MemberExpression" || (last.type === "Identifier" && last.name === "eval");
    const parent = path.parent;
    return parent?.type === "UnaryExpression" && (parent.operator === "typeof" || parent.operator === "delete") && (last.type === "Identifier" || last.type === "MemberExpression");
};

/**
 * Simplify: constant folding, constant propagation, sequence hoisting and dead-code removal. Runs in a fixpoint group
 * with normalize and unflatten: resolved decoder strings and prelude results make opaque predicates constant, dead
 * branches fall away, and the machines whose states became constant can be unflattened in the next round.
 *
 * Every rewrite is exact. Dropped code keeps what it declares beyond itself (`var` and Annex B function names; `let`
 * placeholders for lexical names of a dead statement list), so no binding changes scope. Constant bindings and
 * `arguments` slots come from `constantEnv`.
 */
export const simplify: Pass = {
    name: "simplify",
    description: "Fold constants, hoist sequences, drop dead branches and unreachable code",
    run({ program, log, scope, facts }: PassContext): PassResult {
        const scopes: ScopeInfo = scope();
        const env: EvaluateEnv = { ...constantEnv(scopes, log), cache: new WeakMap<Node, Evaluation>() };
        const counts = { folded: 0, propagated: 0, hoisted: 0, branches: 0, unreachable: 0, pure: 0 };

        /** Whether a fold at `path` can change only the value, not what the code does with the expression. */
        const foldablePosition = (path: Path): boolean => {
            const parent = path.parent;
            if (parent === null || path.isWriteTarget() || isCallee(path)) return false;
            if (parent.type === "TaggedTemplateExpression" && path.key === "quasi") return false;
            if (parent.type === "ExportSpecifier") return false;
            const node = path.node;
            return node.type !== "Identifier" || scopes.referenceOf(node)?.isRead() === true;
        };

        const fold = (path: Path, node: Expression): boolean => {
            if (!foldablePosition(path)) return false;
            const result = evaluate(node, env);
            if (!result.ok || isCanonical(node, result.value)) return false;
            const value: Value = result.value;
            const replacement = valueToNode(value, node);
            // `undefined`, `NaN`, `Infinity` (possibly under a minus) are names: not usable where a local takes them.
            const named = replacement.type === "UnaryExpression" ? replacement.argument : replacement;
            if (named.type === "Identifier" && scopes.declaresName(named.name)) return false;
            if (node.type === "Identifier") {
                if (typeof value === "string" && value.length > MAX_PROPAGATED_STRING) return false;
                counts.propagated++;
            } else {
                counts.folded++;
            }
            // A shorthand property's value can't stand alone: `{ x }` -> `{ x: 5 }`.
            const parent = path.parent;
            if (parent?.type === "Property" && path.key === "value" && parent.shorthand) parent.shorthand = false;
            if (log.debugging) log.debug(`${node.type === "Identifier" ? "propagated" : "folded"} to ${typeof value === "string" ? JSON.stringify(value).slice(0, 40) : String(value)}`, node);
            path.replace(replacement);
            return true;
        };

        /** `(a, v) OP x` and friends -> `(a, v OP x)`, and flattening of sequences. */
        const hoist = (path: Path): boolean => {
            const node = path.node;
            switch (node.type) {
                case "BinaryExpression":
                case "LogicalExpression": {
                    if (node.left.type === "SequenceExpression") {
                        const [prefix, last] = prefixAndLast(node.left);
                        path.replace(sequence([...prefix, { ...node, left: last } as Expression], node));
                        return true;
                    }
                    // `L OP (a, v)` -> `(a, L OP v)`: only when L is a pure constant, and never for && || ?? (they may skip `a`).
                    if (node.type === "BinaryExpression" && node.right.type === "SequenceExpression" && node.left.type !== "PrivateIdentifier" && evaluate(node.left, env).ok) {
                        const [prefix, last] = prefixAndLast(node.right);
                        path.replace(sequence([...prefix, { ...node, right: last } as Expression], node));
                        return true;
                    }
                    return false;
                }
                case "UnaryExpression": {
                    if (node.operator === "delete" || node.argument.type !== "SequenceExpression") return false;
                    const [prefix, last] = prefixAndLast(node.argument);
                    // `typeof (a, x)` reads x (and throws when it's undeclared); `typeof x` doesn't.
                    if (node.operator === "typeof" && last.type === "Identifier") return false;
                    path.replace(sequence([...prefix, { ...node, argument: last } as Expression], node));
                    return true;
                }
                case "ConditionalExpression": {
                    if (node.test.type !== "SequenceExpression") return false;
                    const [prefix, last] = prefixAndLast(node.test);
                    path.replace(sequence([...prefix, { ...node, test: last } as Expression], node));
                    return true;
                }
                case "MemberExpression": {
                    // `(a, o).m` -> `(a, o.m)` only as a plain read: not as a callee or tag (`this` would be lost), not
                    // as a target of `=`, `++` or `delete`, not inside an optional chain.
                    if (node.object.type !== "SequenceExpression" || node.optional || isCallee(path) || path.isWriteTarget() || path.parent?.type === "ChainExpression") return false;
                    const [prefix, last] = prefixAndLast(node.object);
                    path.replace(sequence([...prefix, { ...node, object: last } as Expression], node));
                    return true;
                }
                case "SequenceExpression": {
                    // Flatten nested sequences; drop pure non-final elements, but keep `(0, e)` where it matters.
                    const flat = node.expressions.flatMap((e) => (e.type === "SequenceExpression" ? e.expressions : [e]));
                    let kept = flat.filter((e, i) => i === flat.length - 1 || !evaluate(e, env).ok);
                    const last = kept.at(-1) as Expression;
                    if (kept.length === 1 && keepsSequence(path, last)) {
                        if (flat.length === 2 && node.expressions.length === 2) return false; // already `(pure, e)`
                        kept = [valueToNode(0, node), last];
                    }
                    if (kept.length === node.expressions.length && kept.every((e, i) => e === node.expressions[i])) return false;
                    path.replace(kept.length === 1 ? last : sequence(kept, node));
                    return true;
                }
                default:
                    return false;
            }
        };

        /** Branches decided by a constant. */
        const prune = (path: Path): boolean => {
            const node = path.node;
            switch (node.type) {
                case "IfStatement": {
                    const test = evaluate(node.test, env);
                    if (!test.ok) return false;
                    const taken = test.value ? node.consequent : node.alternate;
                    const dropped = test.value ? node.alternate : node.consequent;
                    const keep = placeholderDeclaration("var", dropped === null ? new Set() : hoistedNames(dropped), node);
                    replaceStatement(path, [...keep, ...branchStatements(taken)], facts);
                    log.debug(`if (${String(test.value)}): kept the ${test.value ? "then" : "else"} branch`, node);
                    return true;
                }
                case "ConditionalExpression": {
                    const test = evaluate(node.test, env);
                    if (!test.ok) return false;
                    log.debug(`${String(test.value)} ? ... : ...: kept the ${test.value ? "first" : "second"} value`, node);
                    path.replace(test.value ? node.consequent : node.alternate);
                    return true;
                }
                case "LogicalExpression": {
                    const left = evaluate(node.left, env);
                    if (!left.ok) return false;
                    const shortCircuit = node.operator === "&&" ? !left.value : node.operator === "||" ? Boolean(left.value) : left.value !== null && left.value !== undefined;
                    log.debug(`${node.operator} with a constant left side: ${shortCircuit ? "short-circuits" : "is its right side"}`, node);
                    path.replace(shortCircuit ? node.left : node.right);
                    return true;
                }
                case "WhileStatement":
                case "ForStatement": {
                    if (node.test === null) return false;
                    const test = evaluate(node.test, env);
                    if (!test.ok || test.value) return false;
                    const init: Statement[] = [];
                    if (node.type === "ForStatement" && node.init !== null) {
                        const head = node.init;
                        if (head.type !== "VariableDeclaration") init.push(at<Statement>({ type: "ExpressionStatement", expression: head }, head));
                        else if (head.kind === "var") init.push(head);
                        // A lexical init is scoped to the loop: pure, it simply goes; otherwise it keeps its own block.
                        else if (!head.declarations.every((d) => d.init === null || evaluate(d.init, env).ok)) init.push(at<Statement>({ type: "BlockStatement", body: [head] }, head));
                    }
                    log.debug("loop test is false: the loop never runs", node);
                    replaceStatement(path, [...init, ...placeholderDeclaration("var", hoistedNames(node.body), node)], facts);
                    return true;
                }
                default:
                    return false;
            }
        };

        /** Statements after return/throw/break/continue, and pure expression statements. */
        const sweep = (body: Statement[]): void => {
            const terminal = body.findIndex(isJump);
            if (terminal !== -1 && terminal < body.length - 1 && !body.slice(terminal + 1).every(isPlaceholder)) {
                const end = body[terminal] as Statement;
                const dead = body.splice(terminal + 1);
                body.push(...deadRemainder(dead, end));
                const dropped = dead.filter((s) => !isPlaceholder(s)).length;
                counts.unreachable += dropped;
                log.debug(`removed ${dropped} unreachable statement(s)`, end);
            }
            for (let i = body.length - 1; i >= 0; i--) {
                const s = body[i] as Statement;
                if (s.type !== "ExpressionStatement" || ("directive" in s && typeof s.directive === "string")) continue;
                if (!evaluate(s.expression, env).ok) continue;
                log.debug("removed a statement with no effect", s);
                body.splice(i, 1);
                counts.pure++;
            }
        };

        traverse(program, {
            exit(path) {
                const node = path.node;
                if (prune(path)) {
                    counts.branches++;
                    return;
                }
                if (hoist(path)) {
                    counts.hoisted++;
                    return;
                }
                if (node.type === "BlockStatement" || node.type === "Program" || node.type === "StaticBlock") sweep(node.body as Statement[]);
                else if (node.type === "SwitchCase") sweep(node.consequent);
                else if (FOLDABLE.has(node.type)) fold(path, node as Expression);
            },
        });

        const changed = counts.folded + counts.propagated + counts.hoisted + counts.branches + counts.unreachable + counts.pure;
        log.info(
            `folded ${counts.folded}, propagated ${counts.propagated} constant(s), hoisted ${counts.hoisted} sequence(s), decided ${counts.branches} branch(es), removed ${counts.unreachable} unreachable and ${counts.pure} pure statement(s)`
        );
        // Folds and prunes stay in their scope; dropped code leaves its declarations behind (placeholders).
        return { changed, bindingsChanged: false, stats: counts };
    },
};
