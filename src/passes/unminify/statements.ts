import type {
    AssignmentExpression,
    BlockStatement,
    Expression,
    ForStatement,
    IfStatement,
    LabeledStatement,
    Node,
    ObjectExpression,
    Statement,
    VariableDeclaration,
    VariableDeclarator,
} from "../../core/ast.js";
import { isFunctionNode, isJump } from "../../core/ast.js";
import { at } from "../../core/build.js";
import { deadRemainder, isPlaceholder } from "../../core/hoisting.js";
import { forEachChild, traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";
import type { PlannedStore } from "./expressions.js";
import { builderHolder, isPlainLiteral, not, plannedStore } from "./expressions.js";

const block = (body: Statement[], origin: Node): BlockStatement => at<BlockStatement>({ type: "BlockStatement", body }, origin);
const expressionStatement = (expression: Expression): Statement => at<Statement>({ type: "ExpressionStatement", expression }, expression);
const returning = (value: Expression): BlockStatement => block([at<Statement>({ type: "ReturnStatement", argument: value }, value)], value);
const declaration = (node: VariableDeclaration, declarators: VariableDeclarator[]): VariableDeclaration =>
    at<VariableDeclaration>({ type: "VariableDeclaration", kind: node.kind, declarations: declarators }, declarators[0] ?? node);

const refersTo = (node: Node | null, context: UnminifyContext, variable: unknown): boolean => {
    if (node === null) return false;
    if (node.type === "Identifier") return context.scopes.variableOf(node) === variable;
    let found = false;
    forEachChild(node, (child) => {
        found ||= refersTo(child, context, variable);
    });
    return found;
};

/**
 * `for (var a = 1, i = 0; i < n; i++)` -> `var a = 1; for (var i = 0; i < n; i++)`: the leading declarators that the
 * test and update don't use move before the loop. Only `var` (a `let` in the head is a fresh binding per iteration
 * and scoped to the loop) and only leading ones, so the initializers keep their order.
 */
const splitForLoopVars = (node: ForStatement, context: UnminifyContext): Statement[] | undefined => {
    const init = node.init;
    if (init?.type !== "VariableDeclaration") return undefined;
    if (init.kind !== "var") {
        if (init.declarations.length > 1) context.refused(`keeps the loop head's ${init.kind} declarations: each iteration has its own`, node);
        return undefined;
    }
    let hoisted = 0;
    for (const declarator of init.declarations) {
        if (declarator.id.type !== "Identifier") break;
        const variable = context.scopes.variableOf(declarator.id);
        if (variable === undefined || refersTo(node.test, context, variable) || refersTo(node.update, context, variable)) break;
        hoisted++;
    }
    if (hoisted === 0) {
        if (init.declarations.length > 1) context.refused("keeps the loop head's declarations: the first is used by the test or update", node);
        return undefined;
    }
    context.did("splitForLoopVars", node);
    const moved = init.declarations.slice(0, hoisted).map((declarator) => declaration(init, [declarator]));
    const rest = init.declarations.slice(hoisted);
    return [...moved, at<ForStatement>({ ...node, init: rest.length === 0 ? null : declaration(init, rest) }, node)];
};

/** `(a, b, c)` as its leading expressions, statements of their own, and the last one; `undefined` for anything else. */
const splitSequence = (expression: Expression | null | undefined, context: UnminifyContext, statement: Statement): { before: Statement[]; last: Expression } | undefined => {
    if (expression?.type !== "SequenceExpression") return undefined;
    const last = expression.expressions.at(-1) as Expression;
    context.did("sequences", statement);
    return { before: expression.expressions.slice(0, -1).map(expressionStatement), last };
};

/** Whether a `break`/`continue` under `node` names `label` (labels don't reach into functions). */
const jumpsTo = (node: Node | null | undefined, label: string): boolean => {
    if (node === null || node === undefined || isFunctionNode(node)) return false;
    if ((node.type === "BreakStatement" || node.type === "ContinueStatement") && node.label?.name === label) return true;
    let found = false;
    forEachChild(node, (child) => {
        found ||= jumpsTo(child, label);
    });
    return found;
};

const isBreakingIf = (statement: Statement, label: string): statement is IfStatement & { consequent: BlockStatement } => {
    if (statement.type !== "IfStatement" || statement.alternate !== null || statement.consequent.type !== "BlockStatement") return false;
    const last = statement.consequent.body.at(-1);
    return last?.type === "BreakStatement" && last.label?.name === label;
};

const isLexical = (statement: Statement): boolean =>
    (statement.type === "VariableDeclaration" && statement.kind !== "var") || statement.type === "ClassDeclaration" || statement.type === "FunctionDeclaration";

/**
 * A statement list that ends where `label`'s block ends, without its breaks to `label`: `if (c) { x; break label; }
 * rest` -> `if (c) { x } else { rest }` (each break skips to the end of the block, which is what the `else` does; `x`
 * too ends there, so its own breaks go the same way), also inside the last statement when it is an `if` (both
 * branches end where the list does) or a block, and a last `break label;` dropped. `undefined` when another jump
 * names the label, or a block-scoped declaration in `rest` would move into the `else`.
 */
const withoutTailBreaks = (list: readonly Statement[], label: string): Statement[] | undefined => {
    for (const [i, statement] of list.entries()) {
        const last = i === list.length - 1;
        if (statement.type === "BreakStatement" && statement.label?.name === label) return last ? list.slice(0, i) : undefined;
        if (isBreakingIf(statement, label)) {
            const rest = list.slice(i + 1);
            const alternate = rest.some(isLexical) ? undefined : withoutTailBreaks(rest, label);
            const taken = withoutTailBreaks(statement.consequent.body.slice(0, -1), label);
            if (alternate === undefined || taken === undefined) return undefined;
            const consequent = block(taken, statement.consequent);
            const otherwise = alternate.length === 0 ? null : block(alternate, rest[0] as Statement);
            return [...list.slice(0, i), at<IfStatement>({ type: "IfStatement", test: statement.test, consequent, alternate: otherwise }, statement)];
        }
        if (!jumpsTo(statement, label)) continue;
        if (!last) return undefined;
        if (statement.type === "BlockStatement") {
            const body = withoutTailBreaks(statement.body, label);
            return body === undefined ? undefined : [...list.slice(0, i), block(body, statement)];
        }
        if (statement.type !== "IfStatement") return undefined;
        const branch = (taken: Statement): Statement | undefined => {
            const body = withoutTailBreaks(taken.type === "BlockStatement" ? taken.body : [taken], label);
            // An `else if` stays one.
            return body === undefined ? undefined : taken.type !== "BlockStatement" && body.length === 1 && body[0]?.type === "IfStatement" ? body[0] : block(body, taken);
        };
        const consequent = branch(statement.consequent);
        const alternate = statement.alternate === null ? null : branch(statement.alternate);
        if (consequent === undefined || alternate === undefined) return undefined;
        return [...list.slice(0, i), at<IfStatement>({ type: "IfStatement", test: statement.test, consequent, alternate }, statement)];
    }
    return [...list];
};

/**
 * `label: { a; if (c1) { x; break label; } if (c2) { y; break label; } rest }` -> `a; if (c1) { x } else if (c2) { y }
 * else { rest }` (the unflattener's exits), breaks nested in a last `if` too (`withoutTailBreaks`), when no other jump
 * names the label. Block-scoped declarations keep a block around the result. First, when the block ends with a loop,
 * the loop's own breaks to the label lose it (`plainJumps`): leaving the loop reaches the end of the block too.
 */
const unlabelBlock = (statement: LabeledStatement, context: UnminifyContext): Statement[] | undefined => {
    if (statement.body.type !== "BlockStatement") return undefined;
    const label = statement.label.name;
    const last = statement.body.body.at(-1);
    if (last !== undefined && LOOPS.has(last.type)) for (const jump of plainJumps(last, label, "same") ?? []) (jump as Statement & { label: unknown }).label = null;
    const body = withoutTailBreaks(statement.body.body, label);
    if (body === undefined || body.some((s) => jumpsTo(s, label))) return undefined;
    context.did("labeledBlocks", statement);
    return body.some(isLexical) ? [block(body, statement)] : body;
};

/**
 * `label: { ... break label; ... } jump;` -> its statements, each break a copy of `jump`: a `break`, `continue` or
 * `return;` right after the block (or the end of the function the block ends: a `return;`, `finally` blocks run
 * either way), which is where leaving it leads. An unlabeled `break`/`continue` copy needs each break outside any loop
 * (and `switch`, for `break`) of the block, so that it reaches the same loop. Block-scoped declarations keep a block
 * around the statements.
 */
const forwardBreaks = (statement: LabeledStatement, next: Statement | undefined, context: UnminifyContext): Statement[] | undefined => {
    if (statement.body.type !== "BlockStatement" || next === undefined) return undefined;
    const plainNext = (next.type === "BreakStatement" || next.type === "ContinueStatement") && next.label === null;
    if (next.type !== "BreakStatement" && next.type !== "ContinueStatement" && !(next.type === "ReturnStatement" && next.argument === null)) return undefined;
    const label = statement.label.name;
    const breaks = plainNext ? plainJumps(statement.body, label, next.type) : allJumps(statement.body, label);
    if (breaks === undefined) return undefined;
    const copy = (origin: Node): Statement => {
        if (next.type === "ReturnStatement") return at<Statement>({ type: "ReturnStatement", argument: null }, origin);
        const target = next.label === null ? null : at<Node & { type: "Identifier" }>({ type: "Identifier", name: next.label.name }, origin);
        return at<Statement>(next.type === "BreakStatement" ? { type: "BreakStatement", label: target } : { type: "ContinueStatement", label: target }, origin);
    };
    replaceJumps(statement.body, new Map(breaks.map((jump) => [jump as Node, copy(jump)])));
    context.did("labeledBlocks", statement);
    const body = statement.body.body;
    return body.some(isLexical) ? [statement.body] : body;
};

const allJumps = (node: Node, label: string): Statement[] => {
    const jumps: Statement[] = [];
    const visit = (child: Node): void => {
        if (isFunctionNode(child)) return;
        if ((child.type === "BreakStatement" || child.type === "ContinueStatement") && child.label?.name === label) jumps.push(child);
        else forEachChild(child, visit);
    };
    forEachChild(node, visit);
    return jumps;
};

const replaceJumps = (node: Node, replacements: ReadonlyMap<Node, Statement>): void => {
    traverse(node, {
        enter(path) {
            if (isFunctionNode(path.node)) path.skip();
        },
        BreakStatement(path) {
            const replacement = replacements.get(path.node);
            if (replacement !== undefined) path.replace(replacement);
        },
    });
};

const LOOPS: ReadonlySet<string> = new Set(["WhileStatement", "DoWhileStatement", "ForStatement", "ForInStatement", "ForOfStatement"]);

/**
 * The jumps to `label` under `node` (not in functions), when none is in a loop of `node`, nor in a `switch` of it
 * when it is (or becomes, `as`) a `break`: then the jump without its label, or the unlabeled jump it becomes, reaches
 * the loop around `node` (or `node`'s own, for its children). `undefined` otherwise.
 */
const plainJumps = (node: Node, label: string, as: "same" | "BreakStatement" | "ContinueStatement"): Statement[] | undefined => {
    const jumps: Statement[] = [];
    let plain = true;
    const visit = (child: Node, inLoop: boolean, inSwitch: boolean): void => {
        if (!plain || isFunctionNode(child)) return;
        if ((child.type === "BreakStatement" || child.type === "ContinueStatement") && child.label?.name === label) {
            if (inLoop || ((as === "same" ? child.type : as) === "BreakStatement" && inSwitch)) plain = false;
            else jumps.push(child);
            return;
        }
        forEachChild(child, (grandchild) => visit(grandchild, inLoop || LOOPS.has(child.type), inSwitch || child.type === "SwitchStatement"));
    };
    forEachChild(node, (child) => visit(child, false, false));
    return plain ? jumps : undefined;
};

/**
 * `label: while (c) { ... continue label; ... break label; }` -> the loop unlabeled, when each jump to the label is
 * in no inner loop (and a `break` in no `switch`) of it (`plainJumps`): the same jump without the label goes to the
 * same place.
 */
const unlabelLoop = (statement: LabeledStatement, context: UnminifyContext): Statement[] | undefined => {
    const loop = statement.body;
    if (!LOOPS.has(loop.type)) return undefined;
    const jumps = plainJumps(loop, statement.label.name, "same");
    if (jumps === undefined) return undefined;
    for (const jump of jumps) (jump as Statement & { label: unknown }).label = null;
    context.did("labeledLoops", statement);
    return [loop];
};

/**
 * The statements a listed statement becomes (`undefined`: itself). Splitting a sequence out of `return`/`throw`/an
 * `if` test/a `switch` discriminant/a lone initializer is exact: the leading expressions run first either way, and a
 * `let`/`const` name is in its dead zone for them either way.
 */
const expandStatement = (statement: Statement, context: UnminifyContext): Statement[] | undefined => {
    switch (statement.type) {
        case "ExpressionStatement": {
            if (statement.expression.type !== "SequenceExpression") return undefined;
            context.did("sequences", statement);
            return statement.expression.expressions.map(expressionStatement);
        }
        case "ThrowStatement": {
            const split = splitSequence(statement.argument, context, statement);
            return split && [...split.before, at<Statement>({ ...statement, argument: split.last }, statement)];
        }
        case "IfStatement": {
            const split = splitSequence(statement.test, context, statement);
            return split && [...split.before, at<Statement>({ ...statement, test: split.last }, statement)];
        }
        case "SwitchStatement": {
            const split = splitSequence(statement.discriminant, context, statement);
            return split && [...split.before, at<Statement>({ ...statement, discriminant: split.last }, statement)];
        }
        case "VariableDeclaration":
            if (statement.declarations.length === 1) {
                const [declarator] = statement.declarations as [VariableDeclarator];
                const split = statement.kind === "using" || statement.kind === "await using" ? undefined : splitSequence(declarator.init, context, statement);
                return split && [...split.before, declaration(statement, [at<VariableDeclarator>({ ...declarator, init: split.last }, declarator)])];
            }
            // `using` declarations are disposed of together at the end of the block: leave them be.
            if (statement.kind === "using" || statement.kind === "await using") {
                context.refused("keeps a `using` declaration whole", statement);
                return undefined;
            }
            context.did("splitDeclarations", statement);
            return statement.declarations.map((declarator) => declaration(statement, [declarator]));
        case "ExportNamedDeclaration": {
            const inner = statement.declaration;
            if (inner?.type !== "VariableDeclaration" || inner.declarations.length < 2 || inner.kind === "using" || inner.kind === "await using") return undefined;
            context.did("splitDeclarations", statement);
            return inner.declarations.map((declarator) => at<Statement>({ ...statement, declaration: declaration(inner, [declarator]) }, declarator));
        }
        case "ReturnStatement": {
            const argument = statement.argument;
            const split = splitSequence(argument, context, statement);
            if (split !== undefined) return [...split.before, at<Statement>({ type: "ReturnStatement", argument: split.last }, statement)];
            if (argument?.type !== "UnaryExpression" || argument.operator !== "void") return undefined;
            context.did("returnVoid", statement);
            return [expressionStatement(argument.argument), at<Statement>({ type: "ReturnStatement", argument: null }, statement)];
        }
        case "ForStatement":
            return splitForLoopVars(statement, context);
        default:
            return undefined;
    }
};

/** `functionBody`: a block ending the function body may forward its breaks to a `return;`. */
const unlabel = (list: readonly Statement[], index: number, context: UnminifyContext, functionBody: boolean): Statement[] | undefined => {
    const statement = list[index] as Statement;
    if (statement.type !== "LabeledStatement") return undefined;
    const ending = functionBody && index === list.length - 1 ? at<Statement>({ type: "ReturnStatement", argument: null }, statement) : undefined;
    return unlabelBlock(statement, context) ?? unlabelLoop(statement, context) ?? forwardBreaks(statement, list[index + 1] ?? ending, context);
};

/** Statements after a jump go (`deadRemainder` keeps the declarations they hoist). */
const dropUnreachable = (list: Statement[], context: UnminifyContext): void => {
    const jump = list.findIndex(isJump);
    if (jump === -1 || jump === list.length - 1 || list.slice(jump + 1).every(isPlaceholder)) return;
    context.did("unreachable", list[jump + 1] as Statement);
    list.push(...deadRemainder(list.splice(jump + 1), list[jump] as Statement));
};

/**
 * Repeats on what an expansion made, then drops unreachable statements and merges object assignments and copies; a
 * copy can put a literal under the name the stores use (`t = {...}; o = t; o.a = x;`), so the merge runs again.
 */
export const expandStatements = (list: Statement[], context: UnminifyContext, functionBody = false): void => {
    for (let i = 0; i < list.length; i++) {
        const statements = expandStatement(list[i] as Statement, context) ?? unlabel(list, i, context, functionBody);
        if (statements === undefined) continue;
        list.splice(i, 1, ...statements);
        i--;
    }
    dropUnreachable(list, context);
    mergeObjectAssignments(list, context);
    if (mergeCopies(list, context)) mergeObjectAssignments(list, context);
};

/**
 * Labels again once the list's own statements are done (the walk's exit): their rewrites may have turned breaks into
 * jumps to a label of this list (a nested block's breaks forwarded to `break outer;`). The `if`s an unlabeled block
 * becomes get their `else if`s merged here, past their own exit. Then loops get rebuilt (`rebuildLoop`), and a bare
 * `return;` ending a function body goes (the end returns undefined too).
 */
export const unlabelStatements = (list: Statement[], context: UnminifyContext, functionBody = false): void => {
    let changed = false;
    for (let i = 0; i < list.length; i++) {
        const statements = unlabel(list, i, context, functionBody);
        if (statements === undefined) continue;
        list.splice(i, 1, ...statements);
        changed = true;
        for (const statement of statements) traverse(statement, { exit: (path) => mergeElseIf(path.node, context) });
        i--;
    }
    if (changed) dropUnreachable(list, context);
    for (let i = 0; i < list.length; i++) {
        const statements = rebuildLoop(list[i] as Statement, context);
        if (statements === undefined) continue;
        list.splice(i, 1, ...statements);
        i += statements.length - 1;
    }
    const last = list.at(-1);
    if (functionBody && last?.type === "ReturnStatement" && last.argument === null) {
        context.did("returnVoid", last);
        list.pop();
    }
};

/** Plain `break`s under `node` (not in a function, loop or `switch` of it): they leave the loop `node` sits in. */
const breaksOut = (node: Node): boolean => {
    if (isFunctionNode(node) || LOOPS.has(node.type) || node.type === "SwitchStatement") return false;
    if (node.type === "BreakStatement") return node.label === null;
    let found = false;
    forEachChild(node, (child) => {
        found ||= breaksOut(child);
    });
    return found;
};

/** Conservative: false only for a jump, or a block or `if`/`else` all of whose ends are jumps. */
const completes = (statement: Statement | undefined): boolean => {
    if (statement === undefined) return true;
    if (isJump(statement)) return false;
    if (statement.type === "BlockStatement") return completes(statement.body.at(-1));
    return statement.type !== "IfStatement" || statement.alternate === null || completes(statement.consequent) || completes(statement.alternate);
};

const statementsOf = (statement: Statement): Statement[] => (statement.type === "BlockStatement" ? statement.body : [statement]);

/** `body` without a `continue;` ending it: that jump goes where the end of the body falls through to. */
const withoutTailContinue = (body: Statement[], context: UnminifyContext): Statement[] => {
    const last = body.at(-1);
    if (last?.type !== "ContinueStatement" || last.label !== null) return body;
    context.did("loops", last);
    return body.slice(0, -1);
};

/**
 * `t` followed by a `break;` that leaves the loop, as statements that end in the break only where `t` completes: when
 * `t` ends with `if (d) { a } else { b }` and one branch never completes, the break goes into the other and the
 * jumping branch's statements follow the `if` (`if (d) { a; break; } b`), which is where only it led. `undefined`
 * when the break can't be placed so (or `b` declares block-scoped names, which would leave its block).
 */
const thenBreak = (t: readonly Statement[], origin: Node): Statement[] | undefined => {
    const last = t.at(-1);
    if (!completes(last)) return [...t];
    if (last?.type !== "IfStatement" || last.alternate === null) return undefined;
    const exit = at<Statement>({ type: "BreakStatement", label: null }, origin);
    const consequent = statementsOf(last.consequent);
    const alternate = statementsOf(last.alternate);
    const keep = t.slice(0, -1);
    // `last` completes, so at most one branch is a jump.
    if (!completes(last.alternate) && !alternate.some(isLexical)) {
        return [...keep, at<IfStatement>({ ...last, consequent: block([...consequent, exit], last.consequent), alternate: null }, last), ...alternate];
    }
    if (!completes(last.consequent) && !consequent.some(isLexical)) {
        return [...keep, at<IfStatement>({ ...last, test: not(last.test, last.test), consequent: block([...alternate, exit], last.alternate), alternate: null }, last), ...consequent];
    }
    return undefined;
};

/**
 * The `while (true)` shells the unflattener leaves, as conditional loops; also a `continue;` ending any loop's body
 * goes (`withoutTailContinue`). Every jump keeps its target: the loop is unlabeled, so only plain jumps outside inner
 * loops (and `switch`es, for `break`) reach it, and the rewrites move none of those across a loop boundary.
 *
 *     while (true) { if (c) break; rest }   ->  while (!c) { rest }
 *     while (true) { if (c) { t } jump }    ->  while (c) { t; break; } jump
 *
 * In the second, `jump` (a `return`, `throw`, labeled jump or `break;`) never goes back to the test, so the loop only
 * repeats through `t`'s `continue`s, which test `c` again either way; a `t` that completes leaves the loop to `jump`
 * as before (`thenBreak` places that break). No plain `break` in `t` unless `jump` is one: it would skip `jump`.
 */
const rebuildLoop = (statement: Statement, context: UnminifyContext): Statement[] | undefined => {
    if (!LOOPS.has(statement.type)) return undefined;
    const loop = statement as Statement & { body: Statement };
    if (loop.body.type !== "BlockStatement") return undefined;
    const body = withoutTailContinue(loop.body.body, context);
    if (statement.type !== "WhileStatement" || statement.test.type !== "Literal" || statement.test.value !== true) {
        loop.body.body = body;
        return undefined;
    }
    const [first, ...rest] = body;
    if (first?.type === "IfStatement" && first.alternate === null && statementsOf(first.consequent).length === 1) {
        const only = statementsOf(first.consequent)[0];
        if (only?.type === "BreakStatement" && only.label === null) {
            context.did("loops", statement);
            return [at<Statement>({ type: "WhileStatement", test: not(first.test, first.test), body: block(rest, loop.body) }, statement)];
        }
    }
    const [, jump] = body;
    if (body.length === 2 && first?.type === "IfStatement" && first.alternate === null && isJump(jump) && !(jump?.type === "ContinueStatement" && jump.label === null)) {
        const leaves = jump?.type === "BreakStatement" && jump.label === null;
        const t = statementsOf(first.consequent);
        const placed = leaves || !t.some(breaksOut) ? thenBreak(t, jump as Statement) : undefined;
        if (placed !== undefined) {
            context.did("loops", statement);
            const rebuilt = at<Statement>({ type: "WhileStatement", test: first.test, body: block(withoutTailContinue(placed, context), first.consequent) }, statement);
            return leaves ? [rebuilt] : [rebuilt, jump as Statement];
        }
    }
    loop.body.body = body;
    return undefined;
};

const assignmentOf = (statement: Statement | undefined): (AssignmentExpression & { left: Node & { type: "Identifier" } }) | undefined => {
    const e = statement?.type === "ExpressionStatement" ? statement.expression : undefined;
    return e?.type === "AssignmentExpression" && e.operator === "=" && e.left.type === "Identifier" ? (e as AssignmentExpression & { left: Node & { type: "Identifier" } }) : undefined;
};

/**
 * `a = x; b = a;` -> `b = x;` when nothing else uses `a`: a function's (or module's) `var` whose only references are
 * these two (so no initializer, which writes it too, no closure, no `arguments` alias as a parameter would have, no
 * other script sees it). `b`, a declared name, is resolved before `x` runs instead of after, which only a `with` or a
 * direct `eval` could make differ (an undeclared one could be made by `x`: strict assignments to it then throw only
 * when resolved before). Names under a `with` or a direct `eval` don't resolve in the scope analysis, so neither is
 * found there. `a`'s declarators go after the walk (`unusedDeclarators`).
 */
const mergeCopies = (list: Statement[], context: UnminifyContext): boolean => {
    const { scopes } = context;
    let merged = false;
    for (let i = 0; i + 1 < list.length; i++) {
        const first = assignmentOf(list[i]);
        const second = assignmentOf(list[i + 1]);
        if (first === undefined || second === undefined || second.right.type !== "Identifier") continue;
        const temp = scopes.variableOf(first.left);
        if (temp === undefined || scopes.variableOf(second.right) !== temp || scopes.variableOf(second.left) === undefined) continue;
        const references = temp.references.filter((reference) => !context.removedReferences.has(reference.identifier as unknown as Node));
        if (!temp.defs.every((def) => (def.parent as { kind?: string } | null)?.kind === "var") || temp.scope.type === "global" || references.length !== 2) continue;
        context.did("copies", list[i] as Statement);
        first.left = second.left;
        list.splice(i + 1, 1);
        for (const def of temp.defs) context.unusedDeclarators.add(def.node as unknown as Node);
        merged = true;
        i--;
    }
    return merged;
};

export const removeDeclarators = (program: Node, unused: ReadonlySet<Node>): void => {
    traverse(program, {
        VariableDeclaration(path) {
            const node = path.node;
            const kept = node.declarations.filter((declarator) => !unused.has(declarator));
            if (kept.length === node.declarations.length) return;
            if (kept.length > 0) node.declarations = kept;
            else if (path.isInStatementList()) path.remove();
        },
    });
};

const freshObject = (statement: Statement): { id: Node & { type: "Identifier"; name: string }; literal: ObjectExpression } | undefined => {
    if (statement.type === "VariableDeclaration" && statement.declarations.length === 1 && statement.kind !== "using" && statement.kind !== "await using") {
        const [declarator] = statement.declarations;
        if (declarator?.id.type === "Identifier" && declarator.init !== null && isPlainLiteral(declarator.init)) return { id: declarator.id, literal: declarator.init };
    }
    const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
    if (e?.type === "AssignmentExpression" && e.operator === "=" && e.left.type === "Identifier" && isPlainLiteral(e.right)) return { id: e.left, literal: e.right };
    return undefined;
};

/**
 * `var o = {}; o.a = x; o["b"] = y; o.a.c = z;` -> `var o = { a: x, b: y };` (also after `o = {...};`, and into a
 * literal a property holds: see `plannedStore`). The values run in the same order, and setting a property of a fresh
 * plain object creates it as the literal does (model 7; never `__proto__`). What differs is what `o` holds while the
 * values run (the bare object, or its old value), so nothing may read `o` then: the values don't name it, no `with`
 * or direct `eval` can, and every other reference to it is in the same function (which runs these statements in
 * their order, not during them) or in a function created after them in this list (not a declaration: those exist
 * from the start).
 */
const mergeObjectAssignments = (list: Statement[], context: UnminifyContext): void => {
    if (context.hasWith || context.hasEval) return;
    let created: Map<Node, Statement> | undefined;
    let positions: Map<Statement, number> | undefined;
    const createdAt = (identifier: Node): number => {
        if (created === undefined) {
            const found = new Map<Node, Statement>();
            for (const statement of list) {
                traverse(statement, {
                    enter(path) {
                        if (path.node.type === "FunctionDeclaration") path.skip();
                        else if (isFunctionNode(path.node)) {
                            traverse(path.node, { Identifier: (inner) => void found.set(inner.node, statement) });
                            path.skip();
                        }
                    },
                });
            }
            created = found;
        }
        positions ??= new Map(list.map((statement, index) => [statement, index]));
        const statement = created.get(identifier);
        return statement === undefined ? -1 : (positions.get(statement) ?? -1);
    };
    for (let i = 0; i < list.length; i++) {
        const fresh = freshObject(list[i] as Statement);
        if (fresh === undefined) continue;
        const planned: PlannedStore[] = [];
        const holder = builderHolder(fresh.id, context.scopes);
        for (let j = i + 1; j < list.length; j++) {
            const store = plannedStore(list[j] as Statement, holder, "none", fresh.literal, planned);
            if (store === undefined) break;
            planned.push(store);
        }
        if (planned.length === 0 || !unobservedDuring(i + planned.length, fresh.id, context, createdAt)) continue;
        context.did("objectAssignments", list[i] as Statement);
        for (const { into, property } of planned) into.properties.push(property as ObjectExpression["properties"][number]);
        // The stores' references to `o` go with them (`o.a = x`, `o.a.c = z`: the root of the assignment's target).
        for (const statement of list.splice(i + 1, planned.length)) {
            let target: Node | undefined = statement.type === "ExpressionStatement" && statement.expression.type === "AssignmentExpression" ? statement.expression.left : undefined;
            while (target?.type === "MemberExpression") target = target.object;
            if (target !== undefined) context.removedReferences.add(target);
        }
        positions = undefined;
    }
};

/**
 * Whether no code but the run of statements ending at index `last` of its list (and code that runs in order with
 * them) can read `id`'s binding while they run: every reference is in the same function, or in a function created
 * by a statement after the run (`createdAt`: the index of the statement that creates it).
 */
const unobservedDuring = (last: number, id: Node, context: UnminifyContext, createdAt: (identifier: Node) => number): boolean => {
    const variable = context.scopes.variableOf(id);
    const own = context.scopes.referenceOf(id)?.from.variableScope ?? variable?.scope.variableScope ?? null;
    if (variable === undefined || own === null) return false;
    return variable.references.every((reference) => reference.from.variableScope === own || createdAt(reference.identifier as unknown as Node) > last);
};

const BODY_SLOTS: Readonly<Record<string, readonly string[]>> = {
    IfStatement: ["consequent", "alternate"],
    ForStatement: ["body"],
    ForInStatement: ["body"],
    ForOfStatement: ["body"],
    WhileStatement: ["body"],
    DoWhileStatement: ["body"],
    WithStatement: ["body"],
};

const blockBodies = (node: Node, context: UnminifyContext): void => {
    const slots = BODY_SLOTS[node.type];
    if (slots === undefined) return;
    const fields = node as unknown as Record<string, Statement | null>;
    for (const slot of slots) {
        const body = fields[slot];
        if (body === null || body === undefined || body.type === "BlockStatement" || (slot === "alternate" && body.type === "IfStatement")) continue;
        context.did("blockStatements", body);
        fields[slot] = block(body.type === "EmptyStatement" ? [] : [body], body);
    }
};

/** The unary operators whose result alone, as a statement, does nothing: `void x;`, `!x;`, `typeof x;` are `x;`. */
const DISCARDABLE_UNARY: ReadonlySet<string> = new Set(["void", "!", "typeof"]);

/**
 * `function () { return (() => { B })(); }` -> `function () { B }`: the arrow runs right away, with the function's
 * own `this`, `arguments` and `new.target`, and its returns (or its end) are the function's. Only when neither has
 * parameters (a `var` of the arrow may share a parameter's name), the function is a plain one, and the arrow has no
 * directives (`"use strict"` would change the function) and no `arguments` of its own.
 */
const inlineNestedIife = (node: Node, context: UnminifyContext): void => {
    if ((node.type !== "FunctionExpression" && node.type !== "FunctionDeclaration") || node.body === null || node.params.length > 0 || node.async || node.generator) return;
    const [only] = node.body.body;
    if (node.body.body.length !== 1 || only?.type !== "ReturnStatement") return;
    const call = only.argument;
    if (call?.type !== "CallExpression" || call.arguments.length > 0 || call.optional) return;
    const arrow = call.callee;
    if (arrow.type !== "ArrowFunctionExpression" || arrow.async || arrow.params.length > 0 || arrow.body.type !== "BlockStatement") return;
    if (arrow.body.body.some((statement) => statement.type === "ExpressionStatement" && "directive" in statement && typeof statement.directive === "string")) return;
    if (context.scopes.scopeOf(arrow)?.set.has("arguments") !== false) return;
    context.did("nestedIife", node);
    node.body.body = arrow.body.body;
};

/** One step; the caller repeats on the result. `null` when the statement was removed. Bodies are put in blocks in place. */
export const rewriteStatement = (path: Path, context: UnminifyContext): Node | null | undefined => {
    const node = path.node;
    switch (node.type) {
        case "ExpressionStatement": {
            const expression = node.expression;
            if (expression.type === "UnaryExpression" && DISCARDABLE_UNARY.has(expression.operator)) {
                const argument = expression.argument;
                // `typeof x` doesn't throw for an undeclared global `x`; `x` does.
                if (expression.operator === "typeof" && argument.type === "Identifier" && context.scopes.variableOf(argument) === undefined) {
                    context.refused("keeps `typeof` of a name that may be undeclared", node);
                    return undefined;
                }
                context.did("unaryStatements", node);
                // What's left of `void 0;` does nothing at all.
                if (argument.type === "Literal" && path.isInStatementList()) {
                    path.remove();
                    return null;
                }
                return at<Statement>({ type: "ExpressionStatement", expression: argument }, node);
            }
            if (expression.type === "LogicalExpression") {
                if (expression.operator === "??") {
                    context.refused("keeps `a ?? b;`: no plain `if` for it", node);
                    return undefined;
                }
                context.did("logicalToIf", node);
                const test = expression.operator === "&&" ? expression.left : not(expression.left, expression.left);
                return at<Statement>({ type: "IfStatement", test, consequent: block([expressionStatement(expression.right)], expression.right), alternate: null }, node);
            }
            if (expression.type === "ConditionalExpression") {
                context.did("ternaryToIf", node);
                return at<Statement>(
                    {
                        type: "IfStatement",
                        test: expression.test,
                        consequent: block([expressionStatement(expression.consequent)], expression.consequent),
                        alternate: block([expressionStatement(expression.alternate)], expression.alternate),
                    },
                    node
                );
            }
            return undefined;
        }
        case "IfStatement": {
            // `if (c) {} else { b }` -> `if (!c) { b }`: c runs either way and b exactly when c is falsy.
            const empty = node.consequent.type === "EmptyStatement" || (node.consequent.type === "BlockStatement" && node.consequent.body.length === 0);
            if (!empty || node.alternate === null) break;
            context.did("emptyBranches", node);
            return at<Statement>({ type: "IfStatement", test: not(node.test, node.test), consequent: node.alternate, alternate: null }, node);
        }
        case "ReturnStatement": {
            const argument = node.argument;
            if (argument?.type !== "ConditionalExpression") return undefined;
            context.did("ternaryToIf", node);
            return at<Statement>({ type: "IfStatement", test: argument.test, consequent: returning(argument.consequent), alternate: returning(argument.alternate) }, node);
        }
        case "ForStatement":
            if (node.init !== null || node.update !== null) break;
            context.did("forToWhile", node);
            return at<Statement>({ type: "WhileStatement", test: node.test ?? at<Expression>({ type: "Literal", value: true, raw: "true" }, node), body: node.body }, node);
        case "FunctionExpression":
        case "FunctionDeclaration":
            inlineNestedIife(node, context);
            return undefined;
        case "ArrowFunctionExpression": {
            const body = node.body;
            if (body.type !== "SequenceExpression") return undefined;
            context.did("blockStatements", body);
            const last = body.expressions.at(-1) as Expression;
            const statements = [...body.expressions.slice(0, -1).map(expressionStatement), at<Statement>({ type: "ReturnStatement", argument: last }, last)];
            node.body = block(statements, body) as typeof node.body;
            node.expression = false;
            return undefined;
        }
        default:
            break;
    }
    blockBodies(node, context);
    return undefined;
};

/** `else { if (b) {} }` -> `else if (b) {}`, once the `else` block is final (on exit). */
export const mergeElseIf = (node: Node, context: UnminifyContext): void => {
    if (node.type !== "IfStatement") return;
    const alternate = node.alternate;
    if (alternate?.type !== "BlockStatement" || alternate.body.length !== 1 || alternate.body[0]?.type !== "IfStatement") return;
    context.did("mergeElseIf", alternate);
    node.alternate = alternate.body[0];
};
