import type { BlockStatement, Expression, ForStatement, IfStatement, LabeledStatement, Node, ObjectExpression, Statement, VariableDeclaration, VariableDeclarator } from "../../core/ast.js";
import { isFunctionNode } from "../../core/ast.js";
import { at } from "../../core/build.js";
import { forEachChild, traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";
import { not, storedProperty } from "./expressions.js";

const block = (body: Statement[], origin: Node): BlockStatement => at<BlockStatement>({ type: "BlockStatement", body }, origin);
const expressionStatement = (expression: Expression): Statement => at<Statement>({ type: "ExpressionStatement", expression }, expression);
/** `{ return value; }` */
const returning = (value: Expression): BlockStatement => block([at<Statement>({ type: "ReturnStatement", argument: value }, value)], value);
const declaration = (node: VariableDeclaration, declarators: VariableDeclarator[]): VariableDeclaration =>
    at<VariableDeclaration>({ type: "VariableDeclaration", kind: node.kind, declarations: declarators }, declarators[0] ?? node);

/** Whether any identifier under `node` refers to `variable`. */
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

/** `if (c) { ...; break label; }` with no other jump to `label` in it. */
const isBreakingIf = (statement: Statement, label: string): statement is IfStatement & { consequent: BlockStatement } => {
    if (statement.type !== "IfStatement" || statement.alternate !== null || statement.consequent.type !== "BlockStatement") return false;
    const body = statement.consequent.body;
    const last = body.at(-1);
    return last?.type === "BreakStatement" && last.label?.name === label && !body.slice(0, -1).some((s) => jumpsTo(s, label)) && !jumpsTo(statement.test, label);
};

/** Whether a statement declares a block-scoped name (`let`, `const`, `class`, or a function in a block). */
const isLexical = (statement: Statement): boolean =>
    (statement.type === "VariableDeclaration" && statement.kind !== "var") || statement.type === "ClassDeclaration" || statement.type === "FunctionDeclaration";

/**
 * `label: { a; if (c1) { x; break label; } if (c2) { y; break label; } rest }` -> `a; if (c1) { x } else if (c2) { y }
 * else { rest }` (the unflattener's exits): each break skips to the end of the block, which is what
 * the `else` does, and no other jump names the label. Block-scoped declarations keep a block around the result.
 */
const unlabelBlock = (statement: LabeledStatement, context: UnminifyContext): Statement[] | undefined => {
    if (statement.body.type !== "BlockStatement") return undefined;
    const label = statement.label.name;
    const body = statement.body.body as Statement[];
    const first = body.findIndex((s) => isBreakingIf(s, label));
    if (first === -1) {
        if (jumpsTo(statement.body, label)) return undefined;
        context.did("labeledBlocks", statement);
        return body.some(isLexical) ? [statement.body] : body;
    }
    let end = first;
    while (end < body.length && isBreakingIf(body[end] as Statement, label)) end++;
    const leading = body.slice(0, first);
    const tail = body.slice(end);
    if ([...leading, ...tail].some((s) => jumpsTo(s, label))) return undefined;
    let chain: Statement | null = tail.length === 0 ? null : block(tail, tail[0] as Statement);
    for (let i = end - 1; i >= first; i--) {
        const branch = body[i] as IfStatement & { consequent: BlockStatement };
        chain = at<IfStatement>({ type: "IfStatement", test: branch.test, consequent: block(branch.consequent.body.slice(0, -1), branch.consequent), alternate: chain }, branch);
    }
    context.did("labeledBlocks", statement);
    const result = [...leading, chain as Statement];
    return body.some(isLexical) ? [block(result, statement)] : result;
};

/**
 * The statements a listed statement becomes (`undefined`: itself): one declaration per declarator, `return void x`
 * -> `x; return;`, loop-head declarations moved out of the loop, and sequences split (`a(), b();` -> `a(); b();`;
 * `return a(), b` -> `a(); return b;`, also for `throw`, an `if` test, a `switch` discriminant and a lone
 * declarator's initializer: the leading expressions run first either way, and a `let`/`const` name is in its dead
 * zone for them either way).
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
        case "LabeledStatement":
            return unlabelBlock(statement, context);
        default:
            return undefined;
    }
};

/** Expand the statements of a list in place (see `expandStatement`), repeating on what an expansion made. */
export const expandStatements = (list: Statement[], context: UnminifyContext): void => {
    for (let i = 0; i < list.length; i++) {
        const statements = expandStatement(list[i] as Statement, context);
        if (statements === undefined) continue;
        list.splice(i, 1, ...statements);
        i--;
    }
    mergeObjectAssignments(list, context);
};

/** `var o = {};` (one declarator) or `o = {};`: the name and the empty literal. */
const freshObject = (statement: Statement): { id: Node & { type: "Identifier"; name: string }; literal: ObjectExpression } | undefined => {
    if (statement.type === "VariableDeclaration" && statement.declarations.length === 1 && statement.kind !== "using" && statement.kind !== "await using") {
        const [declarator] = statement.declarations;
        if (declarator?.id.type === "Identifier" && declarator.init?.type === "ObjectExpression" && declarator.init.properties.length === 0) return { id: declarator.id, literal: declarator.init };
    }
    const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
    if (e?.type === "AssignmentExpression" && e.operator === "=" && e.left.type === "Identifier" && e.right.type === "ObjectExpression" && e.right.properties.length === 0)
        return { id: e.left, literal: e.right };
    return undefined;
};

/**
 * `var o = {}; o.a = x; o["b"] = y;` -> `var o = { a: x, b: y };` (also after `o = {};`). The values run in the same
 * order, and setting a property of a fresh plain object creates it as the literal does (model 7; never `__proto__`,
 * see `storedProperty`). What differs is what `o` holds while the values run (the bare object, or its old value), so
 * nothing may read `o` then: the values don't name it, no `with` or direct `eval` can, and every other reference to
 * it is in the same function (which runs these statements in their order, not during them) or in a function created
 * after them in this list (not a declaration: those exist from the start).
 */
const mergeObjectAssignments = (list: Statement[], context: UnminifyContext): void => {
    if (context.hasWith || context.hasEval) return;
    /** For identifiers in function expressions (not declarations) of the list: their statement in it. */
    let created: Map<Node, Statement> | undefined;
    /** Each statement's index in the list, rebuilt after a merge moves statements up. */
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
        const properties: Node[] = [];
        for (let j = i + 1; j < list.length; j++) {
            const property = storedProperty(list[j] as Statement, fresh.id.name, false);
            if (property === undefined) break;
            properties.push(property);
        }
        if (properties.length === 0 || !unobservedDuring(i + properties.length, fresh.id, context, createdAt)) continue;
        context.did("objectAssignments", list[i] as Statement);
        fresh.literal.properties.push(...(properties as ObjectExpression["properties"]));
        list.splice(i + 1, properties.length);
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

/** `if (a) b();` -> `if (a) { b(); }`, and loop bodies likewise. An `else if` stays. */
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

/**
 * Rewrite the statement at `path` (one step; the caller repeats on the result). Returns the replacement, `null` when
 * the statement was removed, or `undefined` when nothing applies. Bodies are put in blocks in place.
 */
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
            // `() => (a, b)` -> `() => { a; return b; }`
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
