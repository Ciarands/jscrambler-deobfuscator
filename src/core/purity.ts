import type { CallExpression, Node } from "./ast.js";
import { propertyKey } from "./ast.js";
import { evaluate } from "./evaluate.js";
import type { ScopeInfo } from "./scope.js";

/** Evaluation can't throw or have effects. The base predicate: `isPureTest` and `isPlainPrimitive` refine it. */
export const isPure = (node: Node | null | undefined, scopes: ScopeInfo): boolean => {
    if (node === null || node === undefined) return true;
    switch (node.type) {
        case "Literal":
        case "FunctionExpression":
        case "ArrowFunctionExpression":
            return true;
        case "Identifier": {
            // Only bindings with no dead zone: an undeclared name, or `let`/`const`/class read early, throws.
            const variable = scopes.variableOf(node) ?? scopes.staticVariableOf(node);
            if (variable === undefined) return false;
            if (variable.name === "arguments" && variable.defs.length === 0) return variable.scope.type === "function";
            return (
                variable.defs.length > 0 &&
                variable.defs.every(
                    (def) =>
                        def.type === "FunctionName" || def.type === "Parameter" || def.type === "CatchClause" || (def.type === "Variable" && (def.parent as { kind?: string } | null)?.kind === "var")
                )
            );
        }
        case "ArrayExpression":
            return node.elements.every((e) => e === null || (e.type !== "SpreadElement" && isPure(e, scopes)));
        case "ObjectExpression":
            return node.properties.every((p) => p.type === "Property" && !p.computed && p.kind === "init" && isPure(p.value, scopes));
        case "CallExpression":
            return isPureBuilderCall(node, scopes);
        default:
            return evaluate(node).ok;
    }
};

/**
 * `(() => { var t; t = {}; t.a = x; return t; })()` (how jscrambler builds object literals): a call with no arguments
 * of a function literal without parameters whose body only declares `var`s, gives one of them a plain literal, sets
 * static keys of it (not `__proto__`) to pure values and returns something pure. It changes nothing but its fresh
 * object (model 7: no setter on Object.prototype but `__proto__`'s) and can't throw: the holder is the body's own
 * `var`, holding the literal by then. (An async or generator body runs at most this, and throws into its result.)
 */
const isPureBuilderCall = (node: CallExpression, scopes: ScopeInfo): boolean => {
    const fn = node.callee;
    if (node.arguments.length > 0 || (fn.type !== "ArrowFunctionExpression" && fn.type !== "FunctionExpression")) return false;
    if (fn.params.length > 0 || fn.body?.type !== "BlockStatement") return false;
    const body = fn.body.body;
    const last = body.at(-1);
    if (last?.type !== "ReturnStatement") return false;
    // Every top-level `var` of the body is its own (hoisted); a `let`/`const` holds nothing a store may use below.
    const own = new Set(
        body.flatMap((statement) => (statement.type === "VariableDeclaration" && statement.kind === "var" ? statement.declarations.map((d) => (d.id.type === "Identifier" ? d.id.name : "")) : []))
    );
    let holder: string | undefined;
    const assigns = (target: Node, value: Node | null): boolean => {
        if (value !== null && !isPure(value, scopes)) return false;
        if (target.type === "Identifier" && own.has(target.name)) {
            // A `__proto__` property sets a prototype, whose setters a later store could run.
            const plain =
                value?.type === "ObjectExpression" &&
                value.properties.every((p) => p.type === "Property" && !(p.key.type === "Identifier" ? p.key.name === "__proto__" : p.key.type === "Literal" && p.key.value === "__proto__"));
            holder = plain ? target.name : holder === target.name ? undefined : holder;
            return true;
        }
        if (target.type !== "MemberExpression" || target.object.type !== "Identifier" || target.object.name !== holder) return false;
        const key = propertyKey(target);
        return key !== undefined && key !== "__proto__";
    };
    for (const statement of body.slice(0, -1)) {
        if (statement.type === "VariableDeclaration") {
            if (!statement.declarations.every((d) => d.id.type === "Identifier" && (d.init === null || assigns(d.id, d.init)))) return false;
            continue;
        }
        const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
        if (e?.type !== "AssignmentExpression" || e.operator !== "=" || !assigns(e.left, e.right)) return false;
    }
    return isPure(last.argument, scopes);
};

/**
 * `isPure` for `if` tests: `===`/`!==`, `!` and `&&`/`||`/`??` (no conversion, no throw) of pure tests; other binary
 * and unary operators refused even where `isPure` would fold them; anything else as `isPure`.
 */
export const isPureTest = (node: Node, scopes: ScopeInfo): boolean => {
    switch (node.type) {
        case "BinaryExpression":
            return (node.operator === "===" || node.operator === "!==") && isPureTest(node.left as Node, scopes) && isPureTest(node.right, scopes);
        case "LogicalExpression":
            return isPureTest(node.left, scopes) && isPureTest(node.right, scopes);
        case "UnaryExpression":
            return node.operator === "!" && isPureTest(node.argument, scopes);
        default:
            return isPure(node, scopes);
    }
};

/**
 * A primitive literal, possibly negated, but not a regex or a BigInt: `isPure`, and also an update with it (`x += v`,
 * `x++` of a variable holding it) can't throw (`1n + 1` does) or run code.
 */
export const isPlainPrimitive = (node: Node | null): boolean => {
    const literal = node?.type === "UnaryExpression" && node.operator === "-" ? node.argument : node;
    return literal?.type === "Literal" && !(literal.value instanceof RegExp) && typeof literal.value !== "bigint" && !("bigint" in literal && literal.bigint !== undefined && literal.bigint !== null);
};
