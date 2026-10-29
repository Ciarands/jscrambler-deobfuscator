import type { Expression, Node } from "./ast.js";

export type Value = string | number | boolean | null | undefined;
export type Evaluation = { readonly ok: true; readonly value: Value } | { readonly ok: false };

export const FAIL: Evaluation = { ok: false };
export const value = (v: Value): Evaluation => ({ ok: true, value: v });

export interface EvaluateEnv {
    /**
     * Whether an identifier named `undefined`, `NaN` or `Infinity` really is the global (not shadowed).
     * Without this, those names are not evaluated.
     */
    readonly isGlobal?: (identifier: Node) => boolean;
    /**
     * Value of an expression the evaluator can't see through by itself (variables, `arguments` array slots,
     * string decoder calls...). Return `FAIL` when unknown. Consulted before the built-in rules.
     */
    readonly lookup?: (node: Expression) => Evaluation;
    /**
     * Results per node, for callers that evaluate many overlapping subtrees in one walk (a fold at every node of a
     * chain). Only valid while the nodes aren't changed in place.
     */
    readonly cache?: WeakMap<Node, Evaluation>;
}

const GLOBAL_CONSTANTS = new Map<string, Value>([
    ["undefined", undefined],
    ["NaN", Number.NaN],
    ["Infinity", Number.POSITIVE_INFINITY],
]);

/** JS binary operators on primitives. Values are always primitives here, so these can't run user code. */
const binary = (operator: string, left: Value, right: Value): Evaluation => {
    // Primitives only: the casts below never reach valueOf/toString on an object.
    const l = left as number;
    const r = right as number;
    switch (operator) {
        case "+":
            return value(l + r);
        case "-":
            return value(l - r);
        case "*":
            return value(l * r);
        case "/":
            return value(l / r);
        case "%":
            return value(l % r);
        case "**":
            return value(l ** r);
        case "==":
            return value(l == r);
        case "!=":
            return value(l != r);
        case "===":
            return value(l === r);
        case "!==":
            return value(l !== r);
        case "<":
            return value(l < r);
        case "<=":
            return value(l <= r);
        case ">":
            return value(l > r);
        case ">=":
            return value(l >= r);
        case "<<":
            return value(l << r);
        case ">>":
            return value(l >> r);
        case ">>>":
            return value(l >>> r);
        case "&":
            return value(l & r);
        case "|":
            return value(l | r);
        case "^":
            return value(l ^ r);
        default:
            return FAIL;
    }
};

const typeOf = (v: Value): string => (v === null ? "object" : typeof v);

/**
 * Evaluate an expression to a primitive without running anything. Only side-effect-free expressions over known
 * values evaluate; anything else gives `{ ok: false }`.
 */
export const evaluate = (node: Node, env: EvaluateEnv = {}): Evaluation => {
    const { cache } = env;
    const visit = (n: Node): Evaluation => {
        if (cache === undefined) return compute(n);
        const cached = cache.get(n);
        if (cached !== undefined) return cached;
        const result = compute(n);
        cache.set(n, result);
        return result;
    };
    const compute = (n: Node): Evaluation => {
        if (env.lookup !== undefined && n.type !== "Literal") {
            const found = env.lookup(n as Expression);
            if (found.ok) return found;
        }
        switch (n.type) {
            case "Literal": {
                const v: unknown = n.value;
                if (v === null || typeof v === "string" || typeof v === "number" || typeof v === "boolean") return value(v);
                return FAIL; // regex, bigint
            }
            case "Identifier": {
                if (!GLOBAL_CONSTANTS.has(n.name) || env.isGlobal === undefined || !env.isGlobal(n)) return FAIL;
                return value(GLOBAL_CONSTANTS.get(n.name));
            }
            case "UnaryExpression": {
                if (n.operator === "delete") return FAIL;
                const arg = visit(n.argument);
                if (!arg.ok) return FAIL;
                const v = arg.value as number; // primitive, see `binary`
                switch (n.operator) {
                    case "-":
                        return value(-v);
                    case "+":
                        return value(+v);
                    case "!":
                        return value(!v);
                    case "~":
                        return value(~v);
                    case "typeof":
                        return value(typeOf(arg.value));
                    case "void":
                        return value(undefined);
                }
                return FAIL;
            }
            case "BinaryExpression": {
                if (n.left.type === "PrivateIdentifier") return FAIL;
                const left = visit(n.left);
                if (!left.ok) return FAIL;
                const right = visit(n.right);
                if (!right.ok) return FAIL;
                return binary(n.operator, left.value, right.value);
            }
            case "LogicalExpression": {
                const left = visit(n.left);
                if (!left.ok) return FAIL;
                const shortCircuit = n.operator === "&&" ? !left.value : n.operator === "||" ? Boolean(left.value) : left.value !== null && left.value !== undefined;
                return shortCircuit ? left : visit(n.right);
            }
            case "ConditionalExpression": {
                const test = visit(n.test);
                if (!test.ok) return FAIL;
                return visit(test.value ? n.consequent : n.alternate);
            }
            case "SequenceExpression": {
                let last: Evaluation = FAIL;
                for (const expression of n.expressions) {
                    last = visit(expression);
                    if (!last.ok) return FAIL;
                }
                return last;
            }
            case "TemplateLiteral": {
                // A null cooked value (an invalid escape, only allowed in tagged templates) has no string value.
                if (n.quasis.some((quasi) => quasi.value.cooked === null)) return FAIL;
                let text = n.quasis[0]?.value.cooked ?? "";
                for (const [i, expression] of n.expressions.entries()) {
                    const part = visit(expression);
                    if (!part.ok) return FAIL;
                    text += String(part.value) + (n.quasis[i + 1]?.value.cooked ?? "");
                }
                return value(text);
            }
            case "MemberExpression": {
                if (!("property" in n)) return FAIL;
                const object = visit(n.object);
                if (!object.ok || typeof object.value !== "string") return FAIL;
                const key = n.computed ? visit(n.property) : value(n.property.name);
                if (!key.ok) return FAIL;
                if (key.value === "length") return value(object.value.length);
                if (typeof key.value === "number" && Number.isInteger(key.value) && key.value >= 0) return value(object.value[key.value]);
                return FAIL;
            }
            default:
                return FAIL;
        }
    };
    return visit(node);
};
