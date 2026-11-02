import type { Argument, CallExpression, Expression, MemberExpression, Node } from "./ast.js";
import { isIdentifierName, isIndexKey } from "./ast.js";

export type At = Node | readonly [number, number];

interface Position {
    start: number;
    end: number;
    range: [number, number];
}

/** Every created node needs `range`: scope analysis crashes without it, and logs use it to point into the source. */
const positionOf = (at: At): Position => {
    if ("type" in at) {
        const range = at.range ?? [at.start, at.end];
        return { start: range[0], end: range[1], range: [range[0], range[1]] };
    }
    return { start: at[0], end: at[1], range: [at[0], at[1]] };
};

export const at = <N extends Node>(node: { type: N["type"] } & Record<string, unknown>, position: At): N => ({ ...node, ...positionOf(position) }) as unknown as N;

export const identifier = (name: string, position: At): Expression => ({ type: "Identifier", name, ...positionOf(position) });

export const callOf = (callee: Expression, args: readonly Argument[], position: At): CallExpression =>
    at<CallExpression>({ type: "CallExpression", callee, arguments: [...args], optional: false }, position);

export type Primitive = string | number | boolean | null | undefined;

/** What the program declares: `undefined`, `NaN` and `Infinity` are written as names only where none is declared. */
export interface DeclaredNames {
    declaresName(name: string): boolean;
}

/**
 * `undefined`, `NaN` and `Infinity` are written as their global names only when `names` says the program declares no
 * binding of that name; otherwise as `void 0`, `0 / 0` and `1e999` (literals), which no binding can change.
 */
export const valueToNode = (value: Primitive, position: At, names?: DeclaredNames): Expression => {
    const pos = positionOf(position);
    const free = (name: string): boolean => names !== undefined && !names.declaresName(name);
    if (value === undefined) {
        if (free("undefined")) return { type: "Identifier", name: "undefined", ...pos };
        return { type: "UnaryExpression", operator: "void", prefix: true, argument: { type: "Literal", value: 0, raw: null, ...pos }, ...pos } as Expression;
    }
    if (typeof value === "number") {
        if (Number.isNaN(value)) return free("NaN") ? { type: "Identifier", name: "NaN", ...pos } : ({ type: "Literal", value, raw: null, ...pos } as Expression);
        if (value === Infinity) return free("Infinity") ? { type: "Identifier", name: "Infinity", ...pos } : ({ type: "Literal", value, raw: null, ...pos } as Expression);
        if (value < 0 || Object.is(value, -0)) {
            return { type: "UnaryExpression", operator: "-", prefix: true, argument: valueToNode(-value, position, names), ...pos } as Expression;
        }
        return { type: "Literal", value, raw: null, ...pos } as Expression;
    }
    if (value === null) return { type: "Literal", value: null, raw: "null", ...pos } as Expression;
    // The type says primitive; a value that got here untyped (a prototype lookup, an interpreter object) would print as `null`.
    if (typeof value !== "string" && typeof value !== "boolean") throw new TypeError(`valueToNode: not a primitive (${typeof value})`);
    return { type: "Literal", value, raw: null, ...pos } as Expression;
};

export const member = (object: Expression, key: string, position: At): MemberExpression => {
    const pos = positionOf(position);
    if (isIdentifierName(key)) return { type: "MemberExpression", object, property: { type: "Identifier", name: key, ...pos }, computed: false, optional: false, ...pos } as MemberExpression;
    const property = isIndexKey(key) ? valueToNode(Number(key), position) : valueToNode(key, position);
    return { type: "MemberExpression", object, property, computed: true, optional: false, ...pos } as MemberExpression;
};

export const memberChain = (root: Expression, keys: readonly string[], position: At): Expression => keys.reduce<Expression>((object, key) => member(object, key, position), root);
