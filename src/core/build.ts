import type { Argument, CallExpression, Expression, MemberExpression, Node } from "./ast.js";
import { isIdentifierName, isIndexKey } from "./ast.js";

/** Something with a source position: a node or a raw `[start, end]` range. */
export type At = Node | readonly [number, number];

interface Position {
    start: number;
    end: number;
    range: [number, number];
}

/**
 * Position for a new node, copied from `at`.
 *
 * Every node we create needs `range`: scope analysis crashes without it, and log messages use it to point back
 * into the original source.
 */
const positionOf = (at: At): Position => {
    if ("type" in at) {
        const range = at.range ?? [at.start, at.end];
        return { start: range[0], end: range[1], range: [range[0], range[1]] };
    }
    return { start: at[0], end: at[1], range: [at[0], at[1]] };
};

/** Give a freshly built node the position of `position`. The caller states the node type it built. */
export const at = <N extends Node>(node: { type: N["type"] } & Record<string, unknown>, position: At): N => ({ ...node, ...positionOf(position) }) as unknown as N;

export const identifier = (name: string, position: At): Expression => ({ type: "Identifier", name, ...positionOf(position) });

/** `callee(...args)`. */
export const callOf = (callee: Expression, args: readonly Argument[], position: At): CallExpression =>
    at<CallExpression>({ type: "CallExpression", callee, arguments: [...args], optional: false }, position);

export type Primitive = string | number | boolean | null | undefined;

/** A primitive as an expression. `undefined`, `NaN`, `Infinity` and negative numbers become the expressions that produce them. */
export const valueToNode = (value: Primitive, position: At): Expression => {
    const pos = positionOf(position);
    if (value === undefined) return { type: "Identifier", name: "undefined", ...pos };
    if (typeof value === "number") {
        if (Number.isNaN(value)) return { type: "Identifier", name: "NaN", ...pos };
        if (value === Infinity) return { type: "Identifier", name: "Infinity", ...pos };
        if (value < 0 || Object.is(value, -0)) {
            return { type: "UnaryExpression", operator: "-", prefix: true, argument: valueToNode(-value, position), ...pos } as Expression;
        }
        return { type: "Literal", value, raw: null, ...pos } as Expression;
    }
    if (value === null) return { type: "Literal", value: null, raw: "null", ...pos } as Expression;
    // The type says primitive; a value that got here untyped (a prototype lookup, a guest object) would print as `null`.
    if (typeof value !== "string" && typeof value !== "boolean") throw new TypeError(`valueToNode: not a primitive (${typeof value})`);
    return { type: "Literal", value, raw: null, ...pos } as Expression;
};

/** `object.key`, or `object[3]` / `object["a-b"]` when the key isn't an identifier name. */
export const member = (object: Expression, key: string, position: At): MemberExpression => {
    const pos = positionOf(position);
    if (isIdentifierName(key)) return { type: "MemberExpression", object, property: { type: "Identifier", name: key, ...pos }, computed: false, optional: false, ...pos } as MemberExpression;
    const property = isIndexKey(key) ? valueToNode(Number(key), position) : valueToNode(key, position);
    return { type: "MemberExpression", object, property, computed: true, optional: false, ...pos } as MemberExpression;
};

/** `root.a.b[1]` from a root and its keys. */
export const memberChain = (root: Expression, keys: readonly string[], position: At): Expression => keys.reduce<Expression>((object, key) => member(object, key, position), root);
