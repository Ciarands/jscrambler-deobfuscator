import type { MemberExpression, Node } from "oxc-parser";

export type * from "oxc-parser";

export const isFunctionNode = (node: Node | null | undefined): boolean => node?.type === "FunctionExpression" || node?.type === "FunctionDeclaration" || node?.type === "ArrowFunctionExpression";

/** A statement that never completes normally: `return`, `throw`, `break`, `continue`. */
export const isJump = (node: Node | null | undefined): boolean =>
    node?.type === "ReturnStatement" || node?.type === "ThrowStatement" || node?.type === "BreakStatement" || node?.type === "ContinueStatement";

const LOOP_TYPES: ReadonlySet<string> = new Set(["ForStatement", "ForInStatement", "ForOfStatement", "WhileStatement", "DoWhileStatement"]);

/** A loop: what an unlabelled `continue` (and `break`) binds to. */
export const isLoopNode = (node: Node | null | undefined): boolean => node !== null && node !== undefined && LOOP_TYPES.has(node.type);

/** What an unlabelled `break` binds to: a loop or a `switch`. */
export const isBreakTarget = (node: Node | null | undefined): boolean => isLoopNode(node) || node?.type === "SwitchStatement";

/**
 * The property key of a member expression when it is static: `a.b` and `a["b"]` give `"b"`, `a[3]` gives `3`.
 * Returns `undefined` for computed keys that aren't literals.
 */
export const memberKey = (node: MemberExpression): string | number | undefined => {
    if (!("property" in node)) return undefined;
    if (!node.computed) return node.property.name;
    const property = node.property;
    if (property.type === "Literal" && (typeof property.value === "string" || typeof property.value === "number")) return property.value;
    return undefined;
};

/**
 * The property key of a member expression when it is static, as JS sees it (`ToPropertyKey`): `a.b`, `a["b"]` give
 * `"b"`; `a[3]`, `a["3"]` give `"3"`. `undefined` for computed keys that aren't literals and for private names.
 */
export const propertyKey = (node: MemberExpression): string | undefined => {
    if (!("property" in node)) return undefined;
    const property = node.property;
    if (!node.computed) return property.type === "Identifier" ? property.name : undefined;
    if (property.type !== "Literal") return undefined;
    if (typeof property.value === "string") return property.value;
    if (typeof property.value === "number") return String(property.value);
    return undefined;
};

/** A static member chain `R.a[1].b` as its innermost object `R` and its keys (`["a", "1", "b"]`), outermost last. */
export const memberPath = (node: Node): { root: Node; keys: string[] } | undefined => {
    const keys: string[] = [];
    let current = node;
    while (current.type === "MemberExpression") {
        const key = propertyKey(current);
        if (key === undefined) return undefined;
        keys.push(key);
        current = current.object;
    }
    return keys.length === 0 ? undefined : { root: current, keys: keys.toReversed() };
};

/** An ECMAScript IdentifierName (reserved words included: they're valid after a dot). */
export const isIdentifierName = (name: string): boolean => /^[\p{ID_Start}$_][\p{ID_Continue}$\u200C\u200D]*$/u.test(name);

/** A canonical array index or integer key (`"0"`, `"593908"`), printable as a numeric literal. */
export const isIndexKey = (key: string): boolean => {
    const n = Number(key);
    return key !== "" && Number.isSafeInteger(n) && n >= 0 && String(n) === key;
};
