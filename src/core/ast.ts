import type { ArrowFunctionExpression, Function as FunctionNode, MemberExpression, Node } from "oxc-parser";

export type * from "oxc-parser";

export type FunctionLike = FunctionNode | ArrowFunctionExpression;

export const isFunctionNode = (node: Node | null | undefined): boolean => node?.type === "FunctionExpression" || node?.type === "FunctionDeclaration" || node?.type === "ArrowFunctionExpression";

export const isJump = (node: Node | null | undefined): boolean =>
    node?.type === "ReturnStatement" || node?.type === "ThrowStatement" || node?.type === "BreakStatement" || node?.type === "ContinueStatement";

const LOOP_TYPES: ReadonlySet<string> = new Set(["ForStatement", "ForInStatement", "ForOfStatement", "WhileStatement", "DoWhileStatement"]);

export const isLoopNode = (node: Node | null | undefined): boolean => node !== null && node !== undefined && LOOP_TYPES.has(node.type);

export const isBreakTarget = (node: Node | null | undefined): boolean => isLoopNode(node) || node?.type === "SwitchStatement";

/** `a.b`/`a["b"]` give `"b"`, `a[3]` gives `3`; `undefined` for non-literal computed keys. */
export const memberKey = (node: MemberExpression): string | number | undefined => {
    if (!("property" in node)) return undefined;
    if (!node.computed) return node.property.name;
    const property = node.property;
    if (property.type === "Literal" && (typeof property.value === "string" || typeof property.value === "number")) return property.value;
    return undefined;
};

/** As `ToPropertyKey`: `a[3]` and `a["3"]` both give `"3"`. `undefined` for non-literal computed keys and private names. */
export const propertyKey = (node: MemberExpression): string | undefined => {
    if (!("property" in node)) return undefined;
    const property = node.property;
    if (!node.computed) return property.type === "Identifier" ? property.name : undefined;
    if (property.type !== "Literal") return undefined;
    if (typeof property.value === "string") return property.value;
    if (typeof property.value === "number") return String(property.value);
    return undefined;
};

/** A non-computed property key's name: `a` and `"a"` give `"a"`, `1` gives `"1"`. */
export const keyName = (key: Node): string | undefined => {
    if (key.type === "Identifier") return key.name;
    if (key.type === "Literal" && (typeof key.value === "string" || typeof key.value === "number")) return String(key.value);
    return undefined;
};

/** `R.a[1].b` gives root `R` and keys `["a", "1", "b"]`. */
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

export const isIdentifierName = (name: string): boolean => /^[\p{ID_Start}$_][\p{ID_Continue}$\u200C\u200D]*$/u.test(name);

const NOT_BINDABLE: ReadonlySet<string> = new Set(
    (
        "break case catch class const continue debugger default delete do else enum export extends false finally for function if import in " +
        "instanceof new null return super switch this throw true try typeof var void while with yield await let static implements interface " +
        "package private protected public arguments eval"
    ).split(" ")
);

/** A name that may stand as an identifier reference anywhere: not a keyword, literal, strict-mode reserved word, `arguments` or `eval`. */
export const isBindingName = (name: string): boolean => isIdentifierName(name) && !NOT_BINDABLE.has(name);

export const isIndexKey = (key: string): boolean => {
    const n = Number(key);
    return key !== "" && Number.isSafeInteger(n) && n >= 0 && String(n) === key;
};
