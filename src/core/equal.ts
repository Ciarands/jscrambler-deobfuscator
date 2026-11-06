import { memberKey } from "./ast.js";
import type { Node } from "./ast.js";

/** Same identifier or same static member chain. Only meaningful within one scope. */
export const sameReference = (a: Node, b: Node): boolean => {
    if (a.type === "Identifier" && b.type === "Identifier") return a.name === b.name;
    if (a.type === "MemberExpression" && b.type === "MemberExpression") {
        const keyA = memberKey(a);
        return keyA !== undefined && keyA === memberKey(b) && sameReference(a.object, b.object);
    }
    return false;
};
