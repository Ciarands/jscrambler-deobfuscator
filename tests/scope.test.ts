import { describe, expect, it } from "vitest";
import type { Node } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { ScopeInfo } from "../src/core/scope.js";
import { traverse } from "../src/core/traverse.js";

/** How many identifiers named `name` in `code` the scope analysis resolves to a variable of the program. */
const uses = (code: string, name: string): number => {
    const program = parse(code);
    const scopes = new ScopeInfo(program);
    let count = 0;
    traverse(program, {
        Identifier(path) {
            const reference = scopes.referenceOf(path.node as Node);
            if (path.node.name === name && reference?.resolved !== null && reference?.resolved !== undefined) count++;
        },
    });
    return count;
};

describe("scope analysis", () => {
    it("sees references wherever JS puts expressions: accessor properties, static blocks, import options", () => {
        // Each name: its declaration's write, then the use.
        expect(uses("var v = 1; class A { accessor p = v; }", "v")).toBe(2);
        expect(uses("var w = 2; class A { static { w; } }", "w")).toBe(2);
        expect(uses('var y = "json"; import("m", { with: { type: y } });', "y")).toBe(2);
    });
});
