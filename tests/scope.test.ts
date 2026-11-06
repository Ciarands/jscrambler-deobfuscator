import { describe, expect, it } from "vitest";
import type { Expression, ExpressionStatement, Node, Program } from "../src/core/ast.js";
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

const statements = (program: Program) => program.body.map((statement) => statement as ExpressionStatement);

describe("scope analysis: parents", () => {
    it("knows each node's parent as of its last refresh, and none for what left the program", () => {
        const program = parse("a + b; c;");
        const scopes = new ScopeInfo(program);
        const [first, second] = statements(program);
        expect(scopes.parentOf(first!.expression)).toBe(first);
        expect(scopes.parentOf(first!)).toBe(program);
        const moved = second!.expression;
        first!.expression = moved;
        program.body.pop();
        scopes.refresh(program);
        expect(scopes.parentOf(moved)).toBe(first);
        expect(scopes.parentOf(second!)).toBeUndefined();
    });

    it("gives a spread copy of a node no parent: the copy may sit anywhere", () => {
        const program = parse("a + b;");
        const scopes = new ScopeInfo(program);
        const [statement] = statements(program);
        expect(scopes.parentOf(statement!.expression)).toBe(statement);
        expect(scopes.parentOf({ ...statement!.expression } as Expression)).toBeUndefined();
    });

    it("forgets the parents of removed subtrees without a refresh", () => {
        const program = parse("f(a); g(b);");
        const scopes = new ScopeInfo(program);
        const [first, second] = statements(program);
        expect(scopes.parentOf(second!.expression)).toBe(second);
        program.body.pop();
        scopes.forget([second!]);
        expect(scopes.parentOf(second!)).toBeUndefined();
        expect(scopes.parentOf(second!.expression)).toBeUndefined();
        expect(scopes.parentOf(first!.expression)).toBe(first);
    });
});
