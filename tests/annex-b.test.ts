import { describe, expect, it } from "vitest";
import type { Node, Program } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { ScopeInfo } from "../src/core/scope.js";
import { traverse } from "../src/core/traverse.js";
import { deobfuscate } from "../src/index.js";
import { observe } from "./helpers.js";

/** The program, its analysis, and its identifiers named `name` in source order. */
const analyzed = (code: string, name: string): { program: Program; scopes: ScopeInfo; ids: Node[] } => {
    const program = parse(code);
    const ids: Node[] = [];
    traverse(program, {
        Identifier(path) {
            if (path.node.name === name) ids.push(path.node);
        },
    });
    return { program, scopes: new ScopeInfo(program), ids };
};

const uses = (scopes: ScopeInfo, declaration: Node): Node[] => {
    const variable = scopes.variableOf(declaration);
    if (variable === undefined) throw new Error("no variable");
    return scopes.staticReferences(variable).map((reference) => reference.identifier as unknown as Node);
};

/** `annexBEscapes` of the first function declaration of `f` in `code`. */
const escapes = (code: string): boolean => {
    const { scopes, ids } = analyzed(code, "f");
    const declaration = ids.find((id) => scopes.variableOf(id)?.defs.some((def) => def.type === "FunctionName"));
    return scopes.annexBEscapes(scopes.variableOf(declaration!)!);
};

const sameBehaviour = async (input: string, passes: string[]): Promise<string> => {
    const { code } = await deobfuscate(input, { passes: passes as never });
    expect(observe(code)).toBe(observe(input));
    return code;
};

describe("scope analysis: Annex B", () => {
    it("resolves no reference to a sloppy block function's function-wide name to the outer variable", () => {
        // f: the outer declaration, the use in h, the block function, the top-level use.
        const { scopes, ids } = analyzed("var f = 1; function g() { function h() { return f; } h(); { function f() {} } } f;", "f");
        const [outer, inner, block, top] = ids as [Node, Node, Node, Node];
        expect(scopes.variableOf(inner)).toBeUndefined();
        expect(scopes.staticVariableOf(inner)).toBeUndefined();
        expect(scopes.isGlobalReference(inner)).toBe(false);
        expect(scopes.namesGlobal(inner)).toBe(false);
        expect(scopes.nameBoundAt(inner, "f")).toBe(true);
        expect(scopes.declaresName("f")).toBe(true);
        expect(uses(scopes, outer)).toEqual([outer, top]);
        expect(scopes.references(scopes.variableOf(outer)!)?.length).toBe(2);
        expect(scopes.variableOf(top)).toBe(scopes.variableOf(outer));
        expect(scopes.variableOf(block)).not.toBe(scopes.variableOf(outer));
    });

    it("counts no reference to a top-level block function's name as global", () => {
        const { scopes, ids } = analyzed("{ function Math() {} } function g() { return Math.max; }", "Math");
        expect(scopes.isGlobalReference(ids[1]!)).toBe(false);
        expect(scopes.globalReferences("Math")).toEqual([]);
    });

    it("adds a block function's write to its function's variable of the name, until the function is removed", () => {
        const { program, scopes, ids } = analyzed("function g() { var f = 1; { function f() {} } return f; }", "f");
        const [declared, block, read] = ids as [Node, Node, Node];
        expect(uses(scopes, declared)).toEqual([declared, read, block]);
        expect(scopes.staticReferences(scopes.variableOf(declared)!).filter((reference) => reference.isWrite())).toHaveLength(2);
        scopes.refresh(program);
        expect(uses(scopes, declared)).toEqual([declared, read, block]);
        const body = (program.body[0] as Node & { type: "FunctionDeclaration" }).body!.body;
        const [removed] = body.splice(1, 1);
        scopes.forget([removed!]);
        expect(uses(scopes, declared)).toEqual([declared, read]);
    });

    it("makes references to an `if` clause's function unknown: it binds in a block of its own", () => {
        const { scopes, ids } = analyzed("function g() { if (x) function f() {} return f; } function k() { { f; if (x) function f() {} } }", "f");
        expect(scopes.variableOf(ids[1]!)).toBeUndefined();
        expect(scopes.variableOf(ids[2]!)).toBeUndefined();
        expect(scopes.isGlobalReference(ids[2]!)).toBe(false);
    });

    it("leaves strict code, clashing names and parameter defaults to eslint-scope's resolution", () => {
        const programs = [
            '"use strict"; var f = 1; function g() { function h() { return f; } { function f() {} } }',
            "var f = 1; function g() { function h() { return f; } { let f; { function f() {} } } }",
            "var f = 1; function g(a = f) { { function f() {} } }",
        ];
        for (const code of programs) {
            const { scopes, ids } = analyzed(code, "f");
            expect(scopes.variableOf(ids[1]!)).toBe(scopes.variableOf(ids[0]!));
        }
        const { scopes, ids } = analyzed("function g(f) { { function f() {} } return f; }", "f");
        expect(scopes.variableOf(ids[2]!)).toBe(scopes.variableOf(ids[0]!));
        expect(uses(scopes, ids[0]!)).toEqual([ids[2]]);
    });

    it("tells when a block function is reachable through its function-wide binding", () => {
        expect(escapes("function g() { { function f() {} } return f; }")).toBe(true);
        expect(escapes("function g() { var h = () => f; { function f() {} } return h; }")).toBe(true);
        expect(escapes("function g() { var f; { function f() {} } return f; }")).toBe(true);
        expect(escapes("{ function f() {} }")).toBe(true);
        expect(escapes("function g() { if (x) function f() {} }")).toBe(true);
        expect(escapes("function g() { { function f() {} f(); } }")).toBe(false);
        expect(escapes("function g() { var f; { function f() {} } f = 1; }")).toBe(false);
        expect(escapes('function g() { "use strict"; { function f() {} } return f; }')).toBe(false);
        expect(escapes("function g() { { let f; { function f() {} } } return f; }")).toBe(false);
        expect(escapes("function g() { function f() {} return f; }")).toBe(false);
    });

    it("lets a block function inside another of its name write the function-wide binding too, without a binding of its own", () => {
        const { program, scopes, ids } = analyzed("function g() { var r = []; { function f() {} { function f() {} } } return f; }", "f");
        const [outer, inner] = ids as [Node, Node];
        expect(scopes.annexBEscapes(scopes.variableOf(inner)!)).toBe(true);
        const declarations: Node[] = [];
        traverse(program, { FunctionDeclaration: (path) => void declarations.push(path.node) });
        const [, outerDeclaration, innerDeclaration] = declarations as [Node, Node & { type: "FunctionDeclaration" }, Node & { type: "FunctionDeclaration" }];
        expect(outerDeclaration.id).toBe(outer);
        expect(scopes.annexBName(outerDeclaration)).toBe("f");
        // Engines differ (V8 binds it; the spec's `var f` would clash with the outer block's `f`), but the outer one binds the name either way.
        expect(scopes.annexBName(innerDeclaration)).toBeUndefined();
    });

    it("takes a labelled block's function for a block function, and a labelled function in a block for an `if` clause's", () => {
        expect(escapes("function g() { l: { function f() {} f(); } }")).toBe(false);
        expect(escapes("function g() { { l: function f() {} f(); } }")).toBe(true);
        expect(escapes("function g() { l: function f() {} return f; }")).toBe(false);
    });
});

describe("Annex B through the passes", () => {
    it("doesn't fold a use of a block function's function-wide name to the outer variable's value", async () => {
        const code = await sameBehaviour('var f = "global";\nfunction g() { function h() { return f; } return h(); { function f() {} } }\nresult = g();\n', ["simplify"]);
        expect(code).toContain("return f;");
        await sameBehaviour('var f = "o";\nfunction g() { var r = typeof f; { function f() {} } return r; }\nresult = g();\n', ["cleanup", "simplify"]);
    });

    it("sees a block function write its function's variable of the name", async () => {
        await sameBehaviour("function g() { var f = 1; { function f() {} } return typeof f; }\nresult = g();\n", ["simplify"]);
        await sameBehaviour("var f = 1;\n{ function f() {} }\nresult = typeof f;\n", ["simplify"]);
    });

    it("doesn't take an `if` clause's function for a hoisted one", async () => {
        await sameBehaviour("function g() { if (false) function f() { return 1; } try { return f(); } catch (e) { return e.name; } }\nresult = g();\n", ["simplify", "pure-calls"]);
    });

    it("doesn't take a block function to run only after what its block's references follow", async () => {
        // `f()` before `k` is set calls it through the function-wide binding Annex B gives it.
        await sameBehaviour('{ function f() { return k; } }\nvar early = f();\nvar k = "set";\nresult = [early, f()];\n', ["simplify"]);
        await sameBehaviour('function g() { { function f() { return k; } } var early = f(); var k = "set"; return [early, f()]; }\nresult = g();\n', ["simplify"]);
    });

    it("still folds the outer variable in strict code and where a lexical name keeps Annex B away", async () => {
        const strict = await sameBehaviour('var f = "global";\nfunction g() { "use strict"; function h() { return f; } return h(); { function f() {} } }\nresult = g();\n', ["simplify"]);
        expect(strict).toContain('return "global";');
        const clash = await sameBehaviour('var f = "global";\nfunction g() { function h() { return f; } var r = h(); { let f; { function f() {} } } return r; }\nresult = g();\n', ["simplify"]);
        expect(clash).toContain('return "global";');
    });

    it("sees a block function inside another of its name write the function-wide binding", async () => {
        const program =
            'function g() {\n  { function f() { return 1; } { function f() { return table[0]; } } }\n  var run = f;\n  try { result = run(); } catch (e) { result = "threw:" + e.name; }\n  var table = ["a"];\n}\ng();\n';
        await sameBehaviour(program, ["simplify"]);
        await sameBehaviour(program, ["unminify", "simplify", "cleanup"]);
        // The outer block function keeps the function-wide name: no `var f` (which would clash with it) for the dead inner one.
        await sameBehaviour("function g() { var r = []; { function f() { return 1; } if (0) function f() { return 2; } r.push(f()); } return [r, f()]; }\nresult = g();\n", ["simplify"]);
        await sameBehaviour("function g() { var r = []; { function f() { return 1; } if (0) { function f() { return 2; } } r.push(f()); } return [r, f()]; }\nresult = g();\n", ["simplify"]);
    });
});
