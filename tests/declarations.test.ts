import { describe, expect, it } from "vitest";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const RUN: Run = { trace: true, timeout: 1000 };

/** Unminifies `input`, checks the output does what the input does under `run`, and lists its declarations. */
const declarations = async (input: string, run: Run = RUN): Promise<string[]> => {
    const output = (await deobfuscate(input, { passes: ["unminify"] })).code;
    const expected = observe(input, run);
    expect(expected).not.toContain("threw SyntaxError");
    expect(observe(output, run)).toBe(expected);
    const found: string[] = [];
    traverse(parse(output), {
        VariableDeclaration(path) {
            const names = path.node.declarations.map((declarator) => `${declarator.id.type === "Identifier" ? declarator.id.name : "?"}${declarator.init === null ? "" : " ="}`);
            found.push(`${path.node.kind} ${names.join(", ")}`);
        },
    });
    return found;
};

describe("hoisted declarations", () => {
    it("moves a var to its first assignment: const for one write, let for more, joining the names left at the top", async () => {
        const found = await declarations(`
            function f(c) {
                var a, b, d, e;
                a = t(1);
                b = t(a + 1);
                b++;
                if (c) { d = t(2); e = 1; } else { d = t(3); e = 2; }
                return [a, b, d, e];
            }
            result = [f(true), f(false)];
        `);
        expect(found).toEqual(["var d, e", "const a =", "let b ="]);
    });

    it("keeps a var where it is when the first use reads it", async () => {
        const found = await declarations("function f() { var x; t(x); x = t(1); return x; } result = f();");
        expect(found).toEqual(["var x"]);
    });

    it("keeps a var at the top when its uses are in separate blocks", async () => {
        const found = await declarations("function f(c) { var x; if (c) { x = t(1); } if (t(c)) { t(x); } return x; } result = [f(1), f(0)];");
        expect(found).toEqual(["var x"]);
    });

    it("moves into the block holding every use, after the code before it", async () => {
        const found = await declarations("function f(c) { var x; t(0); if (c) { t(1); x = t(2); t(x); } return 3; } result = [f(1), f(0)];");
        expect(found).toEqual(["const x ="]);
    });

    it("keeps a moved declaration a var when its initializer reads it (a let would be in its dead zone)", async () => {
        const found = await declarations("function f() { var x; x = t(typeof x); return x; } result = f();");
        expect(found).toEqual(["var x ="]);
    });

    it("keeps a moved declaration a var when a hoisted function declaration uses it (it may run first)", async () => {
        const found = await declarations("function f() { var x; t(g()); x = t(1); return g(); function g() { return typeof x; } } result = f();");
        expect(found).toEqual(["var x ="]);
    });

    it("keeps a moved declaration a var when a closure in a loop captures it (a let has one binding per iteration)", async () => {
        const found = await declarations(`
            function f() {
                var fs, i, x;
                fs = [];
                for (i = 0; i < 3; i++) { x = t(i); fs.push(() => x); }
                return fs.map((g) => g());
            }
            result = f();
        `);
        expect(found).toEqual(["const fs =", "let i =", "var x ="]);
    });

    it("keeps a loop head's declaration a var when a closure captures it", async () => {
        const found = await declarations("function f() { var fs, i; fs = []; for (i = 0; i < 3; i++) { fs.push(() => i); } return fs.map((g) => g()); } result = f();");
        expect(found).toEqual(["const fs =", "var i ="]);
    });

    it("declares a for-in/of variable in the loop head, as const when the loop alone writes it", async () => {
        const found = await declarations("function f(o) { var k, v, r; r = []; for (k in o) { r.push(k); } for (v of t([1, 2])) { v = v * 2; r.push(v); } return r; } result = f({ a: 1, b: 2 });");
        expect(found).toEqual(["const r =", "const k", "let v"]);
    });

    it("keeps a loop head's declaration a var when it is used after the loop", async () => {
        const found = await declarations("function f(o) { var k; for (k in o) { t(k); } return k; } result = f({ a: 1, b: 2 });");
        expect(found).toEqual(["var k"]);
    });

    it("moves into a switch case only when that case alone uses the name", async () => {
        const found = await declarations(`
            function f(k) {
                var x, y;
                switch (k) {
                    case 1: x = t(1); return [x];
                    case 2: y = t(2); break;
                    default: y = t(3);
                }
                return y;
            }
            result = [f(1), f(2), f(3)];
        `);
        expect(found).toEqual(["var y", "const x ="]);
    });

    it("keeps a moved declaration a var when its name can't be declared lexically", async () => {
        const found = await declarations("function f() { var let; t(0); let = t(1); return [let]; } result = f();");
        expect(found).toEqual(["var let ="]);
    });

    it("moves a script's top-level var without making it lexical: it is a global object property", async () => {
        const found = await declarations("var x; t(0); x = t(1); result = [x, this.x];");
        expect(found).toEqual(["var x ="]);
    });

    it("leaves a name a catch parameter shadows to its own uses", async () => {
        const found = await declarations("function f() { var x; try { throw t(1); } catch (x) { x = t(2); t(x); } x = t(3); return [x]; } result = f();");
        expect(found).toEqual(["const x ="]);
    });

    it("leaves a name an enclosing block declares lexically to its own uses", async () => {
        const found = await declarations("function f() { var x; { let x; x = t(1); t(x); } x = t(2); return [x]; } result = f();");
        expect(found).toEqual(["let x", "const x ="]);
    });

    it("leaves a var a with statement may answer for", async () => {
        const found = await declarations("function f(o) { var x; with (o) { x = t(1); t(x); } return o.x; } result = [f({ x: 0 }), f({})];");
        expect(found).toEqual(["var x"]);
    });

    it("leaves a var a direct eval can see", async () => {
        const found = await declarations("function f() { var x; t(eval('typeof x')); x = t(1); return x; } result = f();");
        expect(found).toEqual(["var x"]);
    });

    it("leaves a var a block function writes (Annex B)", async () => {
        const found = await declarations("function f() { var x; x = t(1); { function x() {} } return typeof x; } result = f();");
        expect(found).toEqual(["var x"]);
    });

    it("leaves a var declared twice, or also a parameter", async () => {
        const found = await declarations("function f(p) { var x, p; x = t(1); var x; p = t(2); return [x, p]; } result = f(0);");
        expect(found).toEqual(["var x, p", "var x"]);
    });
});
