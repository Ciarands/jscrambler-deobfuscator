import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["arguments-arrays"] })).code;

/** `result` exists before the program runs, so strict programs can assign it. */
const RUN: Run = { globals: () => ({ result: undefined }) };

const beforeAndAfter = async (code: string): Promise<[string, string, string]> => {
    const output = await run(code);
    return [observe(code, RUN), observe(output, RUN), output];
};

describe("arguments-arrays", () => {
    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("turns S[0][i] into parameters (%s mode), also when fewer arguments are passed", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a, b, c) {
          var S = [arguments];
          S[3] = S[0][0] + "-" + S[0][2];
          return [S[3], typeof S[0][1], S[0][2]];
        }
        result = [f(1), f(1, 2, 3), f()];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("arguments");
        expect(output).toContain('var S_3 = a + "-" + c;');
    });

    it("turns the other slots into locals: undefined before the first write, one binding per call shared with closures", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function counter(n) {
          var S = [arguments];
          var early = typeof S[5];
          S[5] = S[0][0];
          S[6] = function () { return S[5]++; };
          if (n > 0) S[7] = counter(n - 1);
          return [early, S[6], S[7]];
        }
        var a = counter(2), b = counter(1);
        result = [a[0], a[1](), a[1](), b[1](), a[1](), a[2][1](), a[2][2][1](), a[2][1]()];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("[arguments]");
        expect(output).toContain("var S_5 = n;");
        expect(output).toContain("S_7 = counter(n - 1)");
    });

    it("turns a parameter written only through S[0][i] into that parameter", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          S[0][0] = S[0][0] * 2;
          S[0][0]++;
          return S[0][0];
        }
        result = [f(3), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("a = a * 2;");
    });

    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("keeps arguments where S[0][i] is written and the parameter is used too (%s mode)", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], a];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("arguments[0] = 5;");
    });

    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("keeps arguments where S[0][i] is written and the parameter is shadowed at a use (%s mode)", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a) {
          var S = [arguments];
          S[0][0] = 2;
          return [S[0][0], function (a) { return S[0][0]; }(9)];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("arguments[0] = 2;");
    });

    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("keeps arguments when the parameter is written (%s mode)", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a) {
          var S = [arguments];
          a = 2;
          return S[0][0];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("return arguments[0];");
    });

    it("keeps arguments when a function declaration redeclares the parameter", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          return [S[0][0], typeof a];
          function a() {}
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("return [arguments[0], typeof a];");
    });

    it("keeps arguments when the arguments object escapes, through S[0] or directly", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function poke(x) { x[0] = 9; }
        function viaSlot(a) {
          var S = [arguments];
          poke(S[0]);
          return [S[0][0], a];
        }
        function direct(a) {
          var S = [arguments];
          poke(arguments);
          return S[0][0];
        }
        function written(a) {
          var S = [arguments];
          arguments[0] = 5;
          return S[0][0];
        }
        function calledOn(a, b) {
          var S = [arguments];
          arguments[0]();
          return S[0][1];
        }
        result = [viaSlot(1), viaSlot(), direct(1), direct(), written(1), written(), calledOn(function () { this[1] = 7; })];
        `);
        expect(after).toBe(before);
        expect(output).toContain("poke(arguments);\n  return [arguments[0], a];");
        expect(output).toContain("arguments[0] = 5;\n  return arguments[0];");
        expect(output).not.toContain("[arguments]");
    });

    it("turns S[0][i] into parameters when arguments only goes to a function literal's builtin apply", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a, b) {
          var S = [arguments];
          return [S[0][1], function () { this.n = arguments.length; return arguments.length + S[0][0]; }.apply({}, arguments)];
        }
        var g = (a) => function (a2) { var S = [arguments]; return [S[0][0], (() => 1).apply(null, arguments)]; }(a);
        result = [f(1, 2), f(), g(3)];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("S[0]");
        expect(output).toContain("return arguments.length + a;");
        expect(output).toMatch(/return \[\s*b,/);
        expect(output).toMatch(/return \[\s*a2,/);
    });

    it.each([
        [
            "an object's own apply",
            "var o = { apply: function (t, args) { args[1] = 7; } }; function f(a, b) { var S = [arguments]; o.apply(this, arguments); return S[0][1]; } result = [f(1), f(1, 2)];",
        ],
        ["apply's this argument", "function f(a, b) { var S = [arguments]; (function () { this[1] = 7; }).apply(arguments, []); return S[0][1]; } result = [f(1), f(1, 2)];"],
        ["apply's this argument, behind a spread", "function f(a, b) { var S = [arguments]; (function () { this[1] = 7; }).apply(...[], arguments); return S[0][1]; } result = [f(1), f(1, 2)];"],
        ["the callee of call", "function f(a, b) { var S = [arguments]; (function (x) { x[1] = 7; }).call(null, arguments); return S[0][1]; } result = [f(1), f(1, 2)];"],
    ])("keeps arguments when it is handed to %s", async (_, code) => {
        const [before, after, output] = await beforeAndAfter(code);
        expect(after).toBe(before);
        expect(output).toContain("return arguments[1];");
    });

    it("turns S[0][i] into plain-named parameters of non-simple parameter lists, keeping arguments for one with a default", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a = 5, b, { c }) {
          var S = [arguments];
          S[0][1] = S[0][1] + 1;
          return [S[0][0], S[0][1], S[0][2].c];
        }
        result = [f(undefined, 1, { c: 2 }), f(7, 1, { c: 3 })];
        `);
        expect(after).toBe(before);
        expect(output).toContain("b = b + 1;");
        expect(output).toContain("return [arguments[0], b, arguments[2].c];");
    });

    it("uses arguments in nested arrows and a local where a nested function or class field has its own", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          S[0].length;
          var viaArrow = () => S[0].length;
          var C = class { n = S[0].length; };
          return [viaArrow(), function () { return S[0][0]; }(7), new C().n];
        }
        result = [f(1), f(2, 3)];
        `);
        expect(after).toBe(before);
        expect(output).toContain("var viaArrow = () => arguments.length;");
        expect(output).toContain("var S_0 = arguments;");
        expect(output).toContain("return S_0[0];");
        expect(output).toContain("n = S_0.length;");
        expect(output).not.toContain("[arguments]");
    });

    it("reads a copy of the parameter where its name is shadowed", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          return function (a) { return S[0][0] + a; }(5) + S[0][0] + (() => { let a = 3; return S[0][0] * a; })();
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("var a_1 = a;");
        expect(output).toContain("return a_1 + a;");
        expect(output).toContain("}(5) + a +");
        expect(output).toContain("return a_1 * a;");
        expect(output).not.toContain("arguments");
    });

    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("uses a local for S[0] where the parameter is written and arguments isn't visible (%s mode)", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a) {
          var S = [arguments];
          var read = function (a) { return S[0][0]; };
          a = 2;
          return [read(9), S[0][0], a];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("var S_0 = arguments;");
        expect(output).toContain("return S_0[0];");
        expect(output).not.toContain("[arguments]");
    });

    it("doesn't copy a parameter whose name is shadowed where the array is created", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          block: {
            let a = 9;
            var S = [arguments];
            return [a, S[0][0], function (a) { return S[0][0]; }(2)];
          }
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("= a;");
        expect(output).toMatch(/return \[\s*a,\s*arguments\[0\],\s*function \(a\) \{/);
        expect(output).toContain("return S_0[0];");
    });

    it("takes a nested function's sloppy block function for a binding of its name there (Annex B)", async () => {
        const [before, after] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          S[1] = "slot";
          return function () { var r = [S[0][0], S[1]]; { function a() {} function S_1() {} } return r; }();
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
    });

    it("names a parameter where only a converted nested array shadowed it", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(e, a) {
          var S = [arguments];
          return function () {
            var a = [arguments];
            a[1] = "inner";
            return S[0][1] + a[1];
          }();
        }
        result = [f(1, "outer"), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain('var a_1 = "inner";');
        expect(output).toContain("return a + a_1;");
    });

    it("turns S[0] into a local when S[0] is written", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          S[1] = S[0][0];
          S[0] = [7];
          return [S[0][0], S[1], a];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("var S_0 = arguments;");
        expect(output).toContain("S_0 = [7];");
        expect(output).toContain("var S_1 = S_0[0];");
    });

    it.each([
        ["arguments is reassigned", "function f(a) { var S = [arguments]; S[1] = 1; arguments = [9]; return [S[0][0], arguments[0], a, S[1]]; } result = [f(1), f()];"],
        ["element 0 is an enclosing function's arguments", "function outer() { return ((a) => { var S = [arguments]; S[1] = 1; return [S[0][0], a, S[1]]; })(5); } result = [outer(1), outer()];"],
    ])("turns S[0] into a local when %s", async (_, code) => {
        const [before, after, output] = await beforeAndAfter(code);
        expect(after).toBe(before);
        expect(output).toContain("var S_0 = arguments;");
        expect(output).toContain("S_0[0]");
        expect(output).not.toContain("S[");
    });

    it("keeps arguments where S[0][i] is written and arguments is read directly, but not for its length or by a literal ignoring it", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function read(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], arguments[0]];
        }
        function length(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], arguments.length];
        }
        function applied(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function (x) { return x; }.apply(null, arguments)];
        }
        function appliedOwn(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function () { return arguments[0]; }.apply(null, arguments)];
        }
        function ignored(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function () { return 1; }.apply(null, arguments), (() => 2).apply(null, arguments)];
        }
        function viaFrame(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function () { var T = [arguments]; T[1] = 3; return T[1]; }.apply(null, arguments)];
        }
        function viaFrameRead(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function () { var T = [arguments]; return T[0][0]; }.apply(null, arguments)];
        }
        function viaKeptFrame(a) {
          var S = [arguments];
          S[0][0] = 5;
          return [S[0][0], function () { var T = [arguments]; return T; }.apply(null, arguments)[0][0]];
        }
        result = [
          read(1), read(), length(1), length(), applied(1), applied(), appliedOwn(1), appliedOwn(),
          ignored(1), ignored(), viaFrame(1), viaFrame(), viaFrameRead(1), viaFrameRead(), viaKeptFrame(1), viaKeptFrame(),
        ];
        `);
        expect(after).toBe(before);
        expect(output).toContain("arguments[0] = 5;\n  return [arguments[0], arguments[0]];");
        expect(output).toContain("a = 5;\n  return [a, arguments.length];");
        expect(output).toMatch(/arguments\[0\] = 5;\s*return \[\s*arguments\[0\],\s*function \(x\) \{/);
        expect(output).toMatch(/arguments\[0\] = 5;\s*return \[\s*arguments\[0\],\s*function \(\) \{\s*return arguments\[0\];/);
        expect(output).toMatch(/a = 5;\s*return \[\s*a,\s*function \(\) \{\s*return 1;/);
        expect(output).toMatch(/a = 5;\s*return \[\s*a,\s*function \(\) \{\s*var T_1 = 3;/);
        // read, applied, appliedOwn, viaFrameRead and viaKeptFrame.
        expect(output.match(/arguments\[0\] = 5;/g)).toHaveLength(5);
    });

    it("keeps arguments when a parameter name is declared twice", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a, a) {
          var S = [arguments];
          return [S[0][0], S[0][1]];
        }
        result = [f(1, 2), f(1)];
        `);
        expect(after).toBe(before);
        expect(output).toContain("return [arguments[0], arguments[1]];");
    });

    it("keeps arguments for S[0][i] that is deleted or called on", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function deleted(a) {
          var S = [arguments];
          delete S[0][0];
          return S[0][0];
        }
        function called(a) {
          var S = [arguments];
          return S[0][0]();
        }
        result = [deleted(1), called(function () { return this.length; })];
        `);
        expect(after).toBe(before);
        expect(output).toContain("delete arguments[0];");
        expect(output).toContain("return arguments[0]();");
    });

    it.each([
        ["passed to a function", "function f(a) { var S = [arguments]; S[1] = 1; poke(S); return S[1]; } function poke(s) { s[1] = 2; } result = f();"],
        ["indexed dynamically", "function f(i) { var S = [arguments]; S[1] = 1; S[2] = 2; return S[i]; } result = [f(1), f(2)];"],
        ["a slot is called as its method", "function f() { var S = [arguments]; S[1] = function () { return Array.isArray(this); }; return S[1](); } result = f();"],
        ["a slot is deleted", "function f() { var S = [arguments]; S[1] = 1; delete S[1]; return S[1]; } result = f();"],
        ["it is used inside with", "function f(o) { var S = [arguments]; S[1] = 1; with (o) { return S[1]; } } result = [f({}), f({ S: [0, 2] })];"],
        ["the function calls eval", 'function f() { var S = [arguments]; S[1] = 1; return eval("S[1]"); } result = f();'],
        [
            "a hoisted function using it is called first",
            'function f() { var r = g(); var S = [arguments]; S[1] = 1; return [r, S[1]]; function g() { try { return S[1]; } catch (e) { return "threw"; } } } result = f();',
        ],
        ["it is used before its declaration", 'function f() { try { S[1]; } catch (e) { var r = "threw"; } var S = [arguments]; S[1] = 1; return [r, S[1]]; } result = f();'],
        ["an initializer element runs code", 'function f() { var S = [arguments, peek()]; return S[1]; function peek() { try { return S[1]; } catch (e) { return "threw"; } } } result = f();'],
        ["it is declared again", "function f() { var S = [arguments]; S[1] = 1; var S = [0, 2]; return S[1]; } result = f();"],
        ["it is a const", "function f(x) { const S = [arguments]; if (x) S[1] = 1; return S[1]; } result = [f(1), f()];"],
        ["it is declared in a block", 'function f(x) { if (x) { var S = [arguments]; S[1] = 1; } try { return S[1]; } catch (e) { return "threw"; } } result = [f(1), f()];'],
        ["it is assigned in a loop", "function f(n) { var S; for (var i = 0; i < n; i++) { S = [arguments]; S[1] = (S[1] || 0) + i; } return n ? S[1] : 0; } result = [f(0), f(3)];"],
        ["it is assigned twice", "function f(x) { var S; S = [arguments]; S[1] = 1; var g = function () { return S[1]; }; if (x) S = [arguments]; return [g(), S[1]]; } result = [f(0), f(1)];"],
        ["it is read before it is assigned", "function f() { var S; var r = typeof S; S = [arguments]; S[1] = 1; return [r, S[1]]; } result = f();"],
        ["it is assigned as part of an expression", "function f() { var S; var T = S = [arguments]; S[1] = 1; return [T[1], S[1]]; } result = f();"],
        ["it is assigned in an if test", "function f(x) { var S; if (S = [arguments]) { S[1] = x; } return S[1]; } result = [f(1), f()];"],
        [
            "a break before it can leave a labeled block around it",
            'function f(x) { out: { if (x) break out; var S = [arguments]; S[1] = 1; } try { return S[1]; } catch (e) { return "threw"; } } result = [f(0), f(1)];',
        ],
        [
            "a labeled block around it declares a function",
            'function f(x) { out: { var r = g(); var S = [arguments]; S[1] = 1; function g() { try { return S[1]; } catch (e) { return "threw"; } } } return [r, S[1]]; } result = f();',
        ],
        ["its bare declaration is in a for head", "function f() { for (var S, i = 0; i < 1; i++); S = [arguments]; S[1] = 1; return S[1]; } result = f();"],
    ])("leaves the array alone when %s", async (_, code) => {
        const [before, after, output] = await beforeAndAfter(code);
        expect(after).toBe(before);
        expect(output).toContain("S = [arguments");
        expect(output).toContain("S[1]");
    });

    it("converts the assignment form: a bare var, then the statement S = [arguments] in a labeled block", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a, b) {
          var S, n;
          n = 2;
          out: {
            S = [arguments, 1];
            S[3] = S[0][0] + S[1];
            if (!b) break out;
            S[4] = function () { return S[3] + S[0][1]; };
          }
          return [S[3], S[4] ? S[4].call() : 0, n];
        }
        function empty(a) {
          var S;
          S = [arguments];
          return a;
        }
        result = [f(1), f(1, 2), empty(3)];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("arguments");
        expect(output).toContain("var n;");
        expect(output).toContain("var S_1 = 1;");
        expect(output).toContain("var S_3 = a + S_1;");
        expect(output).toContain("return S_3 + b;");
        expect(output).toMatch(/function empty\(a\) \{\s*return a;\s*\}/);
    });

    it("lets hoisted functions reference each other before the array is created", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          function walk(n) { return n > 0 ? walk(n - 1) + 1 : read(); }
          function read() { read = function () { return -1; }; return S[1] + S[0][0]; }
          var S = [arguments];
          S[1] = 10;
          return [walk(2), walk(1)];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("[arguments]");
        expect(output).toContain("return S_1 + a;");
    });

    it("converts arrays whose hoisted functions are only called after the declaration", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          function g() { return S[1] + S[0][0]; }
          log.push("before");
          var S = [arguments];
          S[1] = 1;
          return g();
        }
        var log = [];
        result = [f(1), log];
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("[arguments]");
        expect(output).toContain("return S_1 + a;");
    });

    it("picks another name where the slot's would be shadowed at a use, shadow an outer name or is taken", async () => {
        const [before, after, output] = await beforeAndAfter(`
        var S_2 = 10;
        function f(a) {
          var S = [arguments];
          var S_3 = "local";
          S[1] = "outer";
          S[2] = 2;
          S[3] = 3;
          function g() { var S_1 = "inner"; return S[1] + S_1; }
          return [g(), S[2] + S_2, S[3] + S_3];
        }
        result = f();
        `);
        expect(after).toBe(before);
        expect(output).toContain('var S_1_1 = "outer";');
        expect(output).toContain("var S_2_1 = 2;");
        expect(output).toContain("var S_3_1 = 3;");
        expect(output).toContain('var S_1 = "inner";');
    });

    it("names two arrays of one function apart", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f() {
          var a = [arguments];
          var a_1 = [arguments];
          a[1] = "a";
          a_1[1] = "a_1";
          return a[1] + a_1[1];
        }
        result = f();
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("[arguments]");
        expect(output).toContain('var a_1_1 = "a";');
        expect(output).toContain('var a_1_1_1 = "a_1";');
    });

    it("avoids the names a nested function's conversion added where an outer slot is used", async () => {
        const [before, after, output] = await beforeAndAfter(`
        var X_1 = "global";
        function f() {
          var X = [arguments];
          X[1] = "outer";
          return [X_1, function () {
            var X_1 = [arguments];
            X_1[1] = "inner";
            return X[1] + X_1[1];
          }()];
        }
        result = f();
        `);
        expect(after).toBe(before);
        expect(output).not.toContain("[arguments]");
        expect(output).toContain('var X_1_1 = "inner";');
        expect(output).toContain('var X_1_2 = "outer";');
    });

    it("folds [arguments][0] reads to arguments", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) { return [arguments][0][0]; }
        var g = function () { return () => [arguments][0].length; };
        result = [f(1), f(), g(1, 2)()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("return a;");
        expect(output).toContain("() => arguments.length");
    });

    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("turns direct arguments[i] reads into parameters (%s mode)", async (_, mode) => {
        const [before, after, output] = await beforeAndAfter(`${mode}
        function f(a, b) {
          var inner = [1, 2].map(function (a) { return arguments[0] * 10; });
          var arrow = () => arguments[1];
          return [arguments[0], typeof arguments[1], arguments.length, inner, arrow()];
        }
        function g(a) {
          return (function () { return arguments.length; }).apply(this, arguments) + "/" + arguments[0];
        }
        function h(a, b = function () { return arguments.length; }) {
          return [arguments[0], b(a)];
        }
        result = [f(1, 2), f(3), f(), g(4, 5), g(), h(1), h(2, (c) => -c)];
        `);
        expect(after).toBe(before);
        expect(output).not.toMatch(/arguments\[/);
        expect(output).toContain("return a * 10;");
        expect(output).toContain("var arrow = () => b;");
        expect(output).toContain("return [a, typeof b, arguments.length, inner, arrow()];");
        expect(output).toContain("return [a, b(a)];");
    });

    it("keeps direct arguments[i] reads where the parameter can differ from the element", async () => {
        const [before, after, output] = await beforeAndAfter(`"use strict";
        var mutate = (args) => { args[0] = "changed"; };
        function escapes(a) { mutate(arguments); return arguments[0]; }
        function writes(a) { arguments[0] = "changed"; return [a, arguments[0]]; }
        function writesParameter(a) { a = "changed"; return arguments[0]; }
        function evals(a) { eval("a = 'changed'"); return arguments[0]; }
        function nestedEval(a) { (() => eval("a = 'changed'"))(); return arguments[0]; }
        function redeclares(a) { function a() {} return typeof arguments[0]; }
        function writesInDefault(a, b = (arguments[0] = "changed")) { return arguments[0]; }
        function arrayWritesInDefault(a, b = (arguments[0] = "changed")) { var S = [arguments]; return S[0][0]; }
        function shadowed(a) { return (() => { var a = "inner"; return arguments[0]; })(); }
        result = [escapes(1), writes(1), writesParameter(1), evals(1), nestedEval(1), redeclares(1), writesInDefault(1), arrayWritesInDefault(1), shadowed(1)];
        `);
        expect(after).toBe(before);
        expect(output.match(/arguments\[0\]/g)).toHaveLength(12);
        expect(output).not.toContain("[arguments]");
    });

    it("keeps direct arguments[i] reads in sloppy mode where an element is deleted or the name means a with object's property", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function deletes(a) { delete arguments[0]; return [a, arguments[0]]; }
        function within(a) { with ({ a: "property" }) { return arguments[0]; } }
        result = [deletes(1), within(1)];
        `);
        expect(after).toBe(before);
        expect(output.match(/arguments\[0\]/g)).toHaveLength(3);
    });

    it("leaves [arguments][0] written, deleted, called on or with other elements", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function written(a) { [arguments][0] = 5; return arguments.length; }
        function deleted(a) { return delete [arguments][0]; }
        function called() { try { return [arguments][0](); } catch (e) { return e.message; } }
        var log = [];
        function more() { return [arguments, log.push(1)][0].length; }
        result = [written(1), deleted(1), called(), more(1), log];
        `);
        expect(after).toBe(before);
        expect(output.match(/\[arguments(, log\.push\(1\))?\]\[0\]/g)).toHaveLength(4);
    });

    it("counts a folded [arguments][0] write as an arguments use", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(a) {
          var S = [arguments];
          [arguments][0][0] = 5;
          return S[0][0];
        }
        result = [f(1), f()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("arguments[0] = 5;\n  return arguments[0];");
    });

    it("keeps initialized elements as initialized locals", async () => {
        const [before, after, output] = await beforeAndAfter(`
        function f(x) {
          var S = [arguments, 1, , x];
          S[2] = S[1] + S[3];
          return S;
        }
        function g(x) {
          var T = [arguments, 1, , x];
          T[2] = T[1] + T[3];
          return [T[1], T[2], T[3]];
        }
        result = [g(4), g()];
        `);
        expect(after).toBe(before);
        expect(output).toContain("var T_1 = 1, T_2, T_3 = x;");
        expect(output).toContain("var S = [arguments, 1, , x];");
    });
});
