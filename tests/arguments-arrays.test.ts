import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["arguments-arrays"] })).code;

/** What a script leaves in `result`, with `undefined`, `NaN` and functions told apart from `null`. */
const observed = (source: string): string => {
    const context: Record<string, unknown> = { result: undefined };
    runInNewContext(source, context);
    return JSON.stringify(context.result, (_, value: unknown) => (value === undefined || typeof value === "function" || Number.isNaN(value) ? String(value) : value));
};

/** What a script and its deobfuscation leave in `result`, and the deobfuscation. */
const observe = async (code: string): Promise<[string, string, string]> => {
    const output = await run(code);
    return [observed(code), observed(output), output];
};

describe("arguments-arrays", () => {
    it.each([
        ["sloppy", ""],
        ["strict", '"use strict";\n'],
    ])("turns S[0][i] into parameters (%s mode), also when fewer arguments are passed", async (_, mode) => {
        const [before, after, output] = await observe(`${mode}
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`${mode}
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
        const [before, after, output] = await observe(`${mode}
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
        const [before, after, output] = await observe(`${mode}
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(code);
        expect(after).toBe(before);
        expect(output).toContain("return arguments[1];");
    });

    it("keeps arguments for non-simple parameter lists", async () => {
        const [before, after, output] = await observe(`
function f(a = 5, b) {
  var S = [arguments];
  return [S[0][0], S[0][1]];
}
result = [f(), f(1, 2)];
`);
        expect(after).toBe(before);
        expect(output).toContain("return [arguments[0], arguments[1]];");
    });

    it("uses arguments in nested arrows and keeps the array where a nested function or class field has its own", async () => {
        const [before, after, output] = await observe(`
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
        expect(output).toContain("var S = [arguments];");
        expect(output).toContain("return S[0][0];");
        expect(output).toContain("n = S[0].length;");
    });

    it("keeps S[0][i] where the parameter's name is shadowed", async () => {
        const [before, after, output] = await observe(`
function f(a) {
  var S = [arguments];
  return function (a) { return S[0][0] + a; }(5) + S[0][0];
}
result = [f(1), f()];
`);
        expect(after).toBe(before);
        expect(output).toContain("var S = [arguments];");
        expect(output).toContain("return S[0][0] + a;");
        expect(output).toContain("}(5) + a;");
    });

    it("keeps the array for S[0] when S[0] is written", async () => {
        const [before, after, output] = await observe(`
function f(a) {
  var S = [arguments];
  S[1] = S[0][0];
  S[0] = [7];
  return [S[0][0], S[1], a];
}
result = [f(1), f()];
`);
        expect(after).toBe(before);
        expect(output).toContain("S[0] = [7];");
        expect(output).toContain("var S_1 = S[0][0];");
    });

    it.each([
        ["arguments is reassigned", "function f(a) { var S = [arguments]; S[1] = 1; arguments = [9]; return [S[0][0], arguments[0], a, S[1]]; } result = [f(1), f()];"],
        ["element 0 is an enclosing function's arguments", "function outer() { return ((a) => { var S = [arguments]; S[1] = 1; return [S[0][0], a, S[1]]; })(5); } result = [outer(1), outer()];"],
    ])("keeps the array for S[0] when %s", async (_, code) => {
        const [before, after, output] = await observe(code);
        expect(after).toBe(before);
        expect(output).toContain("var S = [arguments];");
        expect(output).toContain("S[0][0]");
        expect(output).not.toContain("S[1]");
    });

    it("keeps arguments for S[0][i] that is deleted or called on", async () => {
        const [before, after, output] = await observe(`
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
    ])("leaves the array alone when %s", async (_, code) => {
        const [before, after, output] = await observe(code);
        expect(after).toBe(before);
        expect(output).toContain("S = [arguments");
        expect(output).toContain("S[1]");
    });

    it("converts arrays whose hoisted functions are only called after the declaration", async () => {
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
function f(a) { return [arguments][0][0]; }
var g = function () { return () => [arguments][0].length; };
result = [f(1), f(), g(1, 2)()];
`);
        expect(after).toBe(before);
        expect(output).toContain("return arguments[0];");
        expect(output).toContain("() => arguments.length");
    });

    it("leaves [arguments][0] written, deleted, called on or with other elements", async () => {
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
        const [before, after, output] = await observe(`
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
