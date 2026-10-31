import { createContext, runInContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

/** What a script leaves in `result`, run in a fresh global with a host function `host` that records its calls. */
const observed = (source: string): string => {
    const context = createContext({});
    runInContext("var hostCalls = []; function host(x) { hostCalls.push(x); return x; }", context);
    runInContext(source, context);
    return JSON.stringify([context.result, context.hostCalls]);
};

const resolved = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["pure-calls"] })).code;

describe("pure-calls", () => {
    it("resolves a substitution cipher's calls with constant arguments", async () => {
        const program = `var G = function () {
  var from = "qjGLK";
  from += "x.";
  var key;
  var f9;
  key = from;
  var to = "ABCDE /";
  f9 = (text = "") => Array.from(text).map(c => { var i; i = key.indexOf(c); if (i < 0) { return c; } else { return to[i]; } }).join("");
  var word = "qj";
  word += "GLK";
  return [f9("qjGLKLKLq"), f9(word), f9("x.?"), f9()];
};
result = G();
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("f9(");
        expect(output).toContain(`"ABCDEDEDA"`);
        expect(output).toContain(`" /?"`);
    });

    it("resolves calls of a declaration that uses another pure function and builtins", async () => {
        const program = `function pad(n) { return n < 16 ? "0" + n.toString(16) : n.toString(16); }
function hex(s) {
  var out = [];
  scan: for (var i = 0; i < s.length; i++) {
    if (i > 8) break scan;
    out.push(pad(s.charCodeAt(i) ^ 5));
  }
  return out.join("") + JSON.stringify({ n: Math.max(s.length, 2) });
}
result = [hex("ab"), hex("\\u0000z"), pad(255)];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`result = ['6467{"n":2}', '057f{"n":2}', "ff"];`);
    });

    it("keeps calls of a function that writes an outer variable", async () => {
        const program = `var count = 0;
function next(x) { count++; return x + count; }
result = [next(1), next(1), count];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("next(1)");
    });

    it("keeps calls of a function that calls an unknown function or reads the global object", async () => {
        const program = `function shout(x) { return host(x) + "!"; }
function seen() { return typeof globalThis.hostCalls; }
result = [shout("a"), seen()];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`result = [shout("a"), seen()];`);
    });

    it("keeps calls of a function that uses Math.random", async () => {
        const program = `function noisy(x) { return x + Math.random(); }
var value = noisy(1);
result = value >= 1 && value < 2;
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("noisy(1)");
    });

    it("keeps calls of a function that changes a builtin or reads its own source", async () => {
        const program = `function mark(s) { String.prototype.marked = true; return s; }
function size() { return size.toString().length; }
result = [mark("a"), "b".marked, size() > 0];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`mark("a")`);
        expect(output).toContain("size() > 0");
    });

    it("keeps calls whose argument isn't constant, and resolves the others", async () => {
        const program = `function twice(s) { return s + s; }
result = [twice(host("a")), twice("b")];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`twice(host("a"))`);
        expect(output).toContain(`"bb"`);
    });

    it("keeps calls that run before the function is assigned", async () => {
        const program = `var early;
try { early = f("a"); } catch (error) { early = error.name; }
var f = function (s) { return s + "!"; };
result = [early, f("b")];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`f("a")`);
        expect(output).toContain(`"b!"`);
    });

    it("keeps calls that throw", async () => {
        const program = `function first(s) { return s.charAt(0); }
var caught;
try { first(undefined); } catch (error) { caught = error.name; }
result = [caught, first("xy")];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("first(undefined)");
        expect(output).toContain(`"x"`);
    });
    it("keeps calls whose meaning a strict-mode evaluation would change", async () => {
        const program = `function self() { return typeof this; }
function alias(a) { arguments[0] = "z"; return a; }
function block() { if (true) { function escape() { return "mine"; } } return escape("a b"); }
function guarded(s) { try { String.prototype.seen = s; } catch (error) { return "caught"; } return s; }
result = [self(), alias("a"), block(), guarded("g"), "x".seen];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`result = [self(), alias("a"), block(), guarded("g"), "x".seen];`);
    });

    it("keeps calls that change a pure function they use", async () => {
        const program = `function counter() {}
function count(s) { counter.n = (counter.n || 0) + 1; return s + counter.n; }
result = [count("a"), count("a")];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`count("a")`);
    });

    it("keeps calls that reach the Function constructor or see that builtins are frozen", async () => {
        const program = `var result = "set";
function outside() { return outside.constructor("return typeof result")(); }
function frozen() { return Object.isFrozen(Array.prototype); }
result = [outside(), frozen()];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("result = [outside(), frozen()];");
    });

    it("keeps calls where one name means different bindings, or the result's name is declared", async () => {
        const program = `function big() { return Infinity; }
result = (function () {
  var Infinity = 5;
  function both() { return big() + Infinity; }
  return both();
})();
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("return big() + Infinity;");
        expect(output).toContain("return both();");
    });

    it("keeps calls of functions with engine-dependent or deferred work", async () => {
        const program = `function root(x) { return x ** 0.5; }
function order(s) { return s.split("").sort((a, b) => a < b ? -1 : 1).join(""); }
function later(s) { (async () => { throw s; })().catch(() => {}); return s; }
function third(x) { return x.toString(3); }
function compare(a, b) { return a.localeCompare(b); }
function sine(x) { return Math.sin(x); }
result = [root(2), order("cab"), later("x"), third(0.1), compare("a", "b"), sine(1), third(9)];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        for (const kept of [`root(2)`, `order("cab")`, `later("x")`, `third(0.1)`, `compare("a", "b")`, `sine(1)`]) expect(output).toContain(kept);
        expect(output).toContain(`"100"`);
    });

    it("keeps calls that run too long", async () => {
        const program = `function spin(n) { while (n > 0) {} return n; }
result = [spin(0)];
if (result[0] !== 0) spin(1);
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("result = [0];");
        expect(output).toContain("spin(1);");
    });

    it("keeps calls of a function the program may replace", async () => {
        const program = `function f(c) {
  if (c) {
    function inner(s) { return s + "!"; }
  }
  var caught;
  try { caught = inner("a"); } catch (error) { caught = error.name; }
  function again(s) { return s; }
  again = function () { return "replaced"; };
  return [caught, again("b")];
}
var g = function (s) { return s + "?"; };
globalThis["g"] = function () { return "replaced"; };
result = [f(true), f(false), g("c")];
`;
        const output = await resolved(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`inner("a")`);
        expect(output).toContain(`again("b")`);
        expect(output).toContain(`g("c")`);
    });

    it("resolves calls in code an earlier pass rewrote", async () => {
        const program = `var u = void 0;
function tag(s) { return s + "/" + u; }
result = tag("a");
`;
        const { code: output } = await deobfuscate(program, { passes: ["simplify", "pure-calls"] });
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`result = "a/undefined";`);
    });
});
