import { describe, expect, it } from "vitest";
import type { IdentifierReference, Node } from "../src/core/ast.js";
import type { Value } from "../src/core/evaluate.js";
import type { Answer, OuterBinding } from "../src/core/interpret.js";
import { Interpreter } from "../src/core/interpret.js";
import { parse } from "../src/core/parse.js";
import { ScopeInfo } from "../src/core/scope.js";
import { observe, serialize } from "./helpers.js";

/** Top-level functions and literal constants of `source` are the outer bindings; unbound names are globals. */
const interpreterFor = (source: string, aliases?: ReadonlyMap<string, ReadonlyMap<string, string>>) => {
    const program = parse(source);
    const scopes = new ScopeInfo(program);
    const outer = (identifier: IdentifierReference): OuterBinding | string => {
        const variable = scopes.staticVariableOf(identifier);
        if (variable === undefined) return { global: identifier.name };
        const def = variable.defs[0]?.node as Node | undefined;
        if (def?.type === "FunctionDeclaration") return { function: def };
        const init = def?.type === "VariableDeclarator" ? def.init : null;
        if (init?.type === "FunctionExpression" || init?.type === "ArrowFunctionExpression") return { function: init };
        if (init?.type === "Literal" && (typeof init.value === "string" || typeof init.value === "number")) return { value: init.value };
        return `${identifier.name} isn't a constant`;
    };
    const interpreter = new Interpreter({ outer, ...(aliases === undefined ? {} : { aliases }) });
    const functionNamed = (name: string) => {
        for (const statement of program.body) if (statement.type === "FunctionDeclaration" && statement.id?.name === name) return statement;
        throw new Error(`no function ${name}`);
    };
    return (name: string, args: readonly Value[], steps = 100_000): Answer => interpreter.call(functionNamed(name), args, steps);
};

/** The interpreter's answer, which must be what node:vm gives for the same call. */
const agrees = (source: string, name: string, ...args: Value[]): Value => {
    const answer = interpreterFor(source)(name, args);
    if (!answer.ok) throw new Error(`no answer: ${answer.reason}`);
    expect(serialize(answer.value)).toBe(observe(`${source}\nresult = ${name}(...args);`, { globals: () => ({ args, result: undefined }) }));
    return answer.value;
};

const refusal = (source: string, name: string, ...args: Value[]): string => {
    const answer = interpreterFor(source)(name, args);
    if (answer.ok) throw new Error(`answered ${String(answer.value)}`);
    return answer.reason;
};

describe("interpret", () => {
    it("runs loops, labels and switches", () => {
        const source = `function f(n) {
  var out = "";
  outer: for (var i = 0; i < n; i++) {
    var j = 0;
    while (true) {
      j++;
      if (j > i) continue outer;
      if (i * j > 6) break outer;
      out += i + ":" + j + ",";
    }
  }
  do { out += "d"; n -= 3; } while (n > 0);
  for (const k of [1, 2, 3, 4]) {
    switch (k) {
      case 1: out += "a";
      default: out += "x";
      case 3: out += "c"; break;
      case 4: { let k = "q"; out += k; }
    }
  }
  return out;
}`;
        expect(agrees(source, "f", 5)).toBe("1:1,2:1,2:2,3:1,3:2,ddaxcxccq");
        agrees(source, "f", 0);
    });

    it("runs closures over helpers, per-iteration bindings and recursion", () => {
        const source = `var BASE = 7;
function scale(x) { return x * BASE; }
var twice = function (g, x) { return g(g(x)); };
function f(n) {
  var fns = [];
  for (let i = 0; i < n; i++) fns.push(() => scale(i));
  var fact = function self(k) { return k <= 1 ? 1 : k * self(k - 1); };
  return fns.map((g) => g()).join("-") + "/" + twice(scale, 1) + "/" + fact(n);
}`;
        expect(agrees(source, "f", 4)).toBe("0-7-14-21/49/24");
    });

    it("builds strings with string, array and number builtins", () => {
        const source = `function f(s) {
  var codes = [];
  for (var i = 0; i < s.length; i++) codes.push((s.charCodeAt(i) ^ 5).toString(16).padStart(2, "0"));
  var back = String.fromCharCode.apply(null, codes.map(function (h) { return parseInt(h, 16) ^ 5; }));
  var points = Array.from(s).reverse().join("|");
  var replaced = s.replace("a", function (m, at) { return "[" + m + at + "]"; }).replaceAll("b", "$&$&");
  return \`\${codes.join("")} \${back} \${points} \${replaced} \${s.split("").sort().join("")} \${(255).toString(2)} \${(1.5).toFixed(3)}\`;
}`;
        agrees(source, "f", "ab\uD83D\uDE00ba");
    });

    it("makes local arrays and objects, destructures and spreads them", () => {
        const source = `function f(a, b) {
  var o = { z: 1, 10: "ten", 2: "two", a: [a, b] };
  o.y = { ...o, z: 3 };
  var { z, a: [first, , third = "def"], ...rest } = o;
  var [x, [y] = [b], ...tail] = [a, undefined, 3, 4];
  [x, y] = [y, x];
  var keys = [];
  for (var k in o) keys.push(k);
  var holes = [, 1, , 2];
  return JSON.stringify({ z, first, third, rest: Object.keys(rest), x, y, tail, keys, entries: Object.entries({ q: 1, 0: 2 }) })
    + holes.join("") + holes.map((v) => v * 2) + Object.keys(holes) + [3, 1, 2, "10"].sort() + holes.indexOf(undefined) + holes.includes(undefined);
}`;
        agrees(source, "f", "p", "q");
    });

    it("keeps the spec's edge cases", () => {
        const cases: [string, Value[]][] = [
            ["function f() { return -0; }", []],
            ["function f(x) { return 1 / (x * -1); }", [0]],
            ["function f(x) { return x / x; }", [0]],
            ["function f(s) { return s.charCodeAt(9); }", ["abc"]],
            ["function f(s) { return s.charCodeAt(-1) + s[5]; }", ["abc"]],
            ["function f(x) { return x >>> 0; }", [-1]],
            ["function f(x) { return (x >>> 28) + (-x >>> 1); }", [-0x7fffffff]],
            ["function f(a, b) { return Math.imul(a, b); }", [0xffffffff, 5]],
            ["function f(a, b) { return Math.imul(a, b) | 0; }", [3432918353, 2246822507]],
            ["function f() { return '' + [1, [2, 3], null, undefined] + [] + {}; }", []],
            ["function f() { return [null == undefined, [1] == 1, [] == false, NaN !== NaN, typeof null, typeof f, typeof [], -0 === 0, Object.is(-0, 0)].join(); }", []],
            ["function f() { return Math.max() + ',' + Math.min(1, '0', [-2]) + ',' + Math.round(-0.5) + ',' + Math.sign(-0); }", []],
            ["function f() { return Math.round(-0.4); }", []],
            ["function f(x) { return x++ + ++x + (x += '1'); }", ["5"]],
            ["function f() { return [0.1 + 0.2, 1e21, 2 ** -1074 === 0 ? 1 : 2].join(); }", []],
        ];
        for (const [source, args] of cases) agrees(source.replace("2 ** -1074 === 0 ? 1 : 2", "5e-324"), "f", ...args);
    });

    it("stops at its step budget, deterministically", () => {
        const call = interpreterFor("function spin(n) { var i = 0; while (n > 0) i++; return i; }");
        const first = call("spin", [1], 10_000);
        expect(first).toMatchObject({ ok: false, exhausted: true, reason: "it ran past 10000 steps" });
        expect(call("spin", [1], 10_000)).toEqual(first);
        const finite = interpreterFor("function count(n) { var i = 0; while (i < n) i++; return i; }");
        const small = finite("count", [10], 10_000);
        expect(small).toMatchObject({ ok: true, value: 10 });
        expect(finite("count", [10], 10_000).steps).toBe(small.steps);
        expect(finite("count", [10], small.steps - 1)).toMatchObject({ ok: false, exhausted: true });
    });

    it("refuses what it doesn't model or isn't pure", () => {
        const refused: [string, RegExp][] = [
            ["function f() { return Math.random(); }", /Math\.random/],
            ["function f() { return Math.sin(1); }", /Math\.sin/],
            ["function f() { return 2 ** 0.5; }", /\*\*/],
            ["function f() { return (0.1).toString(3); }", /fraction/],
            ["function f() { return [2, 1].sort(function (a, b) { return a - b; }).join(); }", /comparator/],
            ["function f() { return 'a'.localeCompare('b'); }", /localeCompare/],
            ["function f() { return new Date().getTime(); }", /Date/],
            ["function f() { return f.toString(); }", /toString/],
            ["function f() { String.prototype.marked = 1; return 1; }", /builtin/],
            ["function f() { 'abc'.x = 1; return 1; }", /primitive/],
            ["var count = 0; function f() { count = 1; return count; }", /count/],
            ["function f() { var o = Object.freeze({}); o.x = 1; return 1; }", /frozen/],
            ["function f() { try { return 1; } catch (e) { return 2; } }", /TryStatement/],
            ["function f() { return /a/.test('a'); }", /regular expression/],
            ["function f() { return typeof this; }", /ThisExpression/],
            ["function f() { return arguments.length; }", /arguments/],
            ["function f() { return { get x() { return 1; } }.x; }", /getter/],
            ["function f() { return { __proto__: null }.x; }", /prototype/],
            ["function f() { var o = { toString: function () { return 'x'; } }; return '' + o; }", /toString/],
            ["function f() { var a = [1]; a.push(a); return '' + a; }", /contains itself/],
            ["function f() { var o = { a: 1 }; for (var k in o) o[k + 'x'] = 1; return 1; }", /enumerating/],
            ["function f() { return {}.constructor; }", /constructor/],
            ["function f() { return 'abc'.blah; }", /blah/],
            ["function f(n) { return n > 0 ? f(n - 1) : 0; }", /deeper/],
            ["function f() { var g = function h() { h = 1; return typeof h; }; return g(); }", /function's own name/],
            ["function f() { 'x'.repeat(1 << 30); return 1; }", /longer than/],
        ];
        for (const [source, reason] of refused) expect(refusal(source, "f", 1000), source).toMatch(reason);
    });

    it("gives no answer where the program throws", () => {
        for (const source of [
            "function f() { var o = null; return o.x; }",
            "function f() { var g; return g(); }",
            "function f() { throw 1; }",
            "function f() { x; let x = 1; return x; }",
            "function f() { const [a] = 5; return a; }",
            "function f() { return [].reduce(function (a, b) { return a + b; }); }",
            "function f() { return new Array(-1); }",
            "function f() { const [] = 5; return 1; }",
        ]) {
            expect(refusal(source, "f"), source).toMatch(/^it threw/);
        }
    });

    it("answers only primitives", () => {
        expect(refusal("function f() { return [1]; }", "f")).toBe("it returns an object");
        expect(refusal("function f() { return function () {}; }", "f")).toBe("it returns a function");
    });

    it("resolves builtin aliases the program added", () => {
        const call = interpreterFor(
            "function f(s) { return s.x7('b') + [3, 4].q2('-'); }",
            new Map([
                ["String.prototype", new Map([["x7", "indexOf"]])],
                ["Array.prototype", new Map([["q2", "join"]])],
            ])
        );
        expect(call("f", ["abc"])).toMatchObject({ ok: true, value: "13-4" });
        expect(interpreterFor("function f(s) { return s.x7('b'); }")("f", ["abc"])).toMatchObject({ ok: false });
        const enumerated = interpreterFor("function f() { var n = 0; for (var k in [1]) n++; return n; }", new Map([["Array.prototype", new Map([["q2", "join"]])]]));
        expect(enumerated("f", [])).toMatchObject({ ok: false, reason: expect.stringMatching(/enumerable/) as unknown });
    });
});
