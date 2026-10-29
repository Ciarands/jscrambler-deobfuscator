import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

// A stateful decoder that isn't jscrambler's template: a stage call (made by the prelude) reshuffles its table, and
// later calls read it. Nothing proves those calls free of effects.
const PROGRAM = `
function G() {}
G.D = (function () {
  var table = ["c", "b", "a"], stage = 0;
  return {
    get: function (i) {
      if (stage === 0 && i === 7) { table.reverse(); stage = 1; return 1; }
      stage = 2;
      return table[i];
    },
    num: function () { return 42; }
  };
})();
G.w = function () { return typeof G.D.get === "function" ? G.D.get.apply(G.D, arguments) : G.D.get; };
G.n = function () { return typeof G.D.num === "function" ? G.D.num.apply(G.D, arguments) : G.D.num; };
var flag = G.w(7) === 1;
var out = [];
function f(k) {
  var i = 0;
  out.push(G.w(i), G.w(1), G.w(k), G.n());
}
f(host.k);
out.push(flag);
result = out;
`;

/** What a script leaves in `result`; `setTimeout` callbacks (code after the prelude) run once it has finished. */
const run = (code: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { host: { k: 2 }, setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(code, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

// jscrambler's string decoder: stage calls shuffle the table T; once its counter R is past every stage guard, it is a
// lookup, and the first call matching no stage freezes it (G.D.m becomes the lookup L).
const decoder = ({ lookup = "return T[y];", setup = "", stages = "R += 1;" } = {}) => `
function G() {}
var hits = 0;
G.D = (function () {
  var Q = {
    m: (function (key) {
      var T = "";
      T += "a,b,c,d,e,f";
      T = T.split(",");${setup}
      var R = 0;
      var S = function (x) {
        if (R === 0 && x === 2) { ${stages} T.unshift.apply(T, T.splice(-2, 2).splice(0, 1)); }
        else if (R === 1 && x === 4) { ${stages} T.unshift.apply(T, T.splice(-3, 3).splice(0, 2)); }
        else { Q.m = L; return L(x); }
        return R;
      };
      var L = function (y) { ${lookup} };
      return S;
    })("k")
  };
  return Q;
})();
G.w = function () { return typeof G.D.m === "function" ? G.D.m.apply(G.D, arguments) : G.D.m; };
G.v = function () { return typeof G.D.m === "function" ? G.D.m.apply(G.D, arguments) : G.D.m; };
`;
const deobfuscated = async (program: string): Promise<string> => (await deobfuscate(program, { passes: ["emulate", "resolve-calls"] })).code;
const prelude = "var flag = G.w(2) === 1 && G.v(4) === 2;\nvar first = G.w(1);\n";
// What a run sees, including whether the decoder still froze (G.D.m is L) and the table's order at runtime.
const later = "setTimeout(function () { result = [flag, first, second, G.w(host.k), G.v(5), G.D.m.name, hits]; });\n";

describe("resolve-calls", () => {
    it("resolves later calls of a settled decoder with constant arguments", async () => {
        const program = `${decoder()}${prelude}var second = G.v(0);\nfunction f(k) { var i = 0; result = [flag, first, second, G.w(i), G.v(3), G.w(k)]; }\nsetTimeout(function () { f(host.k); });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        // `i` is a constant binding; `k` isn't known.
        expect(code).toMatch(/result = \[flag, first, second, "[a-f]", "[a-f]", G\.w\(k\)\]/);
    });

    it("resolves a call whose argument runs something before its constant, keeping that first", async () => {
        // Some builds pass a calculator's selector call ahead of the index: `G.w((G.sel(1), 3))`.
        const program = `${decoder()}${prelude}var second = 0;\nG.sel = function (n) { hits += n; };\nsetTimeout(function () { result = [G.w((G.sel(5), 3)), hits]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toMatch(/result = \[\(G\.sel\(5\), "[a-f]"\), hits\]/);
    });

    it("resolves direct calls of a settled decoder's target after the prelude", async () => {
        // What wrappers makes of wrapper calls: `G.D.m(3)`. Direct stage calls in the prelude stay (the simplify-group test at the end).
        const program = `${decoder()}${prelude}var second = 0;\nsetTimeout(function () { result = [first, G.D.m(3), G.D.m(host.k)]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toMatch(/result = \[first, "[a-f]", G\.D\.m\(host\.k\)\]/);
    });

    it("resolves direct calls of the target in prelude statements after the one that settled the decoder", async () => {
        const program = `${decoder()}${prelude}var direct = G.D.m(3);\nsetTimeout(function () { result = [flag, first, direct, G.D.m.name]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toMatch(/var direct = "[a-f]";/);
    });

    it("keeps direct calls of the target that run before the decoder settled: they may be stage calls", async () => {
        // `G.D.m(2)` is the first stage; `G.v(4)` the second, which settles it: before it, or in its statement.
        const tail = "var first = G.w(1);\nvar direct = G.D.m(3);\nsetTimeout(function () { result = [flag, first, direct]; });\n";
        for (const start of ["G.D.m(2);\nvar flag = G.v(4) === 2;\n", "var flag = G.D.m(2) === 1 && G.v(4) === 2;\n"]) {
            const program = `${decoder()}${start}${tail}`;
            const code = await deobfuscated(program);
            expect(run(code)).toBe(run(program));
            expect(code).toContain("G.D.m(2)");
        }
    });

    it("keeps later calls of targets not proven free of effects, whatever the sandbox answers", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["emulate", "resolve-calls"] });
        expect(code).toContain("var flag = (G.w(7), 1) === 1;");
        expect(code).toContain("out.push(G.w(i), G.w(1), G.w(k), G.n());");
        expect(run(code)).toBe(run(PROGRAM));
        // A settled decoder the prelude replaced afterwards: its replacement's calls give the same twice, and count.
        const replaced = `${decoder()}${prelude}G.D.m = function (y) { hits++; return "z"; };\nsetTimeout(function () { result = [G.v(5), G.v(5), hits]; });\n`;
        const output = await deobfuscated(replaced);
        expect(run(output)).toBe(run(replaced));
        expect(output).toContain("result = [G.v(5), G.v(5), hits];");
    });

    it("keeps calls of a decoder written after the prelude, also through a local holding part of G", async () => {
        const program = `${decoder()}${prelude}var d = G.D;\nsetTimeout(function () { d.m = function () { return "swapped"; }; });\nsetTimeout(function () { result = G.v(0); });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("result = G.v(0);");
    });

    it("records no results after a runtime statement fails partway: the guest may no longer match a real run", async () => {
        // The guest lacks `host`: `G.k = ...` throws after `G.s` is set, where a real run sets `G.k` to 2.
        const program = `function G() {}
G.D = { m: function () { return "v" + G.s + G.k; } };
G.w = function () { return typeof G.D.m === "function" ? G.D.m.apply(G.D, arguments) : G.D.m; };
G.k = (function () { G.s = 5; return host.k; })();
var v = G.w();
result = [v];
`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("var v = G.w();");
    });

    it("finds the storage object by its evidence, not by which object a root statement assigns first", async () => {
        const program = `var config = {};\nconfig.ready = true;\n${decoder()}${prelude}var second = G.v(0);\n${later}`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("var flag = (G.w(2), 1) === 1 && (G.v(4), 2) === 2;");
    });

    it("finds the runtime in a lone arrow IIFE after directives", async () => {
        const program = `"use client";\n(() => {\n${decoder()}${prelude}var second = G.v(0);\n${later}})();\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("var flag = (G.w(2), 1) === 1 && (G.v(4), 2) === 2;");
    });

    it("drops prelude calls made on a settled decoder, keeping its stage calls and the call that froze it", async () => {
        const program = `${decoder()}${prelude}var second = G.v(0);\n${later}`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("var flag = (G.w(2), 1) === 1 && (G.v(4), 2) === 2;");
        expect(code).toMatch(/var first = \(G\.w\(1\), "[a-f]"\);/);
        expect(code).toMatch(/var second = "[a-f]";/);
    });

    it("drops them also for `return R++` and a stage function the program got hold of", async () => {
        // R++ in the return: stage calls give R before the step. The escaped stage function can't run a stage again.
        const program = `${decoder({ stages: "" }).replace("return R;", "return R++;")}var f = G.D.m;\nvar flag = G.w(2) === 0 && G.v(4) === 1;\nvar first = G.w(1);\nvar second = G.v(0);\nsetTimeout(function () { result = [first, second, f(2), f(4), G.w(host.k), G.v(5), G.D.m.name]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toMatch(/var second = "[a-f]";/);
    });

    it("keeps prelude calls made before the decoder settled, when it froze early", async () => {
        // Frozen with a stage left: the escaped stage function still runs it (and shuffles the table).
        const program = `${decoder()}var f = G.D.m;\nvar flag = G.w(2) === 1;\nvar first = G.w(1);\nvar second = G.v(0);\nvar third = (f(4), G.v(0));\nsetTimeout(function () { result = [first, second, third, G.v(5), hits]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        expect(code).toMatch(/var second = \(G\.v\(0\), "[a-f]"\);/);
    });

    it("keeps prelude calls when the decoder doesn't follow the template", async () => {
        const shapes = [
            // The lookup does more than read the table.
            { lookup: "hits++; return T[y];" },
            // The table leaks out of the decoder: code holding it can change it.
            { setup: "\n      G.leak = function () { return T; };" },
        ];
        for (const shape of shapes) {
            const program = `${decoder(shape)}${prelude}var second = G.v(0);\n${later.replace("hits]", "hits, G.leak && G.leak().reverse(), G.v(5)]")}`;
            const code = await deobfuscated(program);
            expect(run(code)).toBe(run(program));
            expect(code).toMatch(/var second = \(G\.v\(0\), "[a-f]"\);/);
        }
    });

    it("keeps prelude calls that found another function or holder than the decoder's", async () => {
        const replacements = [
            // Another function at G.D.m: its calls can do anything.
            'G.D.m = function (y) { hits++; return "z"; };\n',
            // Another holder for the stage function: the freeze writes the old holder, which the guest doesn't watch.
            "var old;\n(function () { old = G.D; G.D = { m: old.m }; })();\n",
        ];
        for (const replacement of replacements) {
            const program = `${decoder()}var flag = G.w(2) === 1 && G.v(4) === 2;\n${replacement}var first = G.w(1);\nvar second = G.v(0);\nsetTimeout(function () { result = [first, second, G.w(host.k), G.D.m.name, typeof old === "object" && old.m.name, hits]; });\n`;
            const code = await deobfuscated(program);
            expect(run(code)).toBe(run(program));
            expect(code).toMatch(/var first = \(G\.w\(1\), "[a-z]"\);/);
        }
    });

    it("resolves sites of prelude calls it couldn't place only when each was a lookup on the settled decoder", async () => {
        // The calls inside `map` callbacks don't line up with call sites: the guest saw them, but not where they are.
        const program = `${decoder()}var flag = [2].map(function (i) { return G.w(i); })[0] === 1 && G.v(4) === 2;\nvar first = G.w(1);\nvar list = [3, 5].map(function (i) { return G.w(i); });\nsetTimeout(function () { result = [flag, first, list, G.w(3), G.w(2), G.v(4), G.w(host.k)]; });\n`;
        const code = await deobfuscated(program);
        expect(run(code)).toBe(run(program));
        // G.w(3) was made only as a lookup; G.w(2) and G.v(4) were stage calls: their sites may be those calls.
        expect(code).toMatch(/result = \[flag, first, list, "[a-f]", G\.w\(2\), G\.v\(4\), G\.w\(host\.k\)\]/);
        expect(code).toContain("=== 1 && G.v(4) === 2;");
    });

    it("resolves calls of a settled decoder whose arguments only become constant in the simplify group", async () => {
        // `s[1]` has two writes until the dead branch goes; then it is a constant (and wrappers left the call alone).
        const program = `${decoder()}${prelude}setTimeout(function () { var s = [arguments]; s[1] = 3; if (false) { s[1] = 4; } result = [flag, first, G.w(s[1]), G.w(host.k)]; });\n`;
        const { code } = await deobfuscate(program);
        expect(run(code)).toBe(run(program));
        // `flag` and `first` are constants too once the prelude's calls are split off their declarations.
        expect(code).toMatch(/result = \[true, "c", "[a-f]", G\.w\(host\.k\)\]/);
    });
});
