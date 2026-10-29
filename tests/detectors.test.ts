import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

/**
 * What a script leaves in `result` in a healthy page that isn't being debugged: no `require` or `process`, a native
 * `Date.now`, a `navigator`. `setTimeout` callbacks (code after the prelude) run once it has finished.
 */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback), navigator: { userAgent: "test" } };
    runInNewContext(source, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "detectors", "simplify", "cleanup"] })).code;

/** The program and its deobfuscation leave the same result; returns the deobfuscation. */
const sameBehaviour = async (program: string): Promise<string> => {
    const output = await run(program);
    expect(observed(output)).toBe(observed(program));
    return output;
};

// jscrambler's j-016 detectors, each a builder whose method answers from a report its slow path sets on detection.
const DETECTORS = `
function G() {}
var log = [];
G.N = function () {
  var S = [arguments];
  S[2] = "inspector";
  return {
    d: function () {
      var X = [arguments];
      if (S[5] === undefined) { try { P(); } catch (e) {} }
      return S[5];
    }
  };
  function P() {
    if (typeof require !== "function") { return; }
    var i = require(S[2]);
    if (i.url() !== undefined) { S[5] = "j-016-00015"; }
  }
}();
G.F = function () {
  var S = [arguments];
  return {
    d: function () {
      var X = [arguments];
      if (S[9] === undefined) { try { f(); } catch (e) { S[9] = false; } }
      return !S[9];
    }
  };
  function f() { S[9] = process.execArgv.some(function (a) { return a.startsWith("--inspect"); }) || (process.env.NODE_OPTIONS || "").indexOf("--inspect") !== -1; }
}();
G.H = function () {
  var S = [arguments];
  S[8] = 0;
  return {
    d: function () {
      var X = [arguments];
      if (!S[8]) { W(); }
      return !!S[8];
    }
  };
  function W() { var r = /x/; r.toString = function () { S[8] = 1; }; }
}();
G.T = function () {
  var K = [arguments];
  K[3] = 0;
  K[4] = navigator.userAgent.length < 0;
  K[7] = {
    d: function () {
      var W = [arguments];
      W[4] = function (k) {
        var A = [arguments];
        if (A[0][0]) { K[3] = "j-016-00083"; }
        if (K[4]) { K[3] = "j-016-00085"; }
        return !K[3];
      };
      W[7] = Date.now.bind(Date);
      W[1] = "prototype" in Date.now;
      return function () {
        var t = [arguments];
        if (W[1]) { W[9] = (1, W[4])(W[1]); } else { t[2] = (1, W[7])(); if (!W[5] || t[2] - W[5] > 1500) { W[5] = t[2]; W[9] = (1, W[4])(); } }
        return W[9];
      };
    }()
  };
  return K[7];
}();
G.w = function () { return typeof G.T.d === "function" ? G.T.d.apply(G.T, arguments) : G.T.d; };
`;

/** A lazy check shaped like a detector: `probe` is its slow path, `start` more of its builder. */
const lazy = (probe: string, start = "") => `
function G() {}
G.L = function () {
  var S = [arguments];${start}
  return { d: function () { var X = [arguments]; if (!S[4]) { P(); } return S[4]; } };
  function P() { ${probe} }
}();
setTimeout(function () { result = [G.L.d() ? "set" : "unset"]; });
`;

/** Like `observed`, on a page that has `FEATURE`. */
const withFeature = (code: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback), FEATURE: true };
    runInNewContext(code, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

describe("detectors", () => {
    it("answers every detector call, the prelude's included, and drops the detectors", async () => {
        // G.T's builder reads navigator, which the guest lacks: its answer comes from its code alone.
        const program = `${DETECTORS}if (G.w()) { log.push("start"); }
setTimeout(function () {
  if (!G.N.d()) { log.push("n"); }
  if (G.F.d() && !G.H.d()) { log.push("fh"); }
  if (G.w()) { log.push("t"); }
  result = [log, G.N.d(), G.F.d(), G.H.d(), G.w(), typeof G.T.d()];
});
`;
        const output = await sameBehaviour(program);
        expect(output).not.toMatch(/\.d\(\)|G\.w\(\)/);
        expect(output).not.toContain("j-016");
        expect(output).toContain('result = [log, undefined, true, false, true, "boolean"];');
    });

    it("answers only the truthiness of a report whose detections aren't all literal codes", async () => {
        // The answer is `false` here, but undebugged the probe may as well leave `undefined`: only tests are answered.
        const detector = `
function G() {}
G.V = function () {
  var S = [arguments];
  return {
    d: function () {
      var X = [arguments];
      if (S[9] === undefined) { try { f(); } catch (e) { S[9] = false; } }
      return S[9];
    }
  };
  function f() { S[9] = process.execArgv.some(function (a) { return a.startsWith("--debug"); }) || (process.env.NODE_OPTIONS || "").indexOf("--debug") !== -1; }
}();
`;
        const output = await sameBehaviour(`${detector}setTimeout(function () { var x = G.V.d() ? 1 : 2; result = [x, G.V.d()]; });\n`);
        expect(output).toContain("result = [2, G.V.d()];");
    });

    it("keeps calls that may reach something else than the detector", async () => {
        const cases = [
            "G.N = { d: function () { return 5; } };", // the holder replaced after the prelude
            'var k = "N"; G[k] = { d: function () { return 5; } };', // through a computed key
        ];
        for (const replace of cases) {
            const program = `${DETECTORS}setTimeout(function () { ${replace} result = [G.N.d()]; });\n`;
            const output = await sameBehaviour(program);
            expect(output).toContain("result = [G.N.d()];");
        }
        // A prelude call before the builder (the guest didn't finish it) runs before the detector exists.
        const early = DETECTORS.replace("G.T = function", 'try { var early = G.T.d(); } catch (e) { early = "threw"; }\nG.T = function');
        const output = await sameBehaviour(`${early}setTimeout(function () { result = [early, G.T.d()]; });\n`);
        expect(output).toContain("var early = G.T.d();");
    });

    it("leaves lazy initializers and checks that set their report on the healthy path", async () => {
        // A builder reading navigator, which the guest lacks: only its code speaks for it.
        const unfinished = "\n  S[1] = navigator.userAgent;";
        const shapes = [
            lazy('S[4] = "ready";', unfinished), // set unconditionally: an initialization
            lazy("S[4] = [1, 2].join();", unfinished), // a computed value
            lazy("S[4] = Date.now() > 0;", unfinished), // a check's outcome the guest can't confirm is no detection code
            lazy('if (Date.now() > 0) { S[4] = "j-016-00001"; }'), // a check that fires in the guest, which isn't debugged
            lazy('if (Date.now() > 0) { S[4] = "j-016-00001"; }', "\n  S[4] = 7;"), // started as a report
        ];
        for (const program of shapes) {
            const output = await sameBehaviour(program);
            expect(output).toContain("G.L.d()");
        }
    });

    it("leaves a lazy feature probe: nothing in it checks for a debugger", async () => {
        // The guest lacks FEATURE, so it would answer undefined; a page with it gets 1.
        const program = lazy("if (globalThis.FEATURE) { S[4] = 1; }");
        const output = await sameBehaviour(program);
        expect(output).toContain("G.L.d()");
        expect(withFeature(output)).toBe(withFeature(program));
    });

    it("keeps a detector's builder that calls something outside it while it runs", async () => {
        // Directly, through a local holding it, and through a slot of the builder's array holding it.
        for (const start of ["\n  bump();", "\n  var b = bump;\n  b();", "\n  S[7] = bump;\n  (1, S[7])();"]) {
            const program = lazy('if (typeof require === "function" && require("inspector").url()) { S[4] = "j-016-00015"; }', start)
                .replace("function G() {}", "function G() {}\nvar count = 0;\nfunction bump() { count++; }")
                .replace('result = [G.L.d() ? "set" : "unset"];', 'result = [G.L.d() ? "set" : "unset", count];');
            const output = await sameBehaviour(program);
            expect(observed(output), start).toContain(",1]");
        }
    });
});
