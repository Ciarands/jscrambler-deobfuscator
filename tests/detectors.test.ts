import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

/** Runs in a healthy, undebugged page: no `require`/`process`, native `Date.now`, a `navigator`. */
const RUN: Run = { globals: () => ({ navigator: { userAgent: "test" } }), timers: true };

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["runtime", "detectors", "simplify", "cleanup"] })).code;

const sameBehaviour = async (program: string): Promise<string> => {
    const output = await run(program);
    expect(observe(output, RUN)).toBe(observe(program, RUN));
    return output;
};

// j-016 detectors: each a builder whose method answers from a report its slow path sets on detection.
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

const WITH_FEATURE: Run = { globals: () => ({ FEATURE: true }), timers: true };

describe("detectors", () => {
    it("answers every detector call, directly and through a wrapper", async () => {
        const program = `${DETECTORS}if (G.w()) { log.push("start"); }
setTimeout(function () {
  if (!G.N.d()) { log.push("n"); }
  if (G.F.d() && !G.H.d()) { log.push("fh"); }
  if (G.w()) { log.push("t"); }
  result = [log, G.N.d(), G.F.d(), G.H.d(), G.w(), typeof G.T.d()];
});
`;
        const output = await sameBehaviour(program);
        // G.T's builder reads navigator, which its static proof doesn't need: its calls are answered too.
        expect(output).not.toMatch(/G\.([NFHT]\.d|w)\(\)/);
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
        // A prelude call before the builder runs before the detector exists.
        const early = DETECTORS.replace("G.T = function", 'try { var early = G.T.d(); } catch (e) { early = "threw"; }\nG.T = function');
        const output = await sameBehaviour(`${early}setTimeout(function () { result = [early, G.T.d()]; });\n`);
        expect(output).toContain("var early = G.T.d();");
    });

    it("leaves lazy initializers and checks that set their report on the healthy path", async () => {
        const unfinished = "\n  S[1] = navigator.userAgent;";
        const shapes = [
            lazy('S[4] = "ready";', unfinished), // set unconditionally: an initialization
            lazy("S[4] = [1, 2].join();", unfinished), // a computed value
            lazy("S[4] = Date.now() > 0;", unfinished), // a check's outcome, with no debugger sign
            lazy('if (Date.now() > 0) { S[4] = "j-016-00001"; }', "\n  S[4] = 7;"), // started as a report
        ];
        for (const program of shapes) {
            const output = await sameBehaviour(program);
            expect(output).toContain("G.L.d()");
        }
    });

    it("answers a check that stores a detection code, whatever it tests (model 5)", async () => {
        // The code is the debugger sign: model 5 takes such a check not to fire undebugged, and this one, which does
        // fire, is answered all the same.
        const output = await run(lazy('if (Date.now() > 0) { S[4] = "j-016-00001"; }'));
        expect(output).not.toContain("G.L.d()");
        expect(output).toContain('"unset"');
    });

    it("leaves a lazy feature probe: nothing in it checks for a debugger", async () => {
        const program = lazy("if (globalThis.FEATURE) { S[4] = 1; }");
        const output = await sameBehaviour(program);
        expect(output).toContain("G.L.d()");
        expect(observe(output, WITH_FEATURE)).toBe(observe(program, WITH_FEATURE));
    });

    it("leaves a feature probe that shares its builder with a detector", async () => {
        // Only the detector's own code shows a debugger sign; the probe can't borrow it from their builder.
        const program = `
function G() {}
G.L = function () {
  var S = [arguments];
  return {
    d: function () { var X = [arguments]; if (!S[4]) { P(); } return S[4]; },
    e: function () { var X = [arguments]; if (!S[6]) { Q(); } return S[6]; }
  };
  function P() { if (typeof require === "function" && require("inspector").url()) { S[4] = "j-016-00033"; } }
  function Q() { if (globalThis.FEATURE) { S[6] = true; } }
}();
setTimeout(function () { result = [G.L.d() ? "set" : "unset", G.L.e() ? "on" : "off"]; });
`;
        const output = await sameBehaviour(program);
        expect(output).toContain("G.L.e()");
        expect(output).not.toContain("G.L.d()");
        expect(observe(output, WITH_FEATURE)).toBe(observe(program, WITH_FEATURE));
    });

    it("keeps a detector's builder that calls something outside it while it runs", async () => {
        for (const start of ["\n  bump();", "\n  var b = bump;\n  b();", "\n  S[7] = bump;\n  (1, S[7])();"]) {
            const program = lazy('if (typeof require === "function" && require("inspector").url()) { S[4] = "j-016-00015"; }', start)
                .replace("function G() {}", "function G() {}\nvar count = 0;\nfunction bump() { count++; }")
                .replace('result = [G.L.d() ? "set" : "unset"];', 'result = [G.L.d() ? "set" : "unset", count];');
            const output = await sameBehaviour(program);
            expect(observe(output, RUN), start).toContain(",1]");
        }
    });

    it("answers a detector whose report write is computed, behind a debugger sign in its own code (model 5)", async () => {
        // A timing check around opening an inspector: undebugged it reports nothing, whatever its write computes.
        const program = lazy('var t = Date.now(); if (typeof require === "function") { require("inspector").url(); } S[4] = Date.now() - t > 100;');
        const output = await sameBehaviour(program);
        expect(output).not.toContain("G.L.d()");
        expect(output).toContain('"unset"');
    });

    it("keeps a computed report write when only a sibling method shows a debugger sign", async () => {
        const program = `
function G() {}
G.L = function () {
  var S = [arguments];
  return {
    d: function () { var X = [arguments]; if (!S[4]) { P(); } return S[4]; },
    e: function () { var X = [arguments]; if (!S[6]) { Q(); } return S[6]; }
  };
  function P() { var t = Date.now(); S[4] = Date.now() - t > 100; }
  function Q() { if (typeof require === "function" && require("inspector").url()) { S[6] = "j-016-00001"; } }
}();
setTimeout(function () { result = [G.L.d() ? "set" : "unset", G.L.e() ? "on" : "off"]; });
`;
        const output = await sameBehaviour(program);
        expect(output).toContain("G.L.d()");
        expect(output).not.toContain("G.L.e()");
    });
});
