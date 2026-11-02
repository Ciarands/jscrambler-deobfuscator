import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { createLogger } from "../src/logger.js";
import { observe, type Run } from "./helpers.js";

const run = async (program: string): Promise<{ code: string; lines: string[] }> => {
    const lines: string[] = [];
    const { code } = await deobfuscate(program, { logger: createLogger("debug", (line) => lines.push(line)) });
    return { code, lines };
};

const refusals = (lines: readonly string[]): string[] => lines.filter((line) => line.includes("[runtime]") && line.includes("not taken"));

const STORAGE = `
function G() {}
G[3] = (function () { return globalThis; })();
`;

/** Model 10: the page has the host objects the script uses. */
const PAGE: Run = { globals: () => ({ hostDoc: { title: "page" } }), timers: true };

describe("getters: a later call may answer otherwise", () => {
    it("refuses a call alias whose function counts its calls and lies after the probes (review round 2, B3)", async () => {
        const program = `${STORAGE}
function S(g) {
  var n = 0;
  Object.defineProperty(G, "c1", { get: function () { return function () {
    if (arguments.length === 0) return String.fromCharCode;
    n++;
    return n > 10 ? "LIED" : String.fromCharCode.apply(String, arguments);
  }; }, configurable: true });
}
S(G[3]);
var out = [];
for (var i = 0; i < 12; i++) out.push(G.c1(72));
result = out;
`;
        const { code, lines } = await run(program);
        expect(code).toContain("G.c1(72)");
        expect(refusals(lines).some((line) => line.includes("call alias G.c1") && line.includes("n "))).toBe(true);
        expect(observe(code)).toBe(observe(program));
        expect(observe(code)).toContain("LIED");
    });

    it("refuses an alias whose getter reads a variable other code writes later", async () => {
        const program = `${STORAGE}
function S(g) {
  var name = "fromCharCode";
  Object.defineProperty(String, "q2Fcc", { get: function () { return String[name]; }, configurable: true });
  Object.defineProperty(G, "retarget", { get: function () { name = "raw"; return 0; }, configurable: true });
}
S(G[3]);
var before = String.q2Fcc === String.fromCharCode;
G.retarget;
result = [before, String.q2Fcc === String.fromCharCode, String.q2Fcc === String.raw];
`;
        const { code, lines } = await run(program);
        expect(code).toContain("String.q2Fcc");
        expect(refusals(lines).some((line) => line.includes("alias String.q2Fcc") && line.includes("name is written by code that may run later"))).toBe(true);
        expect(observe(code)).toBe(observe(program));
    });

    it("refuses an alias whose getter answers by its receiver", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(String.prototype, "q3Spl", { get: function () { return this.length > 3 ? String.prototype.slice : String.prototype.split; }, configurable: true });
}
S(G[3]);
result = ["a,b".q3Spl(","), "ab,cd".q3Spl(",")];
`;
        const { code, lines } = await run(program);
        expect(code).toContain(`"ab,cd".q3Spl(",")`);
        expect(refusals(lines).some((line) => line.includes("alias String.prototype.q3Spl") && line.includes("its receiver"))).toBe(true);
        expect(observe(code)).toBe(observe(program));
    });

    it("refuses a host alias whose getter keeps a count", async () => {
        const program = `${STORAGE}
(function (g) {
  var n = 0;
  Object.defineProperty(g, "q6Hd", { get: function () { n++; return n > 3 ? undefined : typeof g.hostDoc == "undefined" ? undefined : g.hostDoc; }, set: function (v) { g.hostDoc = v; }, configurable: true });
})(G[3]);
setTimeout(function () { result = [q6Hd, q6Hd, q6Hd, q6Hd, q6Hd]; });
`;
        const { code, lines } = await run(program);
        expect(code).toContain("q6Hd");
        expect(refusals(lines).some((line) => line.includes("host alias q6Hd"))).toBe(true);
        expect(observe(code, PAGE)).toBe(observe(program, PAGE));
    });

    it("refuses a getter the setup can't be told about (a loop it doesn't follow)", async () => {
        const program = `${STORAGE}
function S(g) {
  var names = ["fromCharCode"], picked;
  for (var i = 0; i < names.length; i++) picked = names[i];
  Object.defineProperty(String, "q2Fcc", { get: function () { return String[picked]; }, configurable: true });
}
S(G[3]);
result = [String.q2Fcc(72)];
`;
        const { code, lines } = await run(program);
        expect(code).toContain("String.q2Fcc(72)");
        expect(refusals(lines).some((line) => line.includes("ForStatement"))).toBe(true);
        expect(observe(code)).toBe(observe(program));
    });

    it("refuses a getter that may throw, and a setup that calls a builtin it doesn't model", async () => {
        const cases = [
            {
                setup: 'Object.defineProperty(String, "q2Fcc", { get: function () { if (typeof g.flag == "undefined") throw 0; return String.fromCharCode; }, configurable: true }); g.flag = 1;',
                reason: "may throw",
            },
            {
                setup: 'var key = "q2" + String.fromCharCode(70) + "cc"; Object.defineProperty(String, key, { get: function () { return String.fromCharCode; }, configurable: true });',
                reason: "doesn't model",
            },
        ];
        for (const { setup, reason } of cases) {
            const program = `${STORAGE}
function S(g) { ${setup} }
S(G[3]);
result = [String.q2Fcc(72)];
`;
            const { code, lines } = await run(program);
            expect(code).toContain("String.q2Fcc(72)");
            expect(refusals(lines).some((line) => line.includes(reason))).toBe(true);
            expect(observe(code)).toBe(observe(program));
        }
    });
});

// The obfuscator's setup shape: a local array holding `arguments` and the frame's values, a `try`, a descriptor whose
// getter compares the type with a string it builds, and a dispatcher for calls.
const TEMPLATE = `${STORAGE}
function S(g) {
  function def(m0, m1, m2, m3, m4, m5) {
    var s = [arguments];
    s[5] = "";
    s[5] = "Property";
    s[1] = {};
    try {
      s[6] = (1, s[0][1])(s[0][0]);
      s[9] = [s[6], s[6].prototype][s[0][3]];
      s[8] = s[0][5] === k[7] ? G : s[9];
      if (s[9].hasOwnProperty(s[0][4]) && s[9][s[0][4]] === s[9][s[0][2]]) return;
      if (s[0][5] !== k[7]) s[9][s[0][4]] = s[9][s[0][2]];
      s[1].set = function (v) { var a = [arguments]; s[9][s[0][2]] = a[0][0]; };
      s[1].get = function () {
        var t = [arguments];
        t[1] = "un";
        t[1] += "defined";
        if (s[0][5] === k[7]) {
          return function () {
            var u = [arguments];
            u[1] = null;
            if (arguments.length > k[7]) {
              if (s[0][3] === k[7]) return s[9][s[0][2]].apply(s[6], arguments);
              u[5] = arguments[k[7]] === u[1] || arguments[k[7]] === undefined ? s[6] : arguments[k[7]];
              return u[5][s[0][2]].apply(u[5], Array.prototype.slice.call(arguments, k[8]));
            }
            return s[9][s[0][2]];
          };
        }
        if (typeof s[9][s[0][2]] == t[1]) return undefined;
        return s[9][s[0][2]];
      };
      s[1].enumerable = false;
      try {
        s[0][0].Object["define" + s[5]](s[8], s[0][4], s[1]);
      } catch (e) {}
    } catch (e2) {}
  }
  function own(x) { var p = [arguments]; return p[0][0]; }
  function str(x) { var p = [arguments]; return p[0][0].String; }
  var k = [arguments];
  k[7] = 0;
  k[8] = 1;
  def(k[0][0], str, "fromCharCode", 0, "c1", k[7]);
  def(k[0][0], str, "split", 1, "c2", k[7]);
  def(k[0][0], str, "fromCharCode", 0, "q2Fcc");
  def(k[0][0], own, "hostDoc", 0, "q6" + "Hd");
  def(k[0][0], own, "__probe", 0, "c3", k[7]);
}
S(G[3]);
`;

describe("getters: the setup's own shape", () => {
    it("proves its call aliases, aliases and host aliases, and rewrites them", async () => {
        const program = `${TEMPLATE}
setTimeout(function () { result = [G.c1(72, 105), G.c2("a,b", ",").length, String.q2Fcc(65), q6Hd.title, typeof q6Hd]; });
`;
        const { code, lines } = await run(program);
        expect(refusals(lines)).toEqual([]);
        expect(lines.some((line) => line.includes("[runtime] global read G.c3() = globalThis.__probe"))).toBe(true);
        expect(code).toContain("String.fromCharCode(72, 105)");
        expect(code).toContain(`"a,b".split(",").length`);
        expect(code).toContain("String.fromCharCode(65)");
        expect(code).toContain("hostDoc.title");
        expect(code).not.toContain("q6Hd");
        expect(observe(code, PAGE)).toBe(observe(program, PAGE));
    });

    it("refuses them all once a frame value the getters read is written by code that runs later", async () => {
        const program = `${TEMPLATE.replace("k[8] = 1;", 'k[8] = 1;\n  Object.defineProperty(G, "bump", { get: function () { k[7] = 1; return 0; }, configurable: true });')}
setTimeout(function () { var before = [G.c1(72), String.q2Fcc === String.fromCharCode]; G.bump; result = [before, G.c1(72), String.q2Fcc === String.fromCharCode]; });
`;
        const { code, lines } = await run(program);
        expect(code).toContain("G.c1(72)");
        expect(code).toContain("String.q2Fcc");
        expect(refusals(lines).some((line) => line.includes("k is handed on, or its slots are written by code that may run later"))).toBe(true);
        expect(observe(code, PAGE)).toBe(observe(program, PAGE));
    });
});

describe("getters: while the setup runs, and its this", () => {
    it("refuses a setup that reads an alias it installed before it finishes (the getter would answer from a frame still running)", async () => {
        const program = `${STORAGE}
function S(g) {
  var name = "raw";
  Object.defineProperty(String, "q2Fcc", { get: function () { return String[name]; }, configurable: true });
  var early = String.q2Fcc === String.raw;
  name = "fromCharCode";
  Object.defineProperty(G, "early", { get: function () { return early; }, configurable: true });
}
S(G[3]);
result = [G.early, String.q2Fcc === String.fromCharCode];
`;
        const { code, lines } = await run(program);
        expect(code).toContain("String.q2Fcc === String.raw");
        expect(refusals(lines).some((line) => line.includes("not taken as a setup call") && line.includes("an accessor would run before the setup finishes"))).toBe(true);
        expect(observe(code)).toBe(observe(program));
    });

    it("takes a setup key's call as using the storage object as this when its function reads this", async () => {
        const program = `
function G() {}
G.v = 1;
G.w = 1;
function S() { Object.defineProperty(G, "m", { get: function () { return function () { Object.defineProperty(this, "v", { value: 2 }); return 0; }; }, configurable: true }); }
S();
setTimeout(function () { G.m(); result = [G.v === G.w]; });
`;
        const { code, lines } = await run(program);
        expect(lines.some((line) => line.includes("G.m(...) may use G as this: the function its getter hands out reads this"))).toBe(true);
        expect(code).toContain("G.v === G.w");
        expect(observe(code, { timers: true })).toBe(observe(program, { timers: true }));
    });

    it("takes the setup's own call aliases as not using the storage object as this", async () => {
        const { lines } = await run(`${TEMPLATE}\nresult = [G.c1(72)];\n`);
        expect(lines.some((line) => line.includes("may use G as this"))).toBe(false);
    });
});

describe("getters: the setup told without running it", () => {
    it("takes a slot as the global object only where its function provably returns it", async () => {
        const read = "\nfunction read() { return typeof G[3].Math; }\nsetTimeout(function () { result = read(); });\n";
        const proven = `${STORAGE}${read}`;
        expect((await run(proven)).code).toContain("return typeof globalThis.Math;");
        for (const slot of ["G[3] = (function () { return Math.random() > 2 ? globalThis : { Math: 1 }; })();", "G[3] = (function () { return globalThis; })();\nG[3] = { Math: 1 };"]) {
            const program = `function G() {}\n${slot}${read}`;
            const { code } = await run(program);
            expect(code).toContain("G[3].Math");
            expect(observe(code, { timers: true })).toBe(observe(program, { timers: true }));
        }
    });

    it("takes a setup's argument as the global object only where nothing between may change the slot", async () => {
        const program = `${STORAGE}
G[4] = (function () { G[3] = { String: { fromCharCode: function () { return "x"; } } }; return 1; })();
function S(g) { Object.defineProperty(String, "q2Fcc", { get: function () { return g.String.fromCharCode; }, configurable: true }); }
S(G[3]);
result = [String.q2Fcc(72), G[4]];
`;
        const { code, lines } = await run(program);
        expect(code).toContain("String.q2Fcc(72)");
        expect(lines.some((line) => line.includes("G.3 may change before the call"))).toBe(true);
        expect(observe(code)).toBe(observe(program));
    });

    it("keeps a setup that leaves a plain value on G while code reads it, and logs what each setup call defines", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(G, "w", { value: 5, configurable: true });
  Object.defineProperty(String, "q2Fcc", { get: function () { return String.fromCharCode; }, configurable: true });
}
S(G[3]);
result = [G.w, String.q2Fcc(72)];
`;
        const { code, lines } = await run(program);
        expect(observe(code)).toBe(observe(program));
        expect(code).toContain("G.w");
        expect(lines.some((line) => line.includes("setup call: defines G.w, String.q2Fcc"))).toBe(true);
    });

    it("tells setInterval from setTimeout (the host's functions are each their own)", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(g, "q8Si", { get: function () { return g.setInterval; }, configurable: true });
  Object.defineProperty(g, "q8St", { get: function () { return g.setTimeout; }, configurable: true });
}
S(G[3]);
result = [q8Si === setInterval, q8St === setTimeout];
`;
        const { code } = await run(program);
        expect(code).toContain("setInterval === setInterval");
        expect(code).toContain("setTimeout === setTimeout");
    });

    it("rewrites a method call alias that goes on for a missing receiver only where the receiver is there", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(G, "ap", { get: function () { return function () {
    var a = Array.prototype.slice.call(arguments);
    if (a.length === 0) return Function.prototype.apply;
    var r = a[0] === null || a[0] === undefined ? Function : a[0];
    return r.apply.apply(r, a.slice(1));
  }; }, configurable: true });
}
S(G[3]);
var f = null;
var made = G.ap(f, null, ["return 7"]);
result = [G.ap(Math.max, null, [1, 5]), made()];
`;
        const { code, lines } = await run(program);
        expect(lines.some((line) => line.includes("call alias G.ap(...) = x.apply(...) where x is neither null nor undefined"))).toBe(true);
        expect(code).toContain("Math.max.apply(null, [1, 5])");
        expect(code).toContain("G.ap(f, null,");
        expect(observe(code)).toBe(observe(program));
    });

    it("takes a static call alias of a builtin that is no function as throwing a TypeError like it", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(G, "m5", { get: function () { return function () {
    if (arguments.length > 0) return Math.apply(g, arguments);
    return Math;
  }; }, configurable: true });
}
S(G[3]);
var caught;
try { G.m5(1); } catch (e) { caught = e instanceof TypeError; }
result = [G.m5() === Math, caught];
`;
        const { code } = await run(program);
        expect(code).toContain("Math(1)");
        expect(code).toContain("Math === Math");
        expect(observe(code)).toBe(observe(program));
    });

    it("follows rest parameters and spreads in the function a getter hands out", async () => {
        const program = `${STORAGE}
function S(g) {
  Object.defineProperty(G, "sp", { get: function () { return (...a) => {
    if (a.length > 0) return (a[0] === null || a[0] === undefined ? String : a[0]).split(...a.slice(1));
    return String.prototype.split;
  }; }, configurable: true });
}
S(G[3]);
result = [G.sp("a,b", ",").length];
`;
        const { code } = await run(program);
        expect(code).toContain(`"a,b".split(",").length`);
        expect(observe(code)).toBe(observe(program));
    });

    it("refuses an alias a setup may not install: a defineProperty that may throw, a check of another name", async () => {
        const twice = `${STORAGE}
function S(g) {
  Object.defineProperty(String, "q2Fcc", { get: function () { return String.fromCharCode; } });
  try { Object.defineProperty(String, "q2Fcc", { get: function () { return String.raw; } }); } catch (e) {}
}
S(G[3]);
result = [String.q2Fcc === String.fromCharCode];
`;
        const first = await run(twice);
        expect(first.code).toContain("String.q2Fcc === String.fromCharCode");
        expect(first.lines.some((line) => line.includes("alias String.q2Fcc: not taken"))).toBe(true);
        expect(observe(first.code)).toBe(observe(twice));

        // The page may have the global the setup checks: then it installs nothing.
        const other = `${STORAGE}
function S(g) {
  if (g.hasOwnProperty("pageFlag")) return;
  Object.defineProperty(g, "q1Str", { get: function () { return g.String; }, configurable: true });
}
S(G[3]);
result = [typeof q1Str];
`;
        const second = await run(other);
        expect(second.code).toContain("typeof q1Str");
        const page: Run = { globals: () => ({ pageFlag: 1 }) };
        expect(observe(second.code, page)).toBe(observe(other, page));
    });
});
