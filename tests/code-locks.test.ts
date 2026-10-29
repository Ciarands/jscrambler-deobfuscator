import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

/** What a script leaves in `result`; `setTimeout` callbacks (code after the prelude) run once it has finished. */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(source, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "code-locks"] })).code;

// jscrambler's shape: a builder returns an object whose method runs its checks once and then answers from a cache.
const lock = ({ extra = "", slowAnswer = 91, firstCall = "G.L.check();", setCache = "c[6] = 15;" } = {}) => `
function G() {}
var log = [];
G.L = function () {
  var c = [arguments];
  c[6] = undefined;
  c[3] = {};
  c[3].check = function () {
    var d = [arguments];
    if (c[6]) { return 67; }
    log.push("checked");
    ${setCache}
    return ${slowAnswer};
  };${extra}
  return c[3];
}();
${firstCall}
`;

const later = "setTimeout(function () { G.L.check(); result = [G.L.check(), log]; });\n";

describe("code-locks", () => {
    it("removes calls after the prelude's first one and answers used ones from the cache", async () => {
        const program = `${lock()}setTimeout(function () { G.L.check(); log.push(G.L.check()); result = log; });\n`;
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        // The prelude's call stays: it runs the checks.
        expect(output).toContain("}();\nG.L.check();");
        expect(output).toContain("log.push(67);");
        expect(output.match(/G\.L\.check\(\)/g)).toHaveLength(1);
    });

    it("keeps calls of a lock whose cache can be cleared", async () => {
        const program = `${lock({ extra: "\n  c[3].reset = function () { c[6] = undefined; };" })}setTimeout(function () { G.L.reset(); result = [G.L.check(), log]; });\n`;
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("result = [G.L.check(), log];");
    });

    it("keeps calls of a lock that doesn't answer from its cache after the prelude", async () => {
        // Never called by the prelude (its first answer, 67 here, may look cached), or never setting its cache.
        for (const shape of [{ firstCall: "" }, { firstCall: "", slowAnswer: 67 }, { setCache: "" }]) {
            const program = `${lock(shape)}${later}`;
            const output = await run(program);
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain("G.L.check();\n  result = [G.L.check(), log];");
        }
    });
});

const runWithCleanup = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "code-locks", "cleanup"] })).code;

// A lock whose checks touch only objects they create: a probe of a function's own source text, a typeof test, and a
// scoring loop that hangs when a check fails. `checks` adds statements to the slow path, `before` code before the
// builder, `prelude` code after it.
const localLock = ({ checks = "", before = "", prelude = "G.L.check();" } = {}) => `
function G() {}
var seen = false;
${before}
G.L = function () {
  var c = [arguments];
  c[6] = undefined;
  c[3] = {};
  c[3].check = function () {
    var d = [arguments];
    if (c[6]) { return 67; }
    d[1] = {};
    d[1].k = ["T"];
    d[1].f = function () { var p = function () { return "X".toLowerCase(); }; return /\\x58/.test(p + []); };
    d[2] = {};
    d[2].k = ["S"];
    d[2].f = function () { return typeof someMissingGlobal === "function"; };
    d[3] = [];
    d[3].push(d[1]);
    d[3].push(d[2]);
    d[4] = 0;
    d[5] = {};
    while (d[4] < d[3].length) {
      var e = d[3][d[4]];
      d[5][e.k[0]] = e.f() ? 1 : 0;
      d[4]++;
    }
    if (d[5].T !== 1 || d[5].S !== 0) { while (1) {} }
    ${checks}
    c[6] = 15;
    return 91;
  };
  return c[3];
}();
${prelude}
`;

describe("code-locks full removal", () => {
    it("removes every call and the definition of a lock whose checks touch only their own objects", async () => {
        // A probe function that never runs may name outside code; a call whose value is discarded may run in the
        // prelude; G may be tested.
        const program = `${localLock({
            checks: "var q = function () { if (false) { seen = 1; } }; d[8] = /seen/.test(q + []);",
            prelude: "G.L.check();\n(G.L.check(), 0);\nglobalThis.KeptG = G;",
        })}setTimeout(function () { G.L.check(); if (G) { result = [G.L.check(), seen]; } });\n`;
        const output = await runWithCleanup(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("check");
        expect(output).not.toContain("G.L");
    });

    it("removes the calls of a lock that G's computed reads before it and its global name can't reach", async () => {
        const program = `${localLock({
            before: 'var key = "L"; var early = typeof G[key];',
            prelude: "G.L.check();\nglobalThis.KeptG = G;",
        })}setTimeout(function () { result = [G.L.check(), early]; });\n`;
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("G.L.check()");
    });

    it("removes every call of a lock whose checks read a missing global through a setup-installed getter", async () => {
        // jscrambler's setup installs getters on G whose functions read one global the page lacks; calling one is a
        // read of that global, not a call into code outside the lock, so the prelude's call goes too.
        const setup = '(function () { Object.defineProperty(G, "r", { get: function () { return function () { return globalThis.MissingName7; }; } }); })();';
        const program = `${localLock({ before: setup, checks: 'd[8] = typeof G.r() === "function";' })}setTimeout(function () { result = [G.L.check()]; });\n`;
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("G.L.check()");
    });

    it("keeps the prelude's call while the lock may be reached otherwise", async () => {
        const cases = [
            { later: 'var key = "L"; result = [G[key].check()];' }, // a computed key
            { later: "var lock = G.L; result = [lock.check()];" }, // the holder by another name
            { later: "result = [(function () { return this.L.check(); }).call(G)];" }, // G handed on
            // A computed read in the prelude, after the first call: it answers the cached value.
            { prelude: 'G.L.check();\nvar key = "L";\nvar second = G[key].check();', later: "result = [second];" },
            // G kept as a global the program names again.
            { prelude: "G.L.check();\nglobalThis.KeptG = G;", later: "result = [KeptG.L.check()];" },
        ];
        for (const { prelude, later: afterPrelude } of cases) {
            const program = `${localLock(prelude === undefined ? {} : { prelude })}setTimeout(function () { ${afterPrelude} });\n`;
            const output = await runWithCleanup(program);
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain("}();\nG.L.check();");
        }
    });

    it("keeps the prelude's call while a wrapper of the lock still has callers", async () => {
        const wrapper = 'G.W = function () { return typeof G.L.check === "function" ? G.L.check.apply(G.L, arguments) : G.L.check; };\n';
        const program = `${localLock()}${wrapper}setTimeout(function () { G.L.check(); result = [G.W(), G.L.check()]; });\n`;
        const output = await runWithCleanup(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("}();\nG.L.check();");
    });

    it("keeps the prelude's calls when one of them uses the value", async () => {
        // After the first call the prelude's second one answers 67; without the first it would answer 91.
        const program = `${localLock({ prelude: "G.L.check();\nvar second = G.L.check();" })}setTimeout(function () { result = [second, G.L.check()]; });\n`;
        const output = await runWithCleanup(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("}();\nG.L.check();");
    });

    it("keeps the prelude's call when the checks change something outside their own objects", async () => {
        const effects = [
            "seen = true;", // an outer variable
            "d[6] = []; d[6].push.marked = true; seen = [].push.marked;", // a builtin (and then an outer variable)
            "d[7] = []; d[7].push.marked = true;", // a builtin
            "G.marked = true;", // an object from outside
            "try { var push = [].push; push(1); } catch (e) {}", // a builtin method with the global object as this
        ];
        for (const checks of effects) {
            const program = `${localLock({ checks })}setTimeout(function () { result = [G.L.check(), seen, [].push.marked === true, G.marked === true]; });\n`;
            const output = await run(program);
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain("}();\nG.L.check();");
        }
    });
});
