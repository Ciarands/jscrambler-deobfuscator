import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

const run = async (code: string) => (await deobfuscate(code, { passes: ["emulate", "global-proxy"] })).code;

/**
 * What a script leaves in `result`. Code that runs after the prelude is scheduled with `setTimeout`: the emulator's
 * timers never fire, here they run (synchronously, in order) once the script has finished.
 */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(source, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

/** What a script and its deobfuscation leave in `result`, and the deobfuscation. */
const observe = async (code: string): Promise<[string, string, string]> => {
    const output = await run(code);
    return [observed(code), observed(output), output];
};

// The shape jscrambler's prelude uses: the global object, found through a getter, parked on the storage function.
const PRELUDE = `
G[7] = (function () {
  if (typeof globalThis === "object") return globalThis;
  var g;
  try {
    Object.defineProperty(Object.prototype, "q", { get: function () { return this; }, configurable: true });
    g = q;
    delete Object.prototype.q;
  } catch (e) { g = window; }
  return g;
})();
G[8] = 2;
function G() {}
`;

describe("global-proxy", () => {
    it("replaces reads of the global-object slot, through the storage object and locals that only hold it", async () => {
        const output = await run(`${PRELUDE}
G[7].console.log("x");
G[7].y = 5;
function f() { var s = G; return s[7].Math; }
`);
        expect(output).toContain(`globalThis.console.log("x");`);
        expect(output).toContain("globalThis.y = 5;");
        expect(output).toContain("return globalThis.Math;");
    });

    it("leaves shadowing locals, writes, other slots and reassigned aliases alone", async () => {
        const output = await run(`${PRELUDE}
function f(G) { return G[7]; }
G[7] = 1;
G[8];
function g() { var s = G; s = other; return s[7]; }
`);
        expect(output).toContain("return G[7];");
        expect(output).toContain("G[7] = 1;");
        expect(output).toContain("G[8];");
        expect(output).toContain("return s[7];");
        expect(output.match(/globalThis/g)).toHaveLength(2); // only the prelude's own
    });

    it("keeps reads that may see another value than the snapshot's", async () => {
        // Written again after the prelude.
        const [laterBefore, laterAfter, laterOutput] = await observe(
            `${PRELUDE}\nfunction reset() { G[7] = { marker: 1 }; }\nfunction read() { return G[7].marker; }\nsetTimeout(function () { result = [read(), (reset(), read())]; });\n`
        );
        expect(laterAfter).toBe(laterBefore);
        expect(laterOutput).toContain("return G[7].marker;");

        // Read while the prelude hasn't set it up yet.
        const [earlyBefore, earlyAfter] = await observe(`var early = typeof G[7];\n${PRELUDE}\nresult = early;\n`);
        expect(earlyAfter).toBe(earlyBefore);

        // Written through the name the prelude shares G under.
        const [sharedBefore, sharedAfter] = await observe(
            `${PRELUDE}\nG[7].SHARE = G;\nfunction read() { return G[7].marker; }\nsetTimeout(function () { var first = read(); SHARE[7] = { marker: 2 }; result = [first, read()]; });\n`
        );
        expect(sharedAfter).toBe(sharedBefore);
    });

    it("keeps reads where globalThis is a local name", async () => {
        const [before, after] = await observe(`${PRELUDE}\nfunction f(globalThis) { return G[7].marker; }\nsetTimeout(function () { result = f({ marker: 3 }); });\n`);
        expect(after).toBe(before);
    });

    it("rewrites reads that see the snapshot's value, also inside the prelude's own functions", async () => {
        const [before, after, output] = await observe(`${PRELUDE}\nG[7].SHARE = G;\nfunction read() { return typeof G[7].Math; }\nsetTimeout(function () { result = read(); });\n`);
        expect(after).toBe(before);
        expect(output).toContain("return typeof globalThis.Math;");
    });

    it("judges code by when it runs: never, only while the prelude runs, or later", async () => {
        // Nothing calls it: its write never happens.
        const [neverBefore, neverAfter, neverOutput] = await observe(
            `${PRELUDE}\nfunction unused() { G[7] = { marker: 1 }; }\nfunction read() { return typeof G[7].Math; }\nsetTimeout(function () { result = read(); });\n`
        );
        expect(neverAfter).toBe(neverBefore);
        expect(neverOutput).toContain("return typeof globalThis.Math;");

        // Only the prelude calls it: what its method call does with `this` (G) is in the snapshot.
        const [preludeBefore, preludeAfter, preludeOutput] = await observe(
            `${PRELUDE}\nG.m = function () { this.flag = 1; };\nfunction setup() { G.m(); }\nsetup();\nfunction read() { return typeof G[7].Math; }\nsetTimeout(function () { result = read(); });\n`
        );
        expect(preludeAfter).toBe(preludeBefore);
        expect(preludeOutput).toContain("return typeof globalThis.Math;");
    });
});
