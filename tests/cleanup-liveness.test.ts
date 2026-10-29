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

/**
 * jscrambler's decoder shape: it finds its string function by trying permutations of a few characters (`codes`, each
 * one below its character) until `G[name]` exists. `before` runs before the decoder, `after` after it; the decoder is
 * used after the prelude with a key no pass can resolve, so it stays, and its probe with it.
 */
const runtime = ({ before = "", codes = "[79, 112]", after = "", later = "" } = {}) => `
function G() {}
G.Pq = function () { return "a,b,c"; };
${before}
G.D = (function () {
  var probe = function (codes) {
    var chars = [];
    var i = 0;
    while (i < codes.length) {
      chars[i] = String.fromCharCode(codes[i] + 1);
      i++;
    }
    var name;
    var found;
    do {
      name = chars.sort(function () { return 0.5 - Math.random(); }).join("");
      found = G[name];
    } while (!found);
    return found;
  };
  var table = probe(${codes})().split(",");
  return { get: function (i) { return table[i]; } };
})();
${after}
setTimeout(function () { ${later} result = G.D.get(Math.floor(Math.random() * 3)) === undefined ? "none" : "some"; });
`;

const run = async (code: string): Promise<string> => (await deobfuscate(code)).code;

describe("cleanup: computed reads in prelude-only code", () => {
    it("removes definitions that run after the probe", async () => {
        const program = runtime({ after: "G.late = function () { return 2; };" });
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("G.late");
        // What the probe finds stays.
        expect(output).toContain("G.Pq = ");
    });

    it("removes definitions before the probe whose key it can't name", async () => {
        const program = runtime({ before: "G.zz = function () { return 3; };" });
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).not.toContain("G.zz");
    });

    it("keeps definitions before the probe whose key it may name", async () => {
        // Either permutation may be found first: both give a table.
        const program = runtime({ before: 'G.qP = function () { return "d,e,f"; };' });
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("G.qP = ");
    });

    it("keeps every definition before the probe when its keys can't be derived", async () => {
        const program = runtime({ before: "G.zz = function () { return 3; };", codes: 'JSON.parse("[79, 112]")', after: "G.late = function () { return 2; };" });
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("G.zz = ");
        expect(output).not.toContain("G.late");
    });

    it("keeps the runtime when a computed read may run after the prelude", async () => {
        const program = runtime({ after: "G.late = function () { return 2; };", later: 'var k = ["la", "te"].join(""); G[k];' });
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain("G.late = ");
    });
});
