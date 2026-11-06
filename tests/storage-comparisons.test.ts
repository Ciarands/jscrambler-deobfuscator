import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

// Matrix: a prelude builder makes rows that point at each other; opaque predicates compare cells.
const MATRIX = `
var seen = 0;
function G() {}
G.k = (function (n) {
  var m = [];
  for (var i = 0; i < n; i++) m[i] = [];
  for (var r = 0; r < n; r++) for (var c = 0; c < n; c++) m[r][c] = m[(r * 2 + c) % n];
  return { m: m, v: 7, o: { valueOf: function () { seen++; return 7; } } };
})(3);
`;

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["runtime", "storage-comparisons"] })).code;

const RUN: Run = { timers: true };

describe("storage-comparisons", () => {
    it("folds equality tests between cells of a matrix nothing changes after the prelude", async () => {
        const program = `${MATRIX}setTimeout(function () { result = [G.k.m[1][2] != G.k.m[0][0], G.k.m[0][1] === G.k.m[2][2], G.k.v == G.k.v]; });\n`;
        const output = await run(program);
        expect(output).toContain("result = [true, false, true];");
        expect(observe(output, RUN)).toBe(observe(program, RUN));
    });

    it("keeps tests whose cells may change, or that would convert an object", async () => {
        const cases = [
            // A later write makes the rows the same.
            { program: `${MATRIX}setTimeout(function () { G.k.m[1] = G.k.m[0]; result = [G.k.m[1] === G.k.m[0]]; });\n`, kept: "G.k.m[1] === G.k.m[0]" },
            // Comparing an object with a number calls its valueOf.
            { program: `${MATRIX}setTimeout(function () { result = [G.k.o == G.k.v, seen]; });\n`, kept: "G.k.o == G.k.v" },
        ];
        for (const { program, kept } of cases) {
            const output = await run(program);
            expect(output).toContain(kept);
            expect(observe(output, RUN)).toBe(observe(program, RUN));
        }
    });

    it("keeps tests of a literal the prelude changes through a wrapper's this", async () => {
        const program = `
function G() {}
G.k = { a: 1, b: 1 };
G.T = function () { this.a = 2; };
G.w = function () { return typeof G.T === "function" ? G.T.apply(G.k, arguments) : G.T; };
G.w();
setTimeout(function () { result = [G.k.a == G.k.b]; });
`;
        const output = await run(program);
        expect(output).toContain("G.k.a == G.k.b");
        expect(observe(output, RUN)).toBe(observe(program, RUN));
    });
});
