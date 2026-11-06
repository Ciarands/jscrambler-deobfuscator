import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

/** Runs in a page: a `document` exists (model 10), timers run after the script. */
const RUN: Run = { globals: () => ({ document: { title: "page" } }), timers: true };

const WRAPPER = 'G.w = function () { return typeof G.D.get === "function" ? G.D.get.apply(G.D, arguments) : G.D.get; };';

describe("answers that depend on the environment", () => {
    it("keeps a call whose answer depends on a host global", async () => {
        const program = `function G() {}
G.D = (function () { return { get: function (i) { return typeof document === "undefined" ? "decoy" : "real"; } }; })();
${WRAPPER}
var url = G.w(1);
result = url;
`;
        const { code } = await deobfuscate(program);
        expect(code).not.toMatch(/url = "decoy"|G\.w\(1\), "decoy"/);
        expect(code).toMatch(/url = G\.(w|D\.get)\(1\)/);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
    });

    it("resolves a call that reads a host global without depending on it", async () => {
        const program = `function G() {}
G.D = (function () { var seen = typeof document; return { get: function (i) { return ["a", "b"][i]; } }; })();
${WRAPPER}
var x = G.w(1);
result = x;
`;
        const { code } = await deobfuscate(program, { passes: ["runtime", "resolve-calls"] });
        expect(code).toContain('"b"');
    });

    it("doesn't fold what depends on the engine's builtin surface", async () => {
        const program = `function count() { return Object.getOwnPropertyNames(Math).length; }
function mode() { return typeof Math.sumPrecise === "function" ? "decoy" : "real"; }
function has() { return "findLast" in Array.prototype; }
function plain() { return [1, 2, 3].map(function (x) { return x * 2; }).join("-"); }
result = [count(), mode(), has(), plain()];
`;
        const { code } = await deobfuscate(program, { passes: ["pure-calls"] });
        expect(code).toContain("count()");
        expect(code).toContain("mode()");
        expect(code).toContain("has()");
        expect(code).toContain('"2-4-6"');
    });

    it("keeps calls of wrappers whose targets lead back to themselves", async () => {
        const self = 'G.a = function () { return typeof G.a === "function" ? G.a.apply(G.a, arguments) : G.a; };';
        const cycle =
            'G.a = function () { return typeof G.b === "function" ? G.b.apply(G, arguments) : G.b; };\nG.b = function () { return typeof G.a === "function" ? G.a.apply(G, arguments) : G.a; };';
        for (const wrappers of [self, cycle]) {
            for (const call of ["G.a(1)", 'G[document.title === "page" ? "a" : "k"](1)']) {
                const program = `function G() {}\nG.k = function (n) { return n + 1; };\n${wrappers}\nsetTimeout(function () { try { result = ${call}; } catch (e) { result = e.name; } });\n`;
                const { code } = await deobfuscate(program);
                expect(code).toContain(`result = ${call};`);
                expect(observe(code, RUN)).toBe(observe(program, RUN));
            }
        }
    });
});
