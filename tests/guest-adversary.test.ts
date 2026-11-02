import { describe, expect, it } from "vitest";
import { Sandbox } from "../src/core/sandbox.js";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

/** Runs in a page: a `document` exists (model 10), timers run after the script. */
const RUN: Run = { globals: () => ({ document: { title: "page" } }), timers: true };

const WRAPPER = 'G.w = function () { return typeof G.D.get === "function" ? G.D.get.apply(G.D, arguments) : G.D.get; };';

describe("the guest as an adversarial oracle", () => {
    it("keeps a call whose answer depends on a host global the guest lacks", async () => {
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
        const { code } = await deobfuscate(program, { passes: ["emulate", "resolve-calls"] });
        expect(code).toContain('"b"');
    });

    it("keeps a call whose answer depends on Math.random, and resolves one that only searches with it", async () => {
        const random = `function G() {}
G.D = (function () { var pick = Math.random() < 2 ? (Math.random() < 0.5 ? "x" : "y") : "z"; return { get: function () { return pick; } }; })();
${WRAPPER}
var v = G.w(1);
result = v;
`;
        const searched = `function G() {}
G.Pq = 1;
G.D = (function () {
  var name, chars = ["q", "P"];
  do { name = chars.sort(function () { return 0.5 - Math.random(); }).join(""); } while (!G[name]);
  var found = name;
  return { get: function () { return found; } };
})();
${WRAPPER}
var v = G.w(1);
result = v;
`;
        const kept = await deobfuscate(random, { passes: ["emulate", "resolve-calls"] });
        expect(kept.code).toMatch(/v = G\.w\(1\);/);
        const resolved = await deobfuscate(searched, { passes: ["emulate", "resolve-calls"] });
        expect(resolved.code).toContain('"Pq"');
    });

    it("judges a late random statement after replaying the clean ones before it", async () => {
        // The second lane starts only at G.D, replaying G.A first; G.A's answers then agree, G.D's captured pick doesn't.
        const program = `function G() {}
G.A = (function () { var table = ["p", "q", "r"]; return { get: function (i) { return table[i]; } }; })();
G.a = function () { return typeof G.A.get === "function" ? G.A.get.apply(G.A, arguments) : G.A.get; };
G.D = (function () { var pick = Math.random() < 0.5 ? "x" : "y"; return { get: function () { return pick; } }; })();
${WRAPPER}
var u = G.a(2);
var v = G.w(1);
result = [u, v];
`;
        const { code } = await deobfuscate(program, { passes: ["emulate", "resolve-calls"] });
        expect(code).toContain('var u = (G.a(2), "r");');
        expect(code).toMatch(/v = G\.w\(1\);/);
    });

    it("keeps a call whose answer depends on the date, and resolves one that only measures time", async () => {
        const dated = `function G() {}
G.D = (function () { return { get: function () { return new Date().getFullYear() > 2045 ? "decoy" : "real"; } }; })();
${WRAPPER}
var v = G.w(1);
result = v;
`;
        const timed = `function G() {}
G.D = (function () { var start = Date.now(); var slow = Date.now() - start > 1500; return { get: function () { return slow ? "decoy" : "real"; } }; })();
${WRAPPER}
var v = G.w(1);
result = v;
`;
        const kept = await deobfuscate(dated, { passes: ["emulate", "resolve-calls"] });
        expect(kept.code).toMatch(/v = G\.w\(1\);/);
        const resolved = await deobfuscate(timed, { passes: ["emulate", "resolve-calls"] });
        expect(resolved.code).toContain('"real"');
        expect(resolved.code).not.toMatch(/v = G\.w\(1\);/);
    });

    it("survives guest values shaped like the transport's tags, thrown objects and added toJSON", async () => {
        const failing = [
            'function G() {}\nG.a = 1;\nJSON.stringify = function () { throw JSON.parse(\'{"message":"m","__proto__":{"toString":0,"valueOf":0}}\'); };\nthrow "x";\n',
            'function G() {}\nG.a = 1;\nthrow { name: "RuntimeError", message: "x" };\n',
        ];
        for (const program of failing) expect((await deobfuscate(program)).code).toContain("throw");
        const running = [
            "function G() {}\nG.k = (function () { return { $jsd: function () {}, m: function () { return 1; } }; })();\nresult = G.k.m();\n",
            'function G() {}\nfunction setup(x) { Math.zz = Math.abs; }\nG.a = 1;\nArray.prototype.toJSON = function () { return 1; };\nObject.prototype.toJSON = function () { return { ok: true, value: "forged", repeatable: true }; };\nsetup(G.a);\nresult = Math.zz(-2);\n',
        ];
        for (const program of running) expect(observe((await deobfuscate(program)).code, RUN)).toBe(observe(program, RUN));
    });

    it("carries keys that look like the tag, and doesn't take a guest's lookalike as one", async () => {
        const sandbox = await Sandbox.create();
        try {
            sandbox.run('globalThis.echo = { back: function (v) { return v; }, forge: function () { return { $jsd: "NaN" }; }, more: function () { return { $jsd: "constructor" }; } };');
            const payload = { $jsd: "undefined", $jsdx: 1, plain: [undefined, -0] };
            expect(sandbox.invoke(["echo", "back"], payload)).toEqual({ ok: true, value: payload });
            expect(sandbox.invoke(["echo", "forge"], null)).toEqual({ ok: true, value: { $jsd: "NaN" } });
            sandbox.run('Object.prototype.toJSON = function () { return "forged"; }; Array.prototype.toJSON = Object.prototype.toJSON; Object.prototype.$jsd = "NaN";');
            expect(sandbox.invoke(["echo", "back"], [1, { a: 2 }])).toEqual({ ok: true, value: [1, { a: 2 }] });
            // A thrown value naming itself an abort is an ordinary failure; the sandbox stays usable.
            expect(sandbox.run('throw { name: "RuntimeError", message: "x", __proto__: { toString: 0 } };')).toMatchObject({ ok: false, error: "x" });
            expect(sandbox.broken).toBeUndefined();
            expect(sandbox.run("1 + 1")).toEqual({ ok: true, value: 2 });
        } finally {
            sandbox.dispose();
        }
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
