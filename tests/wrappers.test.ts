import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { createLogger } from "../src/logger.js";
import { observe, type Run } from "./helpers.js";

const PROGRAM = `
function G() {}
G.H = { base: 10, add: function (x) { return this.base + x; }, limit: 3 };
G.f = function () { return typeof G.H.add === "function" ? G.H.add.apply(G.H, arguments) : G.H.add; };
G.v = function () { return typeof G.H.limit === "function" ? G.H.limit.apply(G.H, arguments) : G.H.limit; };
G.o = function () { return typeof G.H.add === "function" ? G.H.add.apply(G.other, arguments) : G.H.add; };
G.other = { base: 100 };
function run(n) {
  var s = G;
  return [s.f(n), G.v(), G.v(n), G.o(n)];
}
result = run(host.n);
`;

const RUN: Run = { globals: () => ({ host: { n: 5, k: () => 7 } }), timers: true };

const inline = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["runtime", "wrappers"] })).code;

const WRAPPER = `G.f = function () { return typeof G.H.add === "function" ? G.H.add.apply(G.H, arguments) : G.H.add; };`;

describe("wrappers", () => {
    it("inlines calls by target kind, through aliases of the storage object, and keeps behaviour", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["runtime", "wrappers"] });
        // Function target, called through a local holding G: rooted on that local.
        // Value target: inlined only without arguments. A foreign `this` blocks inlining.
        expect(code).toContain("return [s.H.add(n), G.H.limit, G.v(n), G.o(n)];");
        expect(observe(code, RUN)).toBe(observe(PROGRAM, RUN));
    });

    it("inlines calls whose arguments run code when nothing but G's paths reaches the target", async () => {
        // A builder returns a fresh literal naming its local function (`{ add }`).
        const program = `
function G() {}
G.H = (function () {
  var add = function (s, n) { return s + ":" + n; };
  return { add };
})();
${WRAPPER}
setTimeout(function () { var n = host.k(); result = G.f(n.toString(), host.k()); });
`;
        const output = await inline(program);
        expect(output).toContain("result = G.H.add(n.toString(), host.k());");
        expect(observe(output, RUN)).toBe(observe(program, RUN));
    });

    it("keeps calls whose arguments may change the target first", async () => {
        const cases = {
            // The target's object is held in a binding of its own: calling the target swaps it without naming G's paths.
            held: `
function G() {}
var holder = {};
G.H = holder;
G.H.add = function (x) { holder.add = function () { return "swapped"; }; return x; };
${WRAPPER}
setTimeout(function () { result = G.f(G.f(1)); });
`,
            // A method called on the target's object swaps the target through `this`.
            swapped: `
function G() {}
G.H = { add: function (x) { return x + 1; }, swap: function () { this.add = function () { return "swapped"; }; return 1; } };
${WRAPPER}
setTimeout(function () { result = G.f(G.H.swap()); });
`,
            // The builder's local is reassigned to a function that swaps the target through \`this\`.
            reassigned: `
function G() {}
G.H = (function () {
  var add = function (x) { return x + 1; };
  add = function (x) { this.add = function () { return "swapped"; }; return x; };
  return { add: add };
})();
${WRAPPER}
setTimeout(function () { result = G.f(G.f(1)); });
`,
        };
        for (const program of Object.values(cases)) {
            const output = await inline(program);
            expect(observe(output, RUN)).toBe(observe(program, RUN));
            expect(output).toContain("result = G.f(");
        }
    });

    it("keeps calls whose target is written after the prelude", async () => {
        // The snapshot's function target becomes a value: the wrapper returns it, an inlined call would throw.
        const program = `
function G() {}
G.H = { add: function (x) { return x + 1; } };
${WRAPPER}
setTimeout(function () { G.H.add = 5; result = G.f(1); });
`;
        const output = await inline(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("result = G.f(1);");
    });

    it("doesn't take a parameter for G when a spread comes before its argument", async () => {
        const program = `
function G() {}
G.H = { add: function (x) { return x + 1; } };
${WRAPPER}
setTimeout(function () {
  result = (function (a, p) { return typeof p.f === "function" ? p.f(1) : p; })(...[1, { f: function () { return "own"; } }], G);
});
`;
        const output = await inline(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("p.f(1)");
    });

    it("takes no wrapper its assignment may not store", async () => {
        for (const [before, key, reason] of [
            ["", "name", "a function inherits it as an accessor or a read-only property"],
            ["", "__proto__", "a function inherits it as an accessor or a read-only property"],
            ["Object.preventExtensions(G);\n", "f", "prelude code hands G to a call"],
            ["G.lock = function () { Object.preventExtensions(this); };\nG.lock();\n", "f", "a prelude call may change G through its this"],
            ["setTimeout(function () { G = { H: { add: function () { return 0; } } }; });\n", "f", "G isn't a root function declaration nothing reassigns"],
        ]) {
            const program = `
function G() {}
G.H = { add: function (x) { return x + 1; } };
${before}${WRAPPER.replace("G.f =", `G[${JSON.stringify(key)}] =`)}
setTimeout(function () { try { result = G[${JSON.stringify(key)}](1); } catch (e) { result = e.name; } });
`;
            const lines: string[] = [];
            const { code } = await deobfuscate(program, { passes: ["runtime", "wrappers"], logger: createLogger("debug", (line) => lines.push(line)) });
            expect(
                lines.some((line) => line.includes(`G.${key} isn't taken as a wrapper: ${reason}`)),
                reason
            ).toBe(true);
            expect(observe(code, RUN), reason).toBe(observe(program, RUN));
        }
    });

    it("takes no wrapper on a key the setup defines on G or adds to what G inherits", async () => {
        for (const [setup, key, reason] of [
            ['Object.defineProperty(G, "f", { get: function () { return String.fromCharCode; }, configurable: true });', "f", "the setup defines it"],
            // A read-only data property: the wrapper's assignment does nothing, and the call throws.
            ['Object.defineProperty(G, "f", { value: 5, configurable: true });', "f", "the setup defines it"],
            ["g.Object.prototype.q = g.Object.prototype.hasOwnProperty;", "q", "the setup adds it to a builtin"],
            // Not an alias (no builtin reads 1): the assignment to G.q does nothing all the same.
            ['Object.defineProperty(g.Function.prototype, "q", { value: 1, configurable: true });', "q", "the setup adds it to a builtin"],
        ]) {
            const program = `
function G() {}
G[3] = (function () { return globalThis; })();
G.H = { add: function (x) { return x + 1; } };
function S(g) { ${setup} }
S(G[3]);
${WRAPPER.replace("G.f =", `G.${key} =`)}
setTimeout(function () { try { result = G.${key}(72); } catch (e) { result = e.name; } });
`;
            const lines: string[] = [];
            const { code } = await deobfuscate(program, { passes: ["runtime", "wrappers"], logger: createLogger("debug", (line) => lines.push(line)) });
            expect(
                lines.some((line) => line.includes(`G.${key} isn't taken as a wrapper: ${reason}`)),
                reason
            ).toBe(true);
            expect(observe(code, RUN), reason).toBe(observe(program, RUN));
        }
    });

    it("follows G held in a literal: kept as a global by that name, or handed on otherwise", async () => {
        for (const [keep, change, reason] of [
            ["globalThis.holder = { q: G };", "holder.q.f = function () { return 'boom'; };", undefined],
            ["globalThis.held = [G];", "held[0].f = function () { return 'boom'; };", undefined],
            ["", "(function (o) { o.q.f = function () { return 'boom'; }; })({ q: G });", "prelude code hands G to a call"],
            ["var o = { q: G };\nglobalThis.holder = o;", "holder.q.f = function () { return 'boom'; };", "prelude code hands G to a call"],
        ]) {
            const program = `
function G() {}
G.H = { add: function (x) { return x + 1; } };
${keep}
${WRAPPER}
${change}
setTimeout(function () { result = G.f(1); });
`;
            const lines: string[] = [];
            const { code } = await deobfuscate(program, { passes: ["runtime", "wrappers"], logger: createLogger("debug", (line) => lines.push(line)) });
            expect(observe(code, RUN), change).toBe(observe(program, RUN));
            expect(code, change).toContain("result = G.f(1);");
            if (reason !== undefined)
                expect(
                    lines.some((line) => line.includes(`G.f isn't taken as a wrapper: ${reason}`)),
                    change
                ).toBe(true);
        }
    });
});
