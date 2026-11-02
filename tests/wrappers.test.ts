import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
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

const inline = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "wrappers"] })).code;

const WRAPPER = `G.f = function () { return typeof G.H.add === "function" ? G.H.add.apply(G.H, arguments) : G.H.add; };`;

describe("wrappers", () => {
    it("inlines calls by target kind, through aliases of the storage object, and keeps behaviour", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["emulate", "wrappers"] });
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
});
