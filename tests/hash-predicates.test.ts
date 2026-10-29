import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

/** What a script leaves in `result`; `setTimeout` callbacks (code after the prelude) run once it has finished. */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(source, context, { timeout: 2000 });
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "hash-predicates", "simplify"] })).code;

/** The test programs' hash, as the runtime's builder defines it. */
const hash = (s: string, n: number, seed: number): number => {
    let q = seed;
    for (let i = 0; i < n; i++) q = Math.imul(q ^ s.charCodeAt(i), 16777619) | 0;
    return q;
};

/** The hash's loop, then what a variant does with `q`. */
const hashCode = (returned = "q", before = "") => `function (s, n, seed) { ${before} var q = seed; for (var i = 0; i < n; i++) { q = mix(q ^ s.charCodeAt(i), 16777619); } return ${returned}; }`;

/** A runtime with the hash on `G.U.h` (as `G.w` too, through a wrapper), and `app` (from `body`) run after the prelude. */
const program = ({ body, builder = "", hashSource = hashCode(), prelude = "", later = "" }: { body: string; builder?: string; hashSource?: string; prelude?: string; later?: string }) => `
function G() {}
var log = [];
G.U = (function () {
  ${builder}
  var mix = function (a, b) { return Math.imul(a, b) | 0; };
  var h = ${hashSource};
  return { h };
})();
G.w = function () { return typeof G.U.h === "function" ? G.U.h.apply(G.U, arguments) : G.U.h; };
${prelude}
function app() {
  ${body}
}
setTimeout(function () { ${later} app(); result = log; });
`;

/** jscrambler's predicate pair: a counting loop until the hash of `d` is `a`, then an `if` on the hash of the count. */
const predicates = ({ untilDigit = 1, ifTrue = false, loopBody = "S += 2;", between = "", call = "G.U.h" } = {}) => {
    const a = hash(String(untilDigit), 1, 77300);
    const count = 2 + 2 * (untilDigit - 1);
    const O = hash(String(count), String(count).length, 42066) + (ifTrue ? 1 : 0);
    return `var a, O, S;
  a = ${a}; O = ${O}; S = 2;${between}
  for (var d = 1; ${call}(d.toString(), d.toString().length, 77300) !== a; d++) { ${loopBody} }
  if (${call}(S.toString(), S.toString().length, 42066) !== O) { log.push("decoy"); }
  log.push("real", S, d);`;
};

/** A lone `if` on the hash of a constant: the program ends whatever the hash does. */
const lonePredicate = `if (G.U.h("1", 1, 77300) !== ${hash("1", 1, 77300)}) { log.push("decoy"); }
  log.push("real");`;

/** A counting loop on `d` until its hash is `until`, around `body`. */
const loop = (head: string, until: number, body: string) => `for (${head} = 1; G.U.h(d.toString(), d.toString().length, 77300) !== ${until}; d++) { ${body} }`;

describe("hash-predicates", () => {
    it("decides the pair when the loop never runs, directly and through a wrapper", async () => {
        for (const call of ["G.U.h", "G.w"]) {
            const input = program({ body: predicates({ call }) });
            const output = await run(input);
            expect(observed(output)).toBe(observed(input));
            expect(output).not.toContain(`${call}(`);
            expect(output).not.toContain("decoy");
        }
    });

    it("takes a hash reading char codes through String.prototype.charCodeAt.bind for pure, unless String is a local", async () => {
        const bound = `function (s, n, seed) { var code = String.prototype.charCodeAt.bind(s); var q = seed; for (var i = 0; i < n; i++) { q = mix(q ^ code(i), 16777619); } return q; }`;
        const shadow = `var String = { prototype: { charCodeAt: { bind: function (s) { return function (i) { log.push("own"); return s.charCodeAt(i); }; } } } };`;
        for (const [name, builder] of Object.entries({ global: "", local: shadow })) {
            const input = program({ body: lonePredicate, builder, hashSource: bound });
            const output = await run(input);
            expect(observed(output), name).toBe(observed(input));
            expect(output.includes("G.U.h("), name).toBe(name === "local");
        }
    });

    it("replaces a counting loop by its final values, and keeps the branch the test takes", async () => {
        expect([hash("1", 1, 77300), hash("2", 1, 77300)]).not.toContain(hash("3", 1, 77300));
        const input = program({ body: predicates({ untilDigit: 3, ifTrue: true }) });
        const output = await run(input);
        expect(observed(output)).toBe(observed(input));
        expect(output).not.toContain("G.U.h(");
        expect(output).toContain(`log.push("decoy");`);
    });

    it("unrolls a loop that runs once whatever its body does", async () => {
        const input = program({ body: predicates({ untilDigit: 2, loopBody: `log.push("body"); S += 2;` }) });
        const output = await run(input);
        expect(observed(output)).toBe(observed(input));
        expect(output).not.toContain("G.U.h(");
    });

    it("unrolls a loop that runs once only into code that does the same", async () => {
        const once = hash("2", 1, 77300);
        const twice = hash("3", 1, 77300);
        const unrolled = {
            // Block-scoped names of the body keep their block: the function declares the same names.
            scopedBody: `${loop("var d", once, `let x = "body"; log.push(x);`)} let x = "after"; log.push(x, d);`,
        };
        const kept = {
            breaks: `${loop("var d", once, `log.push("body"); break;`)} log.push(d);`,
            lexicalInit: `${loop("let d", once, `log.push("body");`)} let d = "after"; log.push(d);`,
            // Counts on the first run, throws on the second: not a loop that runs once.
            throwsOnSecond: `var x = 1, y; try { ${loop("var d", twice, "y = x.toString(); x = null;")} } catch (e) { log.push("threw"); } log.push(y);`,
        };
        for (const [name, body] of [...Object.entries(unrolled), ...Object.entries(kept)]) {
            const input = program({ body });
            const output = await run(input);
            expect(observed(output), name).toBe(observed(input));
            expect(output.includes("G.U.h("), name).toBe(name in kept);
        }
    });

    it("keeps predicates on a hash that isn't pure", async () => {
        const hashes = {
            writesOutside: hashCode("q", "calls++;"),
            readsChangingOuter: hashCode("q + salt"),
            random: hashCode("Math.random() < 2 ? q : 0"),
        };
        const builder = "var calls = 0; var salt = 0; G.salt = function (x) { salt = x; }; G.calls = function () { return calls; };";
        for (const [name, hashSource] of Object.entries(hashes)) {
            const input = program({ body: `${lonePredicate} log.push(G.calls());`, builder, hashSource, later: "G.salt(1);" });
            const output = await run(input);
            expect(observed(output), name).toBe(observed(input));
            expect(output, name).toContain("G.U.h(");
        }
    });

    it("keeps loops that run more than once doing more than counting", async () => {
        const input = program({ body: predicates({ untilDigit: 3, loopBody: `log.push("body"); S += 2;` }) });
        const output = await run(input);
        expect(observed(output)).toBe(observed(input));
        expect(output).toContain("G.U.h(d.toString()");
    });

    it("keeps predicates whose locals a call in between may change", async () => {
        // The closure is made before the local gets its value, and called after.
        const body = `var set = function () { a = ${hash("2", 1, 77300)}; };\n  ${predicates({ between: " set();" })}`;
        const input = program({ body });
        const output = await run(input);
        expect(observed(output)).toBe(observed(input));
        expect(output).toContain("G.U.h(d.toString()");
    });

    it("keeps predicates on a hash the guest no longer holds, or that changes after the prelude", async () => {
        const replaced = `function (s, n, seed) { log.push("replaced"); return seed; }`;
        for (const [name, options] of Object.entries({
            // Through a reference the analysis doesn't follow (handed to a builtin), while the prelude runs.
            replacedInPrelude: { prelude: `Object.defineProperty(G.U, "h", { value: ${replaced} });` },
            replacedLater: { later: `G.U.h = ${replaced};` },
        })) {
            const input = program({ body: lonePredicate, ...options });
            const output = await run(input);
            expect(observed(output), name).toBe(observed(input));
            expect(output, name).toContain("G.U.h(");
        }
    });
});
