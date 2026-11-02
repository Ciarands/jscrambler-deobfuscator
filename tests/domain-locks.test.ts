import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const LICENSED = "licensed.example";

/** On the host the script was licensed for. */
const RUN: Run = { globals: () => ({ location: { hostname: LICENSED } }) };

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "domain-locks"] })).code;

const hash = (text: string, seed: number): number => {
    let x = seed;
    for (const char of text) x = (x * 31 + char.charCodeAt(0)) | 0;
    return x;
};

// A builder whose method hashes the host with a seed, caching per seed.
const runtime = (subject = "host.location.hostname") => `
function G() {}
G.H = function () {
  var host = globalThis;
  var cache = {};
  function subject() {
    return ${subject};
  }
  return {
    h: function (zero, flag, seed) {
      if (cache[seed] === undefined) {
        var text = subject();
        var x = seed;
        for (var i = 0; i < text.length; i++) x = (x * 31 + text.charCodeAt(i)) | 0;
        cache[seed] = x;
      }
      return cache[seed];
    }
  };
}();
`;

const gate = (first = `G.H.h(0, false, 5) === ${hash(LICENSED, 5)}`) => `if (${first} || G.H.h(0, false, 9) === ${hash("elsewhere.example", 9)}) {
  result = "licensed";
} else {
  result = "locked";
}
`;

describe("domain-locks", () => {
    it("answers tests of a host hash against literals as the licensed host passes them", async () => {
        const program = `${runtime()}${gate()}`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"licensed"');
        expect(output).toContain("if (true) {");
        expect(output).not.toContain("G.H.h(");
    });

    it("answers negated and conjunctive forms with the value the licensed host gives", async () => {
        const conjunction = `G.H.h(0, false, 5) !== ${hash(LICENSED, 5)} && G.H.h(0, false, 9) !== 1`;
        for (const [test, value] of [
            [conjunction, "false"],
            [`!(${conjunction})`, "true"],
        ] as const) {
            const program = `${runtime()}if (${test}) {\n  result = "locked";\n} else {\n  result = "licensed";\n}\n`;
            const output = await run(program);
            expect(observe(output, RUN)).toBe(observe(program, RUN));
            expect(output).toContain(`if (${value}) {`);
        }
    });

    it("keeps a conjunction of equalities, which the licensed host can pass", async () => {
        const program = `${runtime()}if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} && G.H.h(0, false, 9) === ${hash(LICENSED, 9)}) {\n  result = "licensed";\n} else {\n  result = "locked";\n}\n`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"licensed"');
    });

    it("keeps a comparison with a regular expression literal, which no hash equals", async () => {
        const program = `${runtime()}if (G.H.h(0, false, 5) === /x/) {\n  result = "licensed";\n} else {\n  result = "locked";\n}\n`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"locked"');
    });

    it("keeps tests when the lock is used outside them, or the storage object is read with a computed key", async () => {
        for (const use of ["var seen = G.H.h(0, false, 3);", 'var key = "H";\nvar seen = G[key].h(0, false, 3);']) {
            const program = `${runtime()}${gate()}${use}\n`;
            const output = await run(program);
            expect(observe(output, RUN)).toBe(observe(program, RUN));
            expect(output).toContain(`if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} ||`);
        }
    });

    it("answers tests while a wrapper of another of the builder's methods is unused, not while it is called", async () => {
        const builder = runtime().replace("return {\n", "return {\n    g: function () { return 2; },\n");
        const wrapper = 'G.W = function () { return typeof G.H.g === "function" ? G.H.g.apply(G.H, arguments) : G.H.g; };\n';
        const unused = `${builder}${wrapper}${gate()}`;
        const answered = await run(unused);
        expect(observe(answered, RUN)).toBe(observe(unused, RUN));
        expect(answered).toContain("if (true) {");
        const called = `${builder}${wrapper}${gate()}var seen = G.W();\n`;
        const kept = await run(called);
        expect(observe(kept, RUN)).toBe(observe(called, RUN));
        expect(kept).toContain(`if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} ||`);
    });

    it("keeps tests whose hash reads nothing of the host", async () => {
        const program = `${runtime('"fixed text"')}${gate()}`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} ||`);
    });

    it("keeps tests whose hash reads a local that shadows a global object name", async () => {
        const program = `${runtime('(function (window) { return window.location.hostname; })({ location: { hostname: "fixed.example" } })')}${gate()}`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"locked"');
    });

    it("keeps tests that also call a lock whose hash reads nothing of the host", async () => {
        const other = `G.J = function () {\n  return { h: function () { return 1; } };\n}();\n`;
        const program = `${runtime()}${other}${gate(`G.H.h(0, false, 5) === 1 || G.J.h(0) === 2`)}`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"locked"');
    });

    it("keeps tests calling a method the builder doesn't give", async () => {
        const program = `${runtime()}try {\n${gate("G.H.missing(0, false, 5) === 1")}} catch (error) {\n  result = "threw";\n}\n`;
        const output = await run(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(observe(program, RUN)).toBe('"threw"');
    });

    it("keeps tests with a comparison that isn't a lock call with literal arguments", async () => {
        for (const first of ["G.H.h(0, false, seed) === 1", "G.H.h(0, false, 5) === other", "other === 1"]) {
            const program = `var seed = 5, other = 1;\n${runtime()}${gate(first)}`;
            const output = await run(program);
            expect(observe(output, RUN)).toBe(observe(program, RUN));
            expect(output).toContain(`if (${first} ||`);
        }
    });
});
