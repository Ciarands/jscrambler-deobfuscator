import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

const LICENSED = "licensed.example";

/** What a script leaves in `result` on the host it was licensed for. */
const observed = (source: string): string => {
    const context: Record<string, unknown> = { location: { hostname: LICENSED } };
    runInNewContext(source, context);
    return JSON.stringify(context.result);
};

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "domain-locks"] })).code;

/** The fixture's hash of `text` with `seed`. */
const hash = (text: string, seed: number): number => {
    let x = seed;
    for (const char of text) x = (x * 31 + char.charCodeAt(0)) | 0;
    return x;
};

// jscrambler's shape: a builder returns an object whose method hashes the host (read by a helper of the builder)
// with a seed, caching per seed.
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
        expect(observed(output)).toBe(observed(program));
        expect(observed(program)).toBe('"licensed"');
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
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain(`if (${value}) {`);
        }
    });

    it("keeps tests when the lock is used outside them, or the storage object is read with a computed key", async () => {
        for (const use of ["var seen = G.H.h(0, false, 3);", 'var key = "H";\nvar seen = G[key].h(0, false, 3);']) {
            const program = `${runtime()}${gate()}${use}\n`;
            const output = await run(program);
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain(`if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} ||`);
        }
    });

    it("keeps tests whose hash reads nothing of the host", async () => {
        const program = `${runtime('"fixed text"')}${gate()}`;
        const output = await run(program);
        expect(observed(output)).toBe(observed(program));
        expect(output).toContain(`if (G.H.h(0, false, 5) === ${hash(LICENSED, 5)} ||`);
    });

    it("keeps tests with a comparison that isn't a lock call with literal arguments", async () => {
        for (const first of ["G.H.h(0, false, seed) === 1", "G.H.h(0, false, 5) === other", "other === 1"]) {
            const program = `var seed = 5, other = 1;\n${runtime()}${gate(first)}`;
            const output = await run(program);
            expect(observed(output)).toBe(observed(program));
            expect(output).toContain(`if (${first} ||`);
        }
    });
});
