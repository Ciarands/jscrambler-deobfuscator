import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

// Cyclic-array states: rows of a generated table that point at each other, compared by identity.
const PROGRAM = `
function G() {}
G.T = (function () {
  var r = [[], [], []];
  r[0][0] = r[1]; r[0][1] = r[2];
  r[1][0] = r[2]; r[1][1] = r[0];
  r[2][0] = r[0]; r[2][1] = r[1];
  return r;
})();
function f(c) {
  var log = [];
  var s = G.T[0][0];
  for (; s !== G.T[1][1];) switch (s) {
    case G.T[2][1]:
      log.push("b");
      s = c ? G.T[0][1] : G.T[2][0];
      break;
    case G.T[1][0]:
      log.push("c");
      s = G.T[1][1];
      break;
  }
  return log;
}
// A transition that picks a row, then a column: (c ? T[0] : T[1])[1]. And a property that spells the state's name.
function g(c) {
  var log = [], o = { s: 0 };
  var s = G.T[0][0];
  for (; s !== G.T[1][1];) switch (s) {
    case G.T[2][1]:
      log.push("b");
      s = (c ? G.T[0] : G.T[1])[1];
      break;
    case G.T[1][0]:
      o.s += 1;
      log.push("c" + o.s);
      s = G.T[1][1];
      break;
  }
  return log;
}
result = [f(host.a), f(host.b), g(host.a), g(host.b)];
`;

const run = (code: string): string => {
    const context: Record<string, unknown> = { host: { a: true, b: false } };
    runInNewContext(code, context);
    return JSON.stringify(context.result);
};

describe("unflatten with runtime state keys", () => {
    it("unflattens machines whose states are table rows compared by identity", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["emulate", "unflatten"] });
        expect(code).not.toContain("switch");
        expect(run(code)).toBe(run(PROGRAM));
    });
});
