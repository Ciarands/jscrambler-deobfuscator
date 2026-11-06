import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import type { PassSelection } from "../src/index.js";
import { observe } from "./helpers.js";

// A direct eval leaves every reference in the scopes around it unresolved, also the program's own: each fixture has
// a use of its own code there (the evaluated code names nothing), which a pass counting only resolved ones misses.

// The timeout catches a broken probe loop that never ends.
const RUN = { timers: true, timeout: 2000 } as const;

const sameBehaviour = async (program: string, selection: PassSelection = {}): Promise<string> => {
    const { code } = await deobfuscate(program, selection);
    expect(observe(code, RUN)).toBe(observe(program, RUN));
    return code;
};

describe("direct eval: references the scope analysis leaves unresolved", () => {
    it("unflatten keeps a machine whose state a function calling eval reads", async () => {
        const program = `var seen = [];
function peek() { eval(""); seen.push(s); }
for (var s = 3; s !== 0;) {
  switch (s) {
    case 2: peek(); s = 0; break;
    case 3: peek(); s = 1; break;
    case 1: peek(); s = 2; break;
  }
}
result = seen;
`;
        expect(await sameBehaviour(program)).toContain("switch (s)");
    });

    it("cleanup keeps a definition a decoder probe reaches through its arguments object", async () => {
        // The write to `arguments[0]` changes `codes`: the probe looks up `zz`, not a permutation of `Pq`.
        const program = `function G() {}
G.Pq = function () { return "a,b,c"; };
G.zz = function () { return "d,e,f"; };
G.D = (function () {
  var probe = function (codes) {
    eval("");
    arguments[0] = [121, 121];
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
  var table = probe([79, 112])().split(",");
  return { get: function (i) { return table[i]; } };
})();
result = G.D.get(0);
`;
        expect(await sameBehaviour(program)).toContain("G.zz = ");
    });

    it("calculators keep the selector calls when a computed access in the prelude is handed out by a local", async () => {
        const program = `function G() {}
G.K = function (I) {
  return {
    calc: function () {
      var r, a = arguments;
      switch (I) {
        case 0: r = a[0] - a[1]; break;
        case 1: r = a[1] << a[0]; break;
      }
      return r;
    },
    sel: function (p) { I = p; }
  };
}();
G.c = function () { return typeof G.K.calc === "function" ? G.K.calc.apply(G.K, arguments) : G.K.calc; };
G.s = function () { return typeof G.K.sel === "function" ? G.K.sel.apply(G.K, arguments) : G.K.sel; };
var grab;
function look(n) { var v = G[n]; function never() { eval(""); } grab = v; return v; }
var early = look("c")(5, 1);
setTimeout(function () {
  var S = [arguments];
  G.s(0);
  S[1] = G.c(3, 1);
  result = [S[1], early, grab(3, 1)];
});
`;
        expect(await sameBehaviour(program, { passes: ["runtime", "calculators", "calculators-bound"] })).toContain("G.s(0);");
    });

    it("code-locks leave a lock whose holder array a function calling eval hands on", async () => {
        const program = `function G() {}
var log = [];
var h = [];
function tamper() { eval(""); var held = h; held[3].check = function () { return "tampered"; }; }
G.L = function () {
  var c = [arguments];
  c[6] = undefined;
  h[3] = {};
  h[3].check = function () {
    var d = [arguments];
    if (c[6]) { return 67; }
    log.push("checked");
    c[6] = 15;
    return 91;
  };
  return h[3];
}();
G.L.check();
setTimeout(function () { tamper(); log.push(G.L.check()); result = log; });
`;
        expect(await sameBehaviour(program, { passes: ["runtime", "code-locks"] })).toContain("log.push(G.L.check());");
    });
});
