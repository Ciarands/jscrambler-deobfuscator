import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { createLogger } from "../src/logger.js";
import { observe, type Run } from "./helpers.js";

const RUN: Run = { timers: true };

// A templated decoder whose table comes from a root function its name probe finds by trying permutations of "enc".
const decoder = ({ before = "", probeLoop = 'do { x = c.sort(function () { return 0.5 - Math.random(); }).join(""); found = G[x]; } while (!found);\n      return found;' } = {}) => `
function G() {}
function enc() { return "a,b,c,d,e,f"; }
G.enc = enc;
${before}
G.D = (function () {
  var Q = {
    m: (function (key) {
      var probe = function (codes) {
        var c = [];
        var i = 0;
        while (i < codes.length) { c[i] = String.fromCharCode(codes[i] + 1); i++; }
        var x, found;
      ${probeLoop}
      };
      var T = "", s = probe([100, 109, 98])();
      var j = 0;
      while (j < s.length) { T += s.charAt(j); j++; }
      T = T.split(",");
      var R = 0;
      var S = function (x) {
        if (R === 0 && x === 2) { R += 1; T.unshift.apply(T, T.splice(-2, 2).splice(0, 1)); }
        else if (R === 1 && x === 4) { R += 1; T.unshift.apply(T, T.splice(-3, 3).splice(0, 2)); }
        else { Q.m = L; return L(x); }
        return R;
      };
      var L = function (y) { return T[y]; };
      return S;
    })("k")
  };
  return Q;
})();
G.w = function () { return typeof G.D.m === "function" ? G.D.m.apply(G.D, arguments) : G.D.m; };
`;
const tail = "var flag = G.w(2) === 1 && G.w(4) === 2;\nsetTimeout(function () { result = [flag, G.w(0), G.w(3), G.w(2)]; });\n";
/** `tail` with `write` between the two stage calls, each in a statement of its own. */
const stagesAround = (write: string): string => `var a = G.w(2);\n${write}\nvar b = G.w(4);\nvar flag = a === 1 && b === 2;\nsetTimeout(function () { result = [flag, G.w(0), G.w(3), G.w(2)]; });\n`;
const run = async (program: string): Promise<string> => (await deobfuscate(program, { passes: ["runtime", "resolve-calls"] })).code;
/** The output, and whether a debug line includes `text`. */
const logged = async (program: string): Promise<{ code: string; has: (text: string) => boolean }> => {
    const lines: string[] = [];
    const { code } = await deobfuscate(program, { passes: ["runtime", "resolve-calls"], logger: createLogger("debug", (line) => lines.push(line)) });
    return { code, has: (text) => lines.some((line) => line.includes(text)) };
};

describe("string decoders built on the host", () => {
    it("builds the table with the probe's one possible key and answers later calls from it", async () => {
        const program = `${decoder()}${tail}`;
        const code = await run(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("var flag = (G.w(2), 1) === 1 && (G.w(4), 2) === 2;");
        expect(code).toMatch(/result = \[flag, "[a-f]", "[a-f]", "[a-f]"\]/);
    });

    it("refuses a probe whose key may be another key, or added by a computed write, a function, or through a literal holding G before the builder", async () => {
        for (const before of [
            "G.nce = enc;",
            'G["n" + "ec"] = enc;',
            "(function () { G.cen = enc; })();",
            'globalThis.holder = { q: G };\nholder.q.enc = function () { return "u,v,w,x,y,z"; };',
            'var held = [G];\nheld[0].enc = function () { return "u,v,w,x,y,z"; };',
        ]) {
            const program = `${decoder({ before })}${tail}`;
            const code = await run(program);
            expect(observe(code, RUN), before).toBe(observe(program, RUN));
            expect(code, before).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
        }
    });

    it("doesn't replace a probe when code before the builder may store G in a literal (an array or object holding it)", async () => {
        for (const before of ["function unused() { var held = [G]; held[0].nce = enc; }", "function unused() { var held = { q: G }; held.q.nce = enc; }"]) {
            const program = `${decoder({ before })}${tail}`;
            const lines: string[] = [];
            const { code } = await deobfuscate(program, { passes: ["runtime", "resolve-calls"], logger: createLogger("debug", (line) => lines.push(line)) });
            expect(observe(code, RUN), before).toBe(observe(program, RUN));
            expect(code, before).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
            expect(
                lines.some((line) => line.includes("a name probe isn't replaced: G is stored somewhere before the builder")),
                before
            ).toBe(true);
        }
    });

    it("refuses a probe when code before the builder writes G through a local or a local array's slot that may hold it", async () => {
        const write = 'x.enc = function () { return "u,v,w,x,y,z"; };';
        for (const before of [
            `(function () { var x = Math.random() < 2 ? G : 0; ${write} })();`,
            `(function () { var x = G || 0; ${write} })();`,
            `(function () { var y = (0, G), x; x = y; ${write} })();`,
            `(function () { var a = [0]; a[0] = Math.random() < 2 ? G : 0; var x = a[0]; ${write} })();`,
        ]) {
            const program = `${decoder({ before })}${tail}`;
            const lines = await logged(program);
            expect(observe(lines.code, RUN), before).toBe(observe(program, RUN));
            expect(lines.code, before).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
            expect(lines.has("a name probe isn't replaced: a write to G.enc before the builder may add a key it finds"), before).toBe(true);
        }
    });

    it("refuses a probe when a value that may be G goes where the walk doesn't follow it", async () => {
        for (const [use, reason] of [
            ["window.h = x;", "G is stored somewhere before the builder"],
            ["x.k();", "G.k() may run with G as this before the builder"],
            ['Object.defineProperty(x, "nce", { value: enc });', "G is handed to a call before the builder"],
        ]) {
            const before = `(function () { var x = Math.random() < 2 ? G : { k: function () {} }; ${use} })();`;
            const program = `${decoder({ before })}${tail}`;
            const lines = await logged(program);
            expect(observe(lines.code, RUN), use).toBe(observe(program, RUN));
            expect(lines.has(`a name probe isn't replaced: ${reason}`), use).toBe(true);
        }
    });

    it("follows G through the setup's own code, whose changes are the setup's keys, unless other code may run it", async () => {
        // The obfuscator's setup shape: G, or a builtin, picked into a slot of a local array, then given an accessor.
        const setup = `G[3] = (function () { return globalThis; })();
function S(g) {
  function def(m0, m1, m2, m3, m4, m5) {
    var s = [arguments];
    s[5] = "Property";
    s[1] = {};
    try {
      s[6] = (1, s[0][1])(s[0][0]);
      s[9] = [s[6], s[6].prototype][s[0][3]];
      s[8] = s[0][5] === 0 ? G : s[9];
      s[1].get = function () { return s[9][s[0][2]]; };
      s[0][0].Object["define" + s[5]](s[8], s[0][4], s[1]);
    } catch (e) {}
  }
  function str(x) { var p = [arguments]; return p[0][0].String; }
  def(g, str, "fromCharCode", 0, "c1", 0);
}
S(G[3]);`;
        const program = `${decoder({ before: setup })}${tail}`;
        const lines = await logged(program);
        expect(observe(lines.code, RUN)).toBe(observe(program, RUN));
        expect(lines.has("decoder G.D.m: built on the host; its name probe finds G.enc")).toBe(true);
        const again = `${decoder({ before: `${setup}\nsetTimeout(function () { S(G[3]); });` })}${tail}`;
        expect((await logged(again)).has("a name probe isn't replaced: G is handed to a call before the builder")).toBe(true);
    });

    it("refuses a probe that may leave its loop without a key", async () => {
        const probeLoop = 'while (true) { x = c.sort(function () { return 0.5 - Math.random(); }).join(""); found = G[x]; if (found) { return found; } if (x === "zzz") { break; } }';
        const code = await run(`${decoder({ probeLoop })}${tail}`);
        expect(code).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
    });

    it("settles nothing when code the walk can't follow may call the decoder before it settles", async () => {
        // `early()` freezes the decoder with its stages undone: its later calls read the table unshuffled.
        const program = `${decoder()}function early() { G.w(1); }\nearly();\n${tail}`;
        const code = await run(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
    });

    it("settles nothing when code that can tell its stage function from its lookup runs where the freeze isn't known", async () => {
        const program = `${decoder()}function late() { return 1; }\n${tail}late();\nsetTimeout(function () { result.push(G.D.m.name); });\n`;
        const code = await run(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
    });

    it("settles through writes of new global names, not of the global object's accessors", async () => {
        const before = "G.R = (function () { return globalThis; })();";
        const settled = `${decoder({ before })}${stagesAround("G.R.marker = 0;")}`;
        const settledCode = await run(settled);
        expect(observe(settledCode, RUN)).toBe(observe(settled, RUN));
        expect(settledCode).toMatch(/result = \[flag, "[a-f]", "[a-f]", "[a-f]"\]/);
        const program = `${decoder({ before })}${stagesAround("G.R.__proto__ = {};")}`;
        const lines: string[] = [];
        const { code } = await deobfuscate(program, { passes: ["runtime", "resolve-calls"], logger: createLogger("debug", (line) => lines.push(line)) });
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("result = [flag, G.w(0), G.w(3), G.w(2)]");
        expect(lines.some((line) => line.includes("it writes __proto__ of the global object, an accessor or a read-only property"))).toBe(true);
    });
});
