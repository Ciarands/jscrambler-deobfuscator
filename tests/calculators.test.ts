import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const RUN: Run = { timers: true };

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "calculators", "calculators-bound"] })).code;

const sameBehaviour = async (program: string): Promise<string> => {
    const output = await run(program);
    expect(observe(output, RUN)).toBe(observe(program, RUN));
    return output;
};

// A builder returns a selector, which stores the case, and the calculation, which switches on it over its arguments.
const calculator = ({ extra = "" } = {}) => `
function G() {}
G.K = function (I) {
  return {
    calc: function () {
      var r, a = arguments;
      switch (I) {
        case 0: r = a[0] - a[1]; break;
        case 1: r = a[1] << a[0]; break;
        case 2: r = a[0] + a[1] * a[2]; break;
        case 3: r = a[2]; break;
        case 4: r = (a[0] - a[1]) * a[2]; break;
        case 5: r = a[0] || a[1]; break;
      }
      return r;
    },
    sel: function (p) { I = p; }${extra}
  };
}();
G.c = function () { return typeof G.K.calc === "function" ? G.K.calc.apply(G.K, arguments) : G.K.calc; };
G.s = function () { return typeof G.K.sel === "function" ? G.K.sel.apply(G.K, arguments) : G.K.sel; };
`;

const later = (body: string, extra = "", prelude = ""): string => `${calculator({ extra })}${prelude}setTimeout(function () {\n  var S = [arguments];\n${body}\n});\n`;

describe("calculators", () => {
    it("replaces calculations after selector statements with the selected case", async () => {
        const output = await sameBehaviour(later("  var x = 5;\n  G.K.sel(0);\n  S[1] = G.K.calc(10, 3);\n  G.s(2);\n  S[2] = G.K.calc(x, 2, S[1]);\n  result = [S[1], S[2]];"));
        expect(output).toContain("S[1] = 10 - 3;");
        expect(output).toContain("S[2] = x + 2 * S[1];");
        expect(output).not.toMatch(/G\.K\.(calc|sel)\(|G\.[cs]\(/);
    });

    it("replaces wrapper calls and selector calls passed as the last argument", async () => {
        const output = await sameBehaviour(later('  var x = 4;\n  result = [G.c(0, "101", G.s(1)), G.c(x, 1, G.s(0)), G.c(1, 2, G.s(3)), G.c(1, 2, G.s(9))];'));
        expect(output).toContain('result = ["101" << 0, x - 1, void 0, void 0];');
    });

    it("replaces a calculation in an array destructuring target, after the array literal it destructures", async () => {
        const output = await sameBehaviour(later("  var o = [0, 0, 0];\n  var p;\n  G.K.sel(0);\n  [p, o[G.K.calc(3, 1)]] = [G.K.calc(5, 1), 7];\n  result = [o, p];"));
        expect(output).toContain("[p, o[3 - 1]] = [5 - 1, 7];");
        // A store into a member before it may run a setter; a right side that isn't an array literal may iterate with code.
        for (const body of [
            "  var o = [0, 0, 0];\n  G.K.sel(0);\n  [o[0], o[G.K.calc(3, 1)]] = [1, 7];\n  result = [o];",
            "  var o = [0, 0, 0];\n  var p;\n  G.K.sel(0);\n  var src = [1, 7];\n  [p, o[G.K.calc(3, 1)]] = src;\n  result = [o, p];",
        ]) {
            expect(await sameBehaviour(later(body))).toContain("G.K.calc(3, 1)");
        }
    });

    it("drops the prelude's selector calls once no calculation that stays can read them", async () => {
        const resolved = await sameBehaviour(`${calculator()}G.K.sel(0);\nvar x = G.K.calc(5, 3);\nsetTimeout(function () { result = [x]; });\n`);
        expect(resolved).toContain("var x = 5 - 3;");
        expect(resolved).not.toContain("G.K.sel(0);");
        // A calculation the pass can't replace (a call that may reach the selector comes between) keeps them.
        const kept = await sameBehaviour(
            `${calculator()}G.K.sel(0);\nhost();\nvar y = G.K.calc(5, 3);\nsetTimeout(function () { result = [y]; });\n`.replace("function G() {}", "function G() {}\nvar host = function () {};")
        );
        expect(kept).toContain("G.K.sel(0);");
    });

    it("reads arguments beyond those passed as undefined", async () => {
        const output = await sameBehaviour(later("  G.s(3);\n  result = [G.c(1, 2)];"));
        expect(output).toContain("result = [void 0];");
    });

    it("keeps calculations when a call between them and the selector call may change the selector", async () => {
        const output = await sameBehaviour(later("  function f() { G.s(2); return 1; }\n  G.s(0);\n  result = f() + G.c(5, 1, 1);"));
        expect(output).toContain("G.s(0);");
        expect(output).toContain("result = f() + G.c(5, 1, 1);");
    });

    it("passes decided ifs between the selector call and the calculation, through the branch they take", async () => {
        // Answered detectors leave `if (!false) {...}` behind; the branch taken may hold the nearest selector call.
        const decided = "  G.s(1);\n  if (false) { G.s(4); } else { var y = 2; }\n  if (!0) { G.s(0); }\n  S[1] = G.c(10, 3);\n  if (0) { G.s(4); }\n  S[2] = G.c(10, y);";
        const output = await sameBehaviour(later(`${decided}\n  result = [S[1], S[2]];`));
        expect(output).toContain("S[1] = 10 - 3;");
        expect(output).toContain("S[2] = 10 - y;");
        // An undecided test may select another case.
        const open = await sameBehaviour(later("  var x = Date.now() > 0;\n  G.s(1);\n  if (x) { G.s(0); }\n  result = [G.c(10, 3)];"));
        expect(open).toContain("result = [G.c(10, 3)];");
    });

    it("passes calls of runtime functions that can't reach a selector call", async () => {
        // An environment check touching only its builder's own state, through local functions.
        const check = 'G.D = function () {\n  var code;\n  function probe() { if (!code) code = "j-1"; }\n  return { check: function () { if (!code) probe(); return code; } };\n}();\n';
        const output = await sameBehaviour(later("  G.s(0);\n  result = [G.D.check(), G.c(5, 1)];", "", check));
        expect(output).toContain("result = [G.D.check(), 5 - 1];");
    });

    it("keeps calculations after calls of runtime functions that may reach a selector call", async () => {
        const cases = [
            "G.D = function () { return { check: function () { G.s(2); return 1; } }; }();\n", // a member call of the selector's wrapper
            "G.D = function () { function f() { G.s(2); } return { check: function () { f(); return 1; } }; }();\n", // through a local function
            "G.D = function () { return { check: function () { new (function () { G.s(2); })(); return 1; } }; }();\n", // a constructor call
            "G.D = function () { function t() { G.s(2); return 1; } return { check: function () { return t`x`; } }; }();\n", // a tagged template
        ];
        for (const prelude of cases) {
            const output = await sameBehaviour(later("  G.s(0);\n  result = [G.D.check(), G.c(5, 1, 1)];", "", prelude));
            expect(output).toContain("result = [G.D.check(), G.c(5, 1, 1)];");
        }
    });

    it("keeps calculations after a store that may run a setter", async () => {
        const output = await sameBehaviour(later("  var o = { set v(x) { G.s(2); } };\n  G.s(0);\n  o.v = 1;\n  result = G.c(5, 1, 1);"));
        expect(output).toContain("result = G.c(5, 1, 1);");
    });

    it("keeps a selector call whose value a setter after its calculation may read", async () => {
        const body = "  var o = { set v(x) { S[2] = G.c(3, 4); } };\n  G.s(1);\n  S[1] = G.c(1, 2);\n  o.v = 0;\n  G.s(0);\n  S[3] = G.c(7, 2);\n  result = [S[1], S[2], S[3]];";
        const output = await sameBehaviour(later(body));
        expect(output).toContain("G.s(1);\n  S[1] = 2 << 1;");
    });

    it("passes getters and conversions between the selector call and the calculation (model 8)", async () => {
        const output = await sameBehaviour(later("  var o = { get v() { return 2; }, valueOf: function () { return 3; } };\n  G.s(0);\n  S[1] = o.v * -o + G.c(5, 1);\n  result = S[1];"));
        expect(output).toContain("S[1] = o.v * -o + (5 - 1);");
    });

    it("takes model 8 at its word: a getter that calls the selector is the assumption's boundary", async () => {
        const body = "  var o = { get v() { G.s(2); return 1; } };\n  G.s(0);\n  result = o.v + G.c(5, 1, 1);";
        // The getter's selector call decides the case: 1 + (5 + 1 * 1). Model 8 says that doesn't happen, so the
        // calculation becomes the case the visible selector call chose: 1 + (5 - 1).
        expect(observe(later(body), RUN)).toBe("7");
        const output = await run(later(body));
        expect(output).toContain("result = o.v + (5 - 1);");
        expect(observe(output, RUN)).toBe("5");
    });

    it("keeps calculations whose selector value isn't a constant", async () => {
        const output = await sameBehaviour(later("  var n = S[0][0] ? 1 : 0;\n  G.s(n);\n  result = G.c(3, 4);"));
        expect(output).toContain("result = G.c(3, 4);");
    });

    it("binds the arguments first when one would be read after a conversion that may run code", async () => {
        const body = "  var z = 2;\n  var o = { valueOf: function () { z = 100; return 7; } };\n  G.s(4);\n  result = G.c(o, 1, z);";
        // The calculation reads z before o's valueOf changes it: (7 - 1) * 2.
        expect(observe(later(body), RUN)).toBe("12");
        const output = await sameBehaviour(later(body));
        expect(output).toContain("result = ((p0, p1) => (p0 - 1) * p1)(o, z);");
        // Also when a getter argument returns the object whose conversion writes z.
        const getter = "  var z = 2;\n  var w = { valueOf: function () { z = 100; return 7; } };\n  var o = { get v() { return w; } };\n  G.s(4);\n  result = G.c(o.v, 1, z);";
        expect(observe(later(getter), RUN)).toBe("12");
        expect(await sameBehaviour(later(getter))).toContain("result = ((p0, p1) => (p0 - 1) * p1)(o.v, z);");
        // A selector call passed among the arguments isn't bound: the case it chose is already in.
        const selecting = "  var z = 2;\n  var o = { valueOf: function () { z = 100; return 7; } };\n  result = G.c(o, 1, z, G.s(4));";
        expect(await sameBehaviour(later(selecting))).toContain("result = ((p0, p1) => (p0 - 1) * p1)(o, z);");
        // No other function names z or the slot array: whatever a conversion runs, they read the same after it.
        const stable = await sameBehaviour(later("  var z = 2;\n  S[2] = 3;\n  var o = { valueOf: function () { return 7; } };\n  G.s(4);\n  result = [G.c(o, 1, z), G.c(o, 1, S[2])];"));
        expect(stable).toContain("result = [(o - 1) * z, (o - 1) * S[2]];");
        // An argument that only ever holds primitives converts without running code, so a later one reads the same.
        const primitive = await sameBehaviour(
            later("  var z = 2;\n  var touch = function () { z = 5; };\n  var n = 3 * 2;\n  var m = 3 * 2;\n  m = touch;\n  G.s(4);\n  result = [G.c(n, 1, z), G.c(m, 1, z)];")
        );
        expect(primitive).toContain("result = [(n - 1) * z, ((p0, p1) => (p0 - 1) * p1)(m, z)];");
    });

    it("leaves a bound calculation to the passes after it, which don't know its parameters", async () => {
        const program = later("  var z = 2;\n  var o = { valueOf: function () { z = 100; return 7; } };\n  G.s(4);\n  result = G.c(o, 1, z);");
        const { code } = await deobfuscate(program, { passes: ["emulate", "calculators", "calculators-bound", "cleanup", "simplify", "unminify"] });
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("((p0, p1) => (p0 - 1) * p1)(o, z)");
    });

    it("binds the arguments when the first may hold an object: a global, a parameter, a logical or conditional choice", async () => {
        const hook = "  var z = 2;\n  var o = { valueOf: function () { z = 100; return 7; } };\n";
        const bodies = [
            `${hook}  globalThis.g = o;\n  G.s(4);\n  result = G.c(g, 1, z);`,
            `${hook}  function f(p) { G.s(4); return G.c(p, 1, z); }\n  result = f(o);`,
            `${hook}  var n = 0 || o;\n  G.s(4);\n  result = G.c(n, 1, z);`,
            `${hook}  var n = z ? o : 1;\n  G.s(4);\n  result = G.c(n, 1, z);`,
        ];
        for (const body of bodies) {
            const program = later(body, "", "var g = 6;\n");
            expect(observe(program, RUN)).toBe("12");
            await sameBehaviour(program);
        }
    });

    it("reads parameters after a conversion only where no arguments object can write them", async () => {
        // The valueOf writes the second parameter through the `arguments` object it was handed, then returns 7.
        const object = "  var o = { valueOf: function () { this.args[1] = 100; return 7; } };\n";
        const strict = `${object}  function f(o, p) { "use strict"; o.args = arguments; G.s(4); return G.c(o, 1, p); }\n  var g = (o, p) => { G.s(4); return G.c(o, 1, p); };\n  result = [f(o, 2), g(o, 2)];`;
        // Strict arguments objects don't map the parameters; an arrow has none.
        const output = await sameBehaviour(later(strict));
        expect(output).not.toContain("G.c(");
        expect(output).not.toContain("p0");
        expect(output).toContain("return (o - 1) * p;");
        // A sloppy function's does: the calculation reads p before the write, (7 - 1) * 2.
        const sloppy = `${object}  function f(o, p) { o.args = arguments; G.s(4); return G.c(o, 1, p); }\n  result = f(o, 2);`;
        expect(observe(later(sloppy), RUN)).toBe("12");
        expect(await sameBehaviour(later(sloppy))).toContain("return ((p0, p1) => (p0 - 1) * p1)(o, p);");
        // A strict parameter another function names may change during the conversion too.
        const closure =
            '  var o = { valueOf: function () { this.set(); return 7; } };\n  function f(o, p) { "use strict"; o.set = function () { p = 100; }; G.s(4); return G.c(o, 1, p); }\n  result = f(o, 2);';
        expect(observe(later(closure), RUN)).toBe("12");
        expect(await sameBehaviour(later(closure))).toContain("return ((p0, p1) => (p0 - 1) * p1)(o, p);");
    });

    it("puts getter arguments in when each is read once, in the order they were passed", async () => {
        const output = await sameBehaviour(later("  var n = 0;\n  var o = { get p() { n++; return 10; } };\n  G.s(0);\n  S[1] = G.c(o.p, 1);\n  result = [S[1], n];"));
        expect(output).toContain("S[1] = o.p - 1;");
    });

    it("keeps calculations that would read a getter argument out of turn", async () => {
        // Case 1 reads its second argument first: x, which the first argument's getter sets.
        const body = "  var x = 1;\n  var o = { get p() { x = 5; return 1; } };\n  G.s(1);\n  result = G.c(o.p, x);";
        expect(observe(later(body), RUN)).toBe("10");
        const output = await sameBehaviour(later(body));
        expect(output).toContain("result = G.c(o.p, x);");
    });

    it("keeps only the selector calls that calculations which stay read", async () => {
        // S[2] stays (its getter argument would be read out of turn) and reads G.s(1); nothing reads G.s(0)'s value.
        const body =
            "  function f() { return 1; }\n  var x = 1;\n  var o = { get p() { x = 5; return 1; } };\n  G.s(1);\n  S[2] = G.c(o.p, x);\n  G.s(0);\n  S[3] = G.c(9, 4);\n  f();\n  result = [S[2], S[3]];";
        const output = await sameBehaviour(later(body));
        expect(output).toContain("G.s(1);\n  S[2] = G.c(o.p, x);");
        expect(output).toContain("  S[3] = 9 - 4;\n  f();");
        expect(output).not.toContain("G.s(0)");
    });

    it("keeps calculations that would skip or drop a getter argument", async () => {
        // Case 5 reads its second argument only when the first is falsy; case 0 never reads its third; no case is 9.
        const body =
            "  var n = 0;\n  var o = { get p() { n++; return 2; } };\n  G.s(5);\n  S[1] = G.c(1, o.p);\n  G.s(0);\n  S[2] = G.c(1, 2, o.p);\n  G.s(9);\n  S[3] = G.c(o.p);\n  result = [S[1], S[2], S[3], n];";
        const output = await sameBehaviour(later(body));
        expect(output).toContain("S[1] = G.c(1, o.p);");
        expect(output).toContain("S[2] = G.c(1, 2, o.p);");
        expect(output).toContain("S[3] = G.c(o.p);");
    });

    it("keeps calculations with a getter argument evaluated before the selector call", async () => {
        // Put in, the getter would run after the selector call, and its own selector call would stick.
        const body = "  function f() { return 1; }\n  var o = { get p() { G.s(2); return 9; } };\n  S[1] = G.c(o.p, 1, G.s(0));\n  f();\n  S[2] = G.c(4, 1, 1);\n  result = [S[1], S[2]];";
        const output = await sameBehaviour(later(body));
        expect(output).toContain("S[1] = G.c(o.p, 1, G.s(0));");
    });

    it("keeps calculations whose arguments may have effects", async () => {
        // Case 0 doesn't use the third argument, but its call still runs (before the selector call).
        const output = await sameBehaviour(later("  var n = 0;\n  function f() { n++; return 1; }\n  result = [G.c(5, 1, f(), G.s(0)), n];"));
        expect(output).toContain("result = [G.c(5, 1, f(), G.s(0)), n];");
    });

    it("keeps the selector calls a remaining calculation may read, and removes overwritten ones", async () => {
        const body = "  function f() { return 1; }\n  G.s(1);\n  S[1] = G.c(1, 2);\n  G.s(0);\n  S[2] = G.c(7, 2);\n  f();\n  S[3] = G.c(3, 1);\n  G.s(1);\n  result = [S[1], S[2], S[3]];";
        const output = await sameBehaviour(later(body));
        expect(output).not.toContain("G.s(1);\n  S[1]");
        expect(output).toContain("S[1] = 2 << 1;");
        expect(output).toContain("G.s(0);\n  S[2] = 7 - 2;");
        expect(output).toContain("S[3] = G.c(3, 1);");
    });

    it("keeps the selector calls when a reference to the calculator escapes", async () => {
        const output = await sameBehaviour(later("  var c = G.K;\n  G.s(1);\n  S[1] = G.c(1, 2);\n  result = [S[1], c.calc(4, 5)];"));
        expect(output).toContain("G.s(1);\n  S[1] = 2 << 1;");
    });

    it("leaves calculators whose state something else writes", async () => {
        const output = await sameBehaviour(later("  G.s(0);\n  S[1] = G.c(3, 4);\n  G.K.reset();\n  result = [S[1], G.c(3, 4)];", ",\n    reset: function () { I = 1; }"));
        expect(output).toContain("S[1] = G.c(3, 4);");
    });

    it("keeps every selector call when a computed access to the storage object may reach the calculator later", async () => {
        // The value is only called, which would be harmless in prelude-only code: here it runs after the prelude.
        const output = await sameBehaviour(later('  var k = "c";\n  var held = G[k];\n  G.s(1);\n  S[1] = G.c(1, 2);\n  result = [S[1], held(4, 5)];'));
        expect(output).toContain("G.s(1);\n  S[1] = 2 << 1;");
    });

    it("removes the selector calls once every calculation after the prelude is gone", async () => {
        // A computed access in prelude-only code whose value is only called there can't reach code that runs later.
        const prelude = 'function look(n) { var v; v = G[n]; return v; }\nvar early = look("c")(5, 1);\n';
        const output = await sameBehaviour(later("  function f() { return 1; }\n  G.s(0);\n  S[1] = G.c(3, 1);\n  f();\n  result = [S[1], early];", "", prelude));
        expect(output).toContain("S[1] = 3 - 1;");
        expect(output).not.toContain("G.s(0)");
    });

    it("keeps the selector calls when a block function's computed access to the storage object may run later (Annex B)", async () => {
        // Calls reach `look` through the binding Annex B gives it outside its block, not through its block's own.
        const prelude = '{ function look(n) { var v; v = G[n]; return v; } }\nvar early = look("c")(5, 1);\n';
        const output = await sameBehaviour(later('  G.s(1);\n  S[1] = G.c(1, 2);\n  result = [S[1], look("c")(4, 5)];', "", prelude));
        expect(output).toContain("G.s(1);");
    });

    it("keeps the prelude's selector calls, which its own calculations may read", async () => {
        const prelude = "function f() { return 1; }\nG.s(2);\nf();\nvar early = G.c(1, 2, 3);\n";
        const output = await sameBehaviour(later("  G.s(0);\n  result = [G.c(3, 1), early];", "", prelude));
        expect(output).toContain("result = [3 - 1, early];");
        expect(output).toContain("G.s(2);");
    });

    it("keeps calculations whose methods may be replaced after the prelude", async () => {
        const output = await sameBehaviour(later("  G.K.calc = function () { return 42; };\n  G.s(0);\n  result = G.c(3, 1);"));
        expect(output).toContain("result = G.c(3, 1);");
    });
});

describe("calculators in the whole pipeline", () => {
    it("replaces calculations whose arguments become plain parameters once the arguments array goes", async () => {
        // `S[0][1]` read before `S[0][0]` may be a getter read out of turn; as parameters they are plain reads.
        const program = `${calculator()}function f(p, q) {\n  var S = [arguments];\n  G.K.sel(1);\n  return G.K.calc(S[0][0], S[0][1]);\n}\nsetTimeout(function () { result = [f(2, 3), f(1, 8)]; });\n`;
        const { code } = await deobfuscate(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("return q << p;");
    });

    it("binds arguments only once arguments arrays are gone, so those that become plain parameters go in directly", async () => {
        // Before, `S[0][1]` would be read after converting `S[0][0]`; as a strict function's parameters they read the same.
        const program = `${calculator()}function f(p, q) {\n  "use strict";\n  var S = [arguments];\n  G.K.sel(4);\n  return G.K.calc(S[0][0], 1, S[0][1]);\n}\nsetTimeout(function () { result = [f(2, 3), f({ valueOf: function () { return 5; } }, 8)]; });\n`;
        const { code } = await deobfuscate(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("return (p - 1) * q;");
    });
});
