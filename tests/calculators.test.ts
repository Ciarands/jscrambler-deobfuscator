import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

/** What a script leaves in `result`; `setTimeout` callbacks (code after the prelude) run once it has finished. */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(source, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

const run = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "calculators"] })).code;

/** The program and its deobfuscation leave the same result; returns the deobfuscation. */
const sameBehaviour = async (program: string): Promise<string> => {
    const output = await run(program);
    expect(observed(output)).toBe(observed(program));
    return output;
};

// jscrambler's shape: a builder returns a selector, which stores the case to compute, and the calculation, which
// switches on it over its arguments. `G.c` and `G.s` are the runtime's wrappers of the two.
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

/** The calculator, `prelude` code, and `body` as code that runs after the prelude (in a function with a slot array `S`). */
const later = (body: string, extra = "", prelude = ""): string => `${calculator({ extra })}${prelude}setTimeout(function () {\n  var S = [arguments];\n${body}\n});\n`;

describe("calculators", () => {
    it("replaces calculations after selector statements with the selected case", async () => {
        const output = await sameBehaviour(later("  var x = 5;\n  G.K.sel(0);\n  S[1] = G.K.calc(10, 3);\n  G.s(2);\n  S[2] = G.K.calc(x, 2, S[1]);\n  result = [S[1], S[2]];"));
        expect(output).toContain("S[1] = 10 - 3;");
        expect(output).toContain("S[2] = x + 2 * S[1];");
        // Every calculation is gone: the selector calls only stored what nothing reads any more.
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
        // An environment check like jscrambler's: it only touches its builder's own state, through local functions.
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
        expect(observed(later(body))).toBe("7");
        const output = await run(later(body));
        expect(output).toContain("result = o.v + (5 - 1);");
        expect(observed(output)).toBe("5");
    });

    it("keeps calculations whose selector value isn't a constant", async () => {
        const output = await sameBehaviour(later("  var n = S[0][0] ? 1 : 0;\n  G.s(n);\n  result = G.c(3, 4);"));
        expect(output).toContain("result = G.c(3, 4);");
    });

    it("keeps calculations whose arguments would be read after a conversion that may run code", async () => {
        const body = "  var z = 2;\n  var o = { valueOf: function () { z = 100; return 7; } };\n  G.s(4);\n  result = G.c(o, 1, z);";
        // The calculation reads z before o's valueOf changes it: (7 - 1) * 2.
        expect(observed(later(body))).toBe("12");
        const output = await sameBehaviour(later(body));
        expect(output).toContain("result = G.c(o, 1, z);");
    });

    it("puts getter arguments in when each is read once, in the order they were passed", async () => {
        const output = await sameBehaviour(later("  var n = 0;\n  var o = { get p() { n++; return 10; } };\n  G.s(0);\n  S[1] = G.c(o.p, 1);\n  result = [S[1], n];"));
        expect(output).toContain("S[1] = o.p - 1;");
    });

    it("keeps calculations that would read a getter argument out of turn", async () => {
        // Case 1 reads its second argument first: x, which the first argument's getter sets.
        const body = "  var x = 1;\n  var o = { get p() { x = 5; return 1; } };\n  G.s(1);\n  result = G.c(o.p, x);";
        expect(observed(later(body))).toBe("10");
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
