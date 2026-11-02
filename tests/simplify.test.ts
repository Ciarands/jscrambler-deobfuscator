import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const PROGRAM = `
var log = [];
function t(x) { log.push(x); return x; }
function shadowed(undefined) { return void 0 === undefined; }
function branches() {
  var k = 3;
  if (k > 2) { t("then"); } else { var hidden = 1; t("else"); }
  t(typeof hidden);
  while (k < 0) { var looped = 1; }
  t(typeof looped);
  if ((t("effect"), 1) === (t("effect2"), 2)) t("no"); else t("yes");
  var o = { m: function () { return this === o; } };
  t((0, o.m)());
  t((t("s"), o).m());
  return early();
  t("dead");
  function early() { return t("hoisted"); }
}
function beforeInit() { t(x); var x = 5; return x; }
t(shadowed(5));
branches();
t(beforeInit());
result = log;
`;

const RUN: Run = { globals: () => ({ host: { flag: false } }) };

// Constants and `arguments` slots, judged in execution order (after unflattening), not source order.
const ORDERED = `
var log = [];
function t(x) { log.push(x); return x; }
function inverse() {
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 2: var k = "late"; s = 0; break;
    case 1: t(k); s = 2; break;
  }
}
function hoisting() {
  early();
  var c = 5;
  function early() { t(c); }
  t(c);
}
function slots() {
  var a = [arguments];
  a[3] = "x";
  a[4] = 1;
  a[4] = 2;
  if (host.flag) { a[5] = "y"; }
  t(a[3]);
  t(a[4]);
  t(a[5]);
}
function calledAfter() {
  var d = 7;
  function useD() { t(d); }
  useD();
}
inverse();
hoisting();
slots();
calledAfter();
result = log;
`;

// Places where a fold or hoist is only exact with care: each case behaves differently if done naively.
const REFERENCES = [
    "var log = [];",
    "function t(x) { log.push(x); return x; }",
    'function tag(strings, value) { return strings.raw.join("|") + ":" + String(strings[0]) + ":" + value; }',
    // A tagged template's literal is the tag's argument, not a string; an invalid escape has no cooked value.
    "t(tag`a${1 + 1}b`);",
    "t(tag`\\unicode`);",
    "var o = { x: 1, p: 1 };",
    '(t("w"), o).x = 2;',
    "t(o.x);",
    't(delete (t("d"), o).p);',
    't("p" in o);',
    // Indirect eval runs globally, direct eval in the caller's scope.
    'function evals() { (0, eval)("var leaked = 1"); return typeof leaked; }',
    "t(evals());",
    "t(typeof leaked);",
    // `typeof (0, x)` reads x; `typeof x` doesn't.
    "try { t(typeof (0, undeclared)); } catch (e) { t(e.name); }",
    'try { t(typeof (t("q"), undeclared)); } catch (e) { t(e.name); }',
    // Only own names are global constants.
    "t(typeof constructor);",
    // A dead loop's lexical init stays scoped to itself.
    'let i = "outer";',
    'for (let i = t("init"); false;) {}',
    "for (let j = 0; false;) {}",
    "t(i);",
    // A local: a script global spelled as a property (`.sh`) may be the global object's, so it isn't a constant.
    "function shorthand() { var sh = 3; return { sh }.sh; }",
    "t(shorthand());",
    // Lexical names of unreachable code stay bound (in their dead zone), not resolved to an outer binding.
    "function lexicalDead() {",
    "  function peek() { try { return typeof late; } catch (e) { return e.name; } }",
    "  return peek();",
    "  let late = 1;",
    "  class Gone {}",
    "}",
    "t(lexicalDead());",
    'var late = "outer";',
    // `arguments` slots moved by a method, by `length` or written by destructuring aren't constants.
    "function slotsMoved() {",
    "  var a = [arguments];",
    '  a[1] = "x";',
    "  a.splice(1, 1);",
    "  t(a[1]);",
    "  var b = [arguments];",
    '  b[1] = "y";',
    "  b.length = 0;",
    "  t(b[1]);",
    "  var c = [arguments];",
    '  c[2] = "z";',
    '  [c[2]] = ["w"];',
    "  t(c[2]);",
    "}",
    "slotsMoved();",
    "result = log;",
].join("\n");

describe("simplify", () => {
    it("folds, decides branches and drops dead code without changing behaviour", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["simplify", "normalize"] });
        expect(observe(code, RUN)).toBe(observe(PROGRAM, RUN));
        expect(code).not.toContain(`t("dead")`);
        expect(code).not.toContain(`t("else")`);
        expect(code).toContain(`t("effect");\n  t("effect2");\n  t("yes");`);
        expect(code).toContain("var hidden;");
        expect(code).toContain("var looped;");
        // A read before the initializer runs is not a constant use.
        expect(code).toContain("t(x);");
    });

    it("decodes base64 literals the host's atob turns into printable text, not binary, invalid, shadowed or extra-argument ones, nor calls of other functions", async () => {
        const program =
            'var out = [atob("bmF2aWdhdG9y"), atob("tNmJdQ=="), (function (atob) { return atob("eA=="); })(function (s) { return s + "!"; })];\ntry { out.push(atob("*")); } catch (e) { out.push(e.name); }\nvar hits = 0;\nout.push(atob("eA==", hits++), hits, String("eA=="));\nresult = out;\n';
        const { code } = await deobfuscate(program, { passes: ["simplify"] });
        const run: Run = { globals: () => ({ host: { flag: false }, atob }) };
        expect(observe(code, run)).toBe(observe(program, run));
        expect(code).toContain('"navigator"');
        for (const kept of ['atob("tNmJdQ==")', 'atob("eA==")', 'atob("*")']) expect(code).toContain(kept);
    });

    it("propagates constants and arguments slots only where they are already set", async () => {
        const { code } = await deobfuscate(ORDERED, { passes: ["unflatten", "simplify", "normalize"] });
        expect(observe(code, RUN)).toBe(observe(ORDERED, RUN));
        expect(code).toContain(`t("x");`);
        expect(code).toContain("t(5);");
        expect(code).toContain("t(7);");
        // Read before it runs (execution order), inside a hoisted function called earlier, written twice or
        // conditionally: not.
        expect(code).toContain("t(k);");
        expect(code).toContain("t(c);");
        expect(code).toContain("t(a[4]);");
        expect(code).toContain("t(a[5]);");
    });

    it("keeps reference semantics: tags, writes, delete, eval, typeof, lexical scopes", async () => {
        const { code } = await deobfuscate(REFERENCES, { passes: ["simplify", "normalize"] });
        expect(observe(code, RUN)).toBe(observe(REFERENCES, RUN));
        expect(code).toContain("tag`a${2}b`");
        expect(code).toContain("(0, eval)(");
        expect(code).toContain("let late, Gone;");
        expect(code).toContain("sh: 3");
    });

    it("leaves export specifiers naming their binding", async () => {
        const { code } = await deobfuscate("const x = 5;\nexport { x };\nexport const y = x + 1;\n", { passes: ["simplify", "normalize"] });
        expect(code).toContain("export { x }");
        expect(code).toContain("export const y = 6");
    });

    it("keeps a dead block function's name function-wide only in sloppy code (Annex B), not in strict code", async () => {
        const strict = [
            '"use strict";\nvar result, r;\nif (false) { function f() { return 1; } }\ntry { r = f; } catch (e) { r = "threw " + e.name; }\nresult = r;\n',
            '"use strict";\nvar result, r;\nwhile (false) { function f() { return 1; } }\ntry { r = f; } catch (e) { r = "threw " + e.name; }\nresult = r;\n',
            'globalThis.f = "global";\nfunction g() { "use strict"; function h() { return f; } return h(); { function f() {} } }\nresult = g();\n',
        ];
        for (const program of strict) {
            const { code } = await deobfuscate(program, { passes: ["simplify"] });
            expect(observe(code)).toBe(observe(program));
            expect(code).not.toContain("var f");
        }
        const sloppy = [
            "function g() { if (false) { function f() {} } return typeof f; }\nresult = g();\n",
            'globalThis.f = "global";\nfunction g() { function h() { return f; } return h(); { function f() {} } }\nresult = g();\n',
        ];
        for (const program of sloppy) {
            const { code } = await deobfuscate(program, { passes: ["simplify"] });
            expect(observe(code)).toBe(observe(program));
            expect(code).toContain("var f;");
        }
    });

    it("keeps a decided if's function in a block of its own, and a dead labelled function hoisted", async () => {
        const programs = [
            // An `if` clause's function binds in a block of its own (Annex B): not hoisted in the block around the `if`.
            "function g() { { try { f(); } catch (e) { return e.name; } if (1) function f() {} } }\nresult = g();\n",
            "function g() { { try { f(); } catch (e) { return e.name; } if (0); else function f() {} } }\nresult = g();\n",
            // A labelled function in a block is that block's.
            "function g() { { try { f(); } catch (e) { return e.name; } if (1) { l: function f() {} } } return typeof f; }\nresult = g();\n",
            // A labelled function is hoisted as a plain one is, also after a return.
            "function g() { var r = typeof f; return r; l: m: function f() {} }\nresult = g();\n",
        ];
        for (const program of programs) {
            const { code } = await deobfuscate(program, { passes: ["simplify"] });
            expect(observe(code), program).toBe(observe(program));
        }
    });

    it("leaves a dead class static block's vars to the block", async () => {
        const shapes = ['if (0) { class K { static { var x = "inner"; } } }', 'while (0) try { class K { static { var x = "inner"; } } } finally {}'];
        for (const dead of shapes) {
            const program = `var x = "outer";\nfunction h() { x = "changed"; }\nfunction g() { var r = x; ${dead} r += "/" + x; result = r; }\nh();\ng();\n`;
            const { code } = await deobfuscate(program, { passes: ["simplify"] });
            expect(observe(code), program).toBe(observe(program));
            expect(code).not.toContain("var x;");
        }
    });
});
