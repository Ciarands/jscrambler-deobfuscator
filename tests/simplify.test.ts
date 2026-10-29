import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

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

const run = (code: string): string => {
    const context: Record<string, unknown> = { host: { flag: false } };
    runInNewContext(code, context);
    return JSON.stringify(context.result);
};

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
    // Targets of assignment and delete keep their reference.
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
        expect(run(code)).toBe(run(PROGRAM));
        expect(code).not.toContain(`t("dead")`);
        expect(code).not.toContain(`t("else")`);
        // The opaque predicate is decided; its side effects stay, in order.
        expect(code).toContain(`t("effect");\n  t("effect2");\n  t("yes");`);
        // Hoisted names of dropped code stay declared.
        expect(code).toContain("var hidden;");
        expect(code).toContain("var looped;");
        // A read before the initializer runs is not a constant use.
        expect(code).toContain("t(x);");
    });

    it("propagates constants and arguments slots only where they are already set", async () => {
        const { code } = await deobfuscate(ORDERED, { passes: ["unflatten", "simplify", "normalize"] });
        expect(run(code)).toBe(run(ORDERED));
        // Written once, at the top of the function: a constant from there on.
        expect(code).toContain(`t("x");`);
        expect(code).toContain("t(5);");
        // A function declaration only called after the definition sees the constant too.
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
        expect(run(code)).toBe(run(REFERENCES));
        // Still folded inside the template's expressions.
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
});
