import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import type { Node } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";
import { deobfuscate } from "../src/index.js";
import { flatten, generate, mulberry32, runTrace } from "./fuzz/programs.js";

const unminify = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["unminify"] })).code;

/** Run a script; return what it recorded through `t(x)` and how it ended (its `result`, or the error it threw). */
const run = (code: string): unknown[] => {
    const trace: unknown[] = [];
    const context: Record<string, unknown> = { t: (x: unknown) => (trace.push(x), x) };
    try {
        runInNewContext(code, context, { timeout: 1000 });
        trace.push(["result", context["result"]]);
    } catch (error) {
        trace.push(["threw", error instanceof Error ? error.constructor.name : String(error)]);
    }
    return trace;
};

/** Output of the pass, after checking that it behaves as the input does (and that the input is a valid script). */
const sameBehaviour = async (input: string): Promise<string> => {
    const output = await unminify(input);
    const expected = run(input);
    expect(expected.at(-1)).not.toEqual(["threw", "SyntaxError"]);
    expect(run(output)).toEqual(expected);
    return output;
};

/** How many nodes of the output match `test`. */
const count = (code: string, test: (node: Node) => boolean): number => {
    let found = 0;
    traverse(parse(code), {
        enter(path) {
            if (test(path.node)) found++;
        },
    });
    return found;
};

const isBareBody = (node: Node): boolean => {
    const bodies: (Node | null)[] = [];
    if (node.type === "IfStatement") bodies.push(node.consequent, node.alternate?.type === "IfStatement" ? null : node.alternate);
    if (node.type === "ForStatement" || node.type === "WhileStatement" || node.type === "DoWhileStatement" || node.type === "ForInStatement" || node.type === "ForOfStatement") bodies.push(node.body);
    return bodies.some((body) => body !== null && body.type !== "BlockStatement");
};

/** A call of a function expression, directly or through `.apply`/`.call`. */
const isFunctionCall = (node: Node): boolean => node.type === "CallExpression" && (node.callee.type === "MemberExpression" ? node.callee.object : node.callee).type.endsWith("FunctionExpression");

const isNot = (node: Node): node is Extract<Node, { type: "UnaryExpression" }> => node.type === "UnaryExpression" && node.operator === "!";

describe("unminify", () => {
    it("puts bodies in blocks, merges else-if, turns bodiless for loops into while loops, and arrow sequences into blocks", async () => {
        const output = await sameBehaviour(`
            var n = 0;
            if (t(1)) t(2); else if (t(0)) t(3); else { if (t(4)) t(5); }
            for (; n < 3;) n++, t(n);
            for (var k in { a: 1 }) t(k);
            do t("do"); while (false);
            var f = () => (t("a"), "b");
            result = f();
        `);
        expect(count(output, isBareBody)).toBe(0);
        expect(count(output, (node) => node.type === "ForStatement")).toBe(0);
        expect(
            count(output, (node) => node.type === "IfStatement" && node.alternate?.type === "BlockStatement" && node.alternate.body.length === 1 && node.alternate.body[0]?.type === "IfStatement")
        ).toBe(0);
        expect(count(output, (node) => node.type === "ArrowFunctionExpression" && node.body.type !== "BlockStatement")).toBe(0);
    });

    it("splits declarations, in order", async () => {
        const output = await sameBehaviour("var a = t(1), b = t(a + 1), c; let d = t(b), e = d; result = [a, b, c, d, e];");
        expect(count(output, (node) => node.type === "VariableDeclaration" && node.declarations.length > 1)).toBe(0);
    });

    it("splits declarations and `return void` in switch cases too", async () => {
        const output = await sameBehaviour("function f(k) { switch (k) { case 1: var a = t(1), b = t(a + 1); return void t(b); default: return 0; } } result = [f(1), f(2)];");
        expect(count(output, (node) => node.type === "VariableDeclaration" && node.declarations.length > 1)).toBe(0);
        expect(count(output, (node) => node.type === "UnaryExpression" && node.operator === "void")).toBe(0);
    });

    it("moves leading var declarators the loop test and update don't use out of a for head, keeping their order", async () => {
        const output = await sameBehaviour("for (var a = t(1), i = t(0), b = t(2); i < 2; i++) t(a + b); result = [a, b, i];");
        // `a` leaves the head; `b` comes after `i` (used by the test), so it stays to keep t(0) before t(2).
        expect(count(output, (node) => node.type === "ForStatement" && node.init?.type === "VariableDeclaration" && node.init.declarations.length === 2)).toBe(1);
    });

    it("leaves let declarators in the loop head, where each iteration has its own", async () => {
        await sameBehaviour("var fs = []; for (let k = 0, i = 0; i < 3; i++) fs.push(() => k++); result = [fs[0](), fs[0](), fs[1](), fs[2]()];");
    });

    it("unquotes keys, but not a computed __proto__, a computed class constructor, or a static prototype", async () => {
        const output = await sameBehaviour(`
            var proto = { inherited: 1 };
            var o = { "a": 1, ["b"]: 2, "c"() { return 3; }, ["__proto__"]: proto, "x-y": 4 };
            class A { ["constructor"]() { return "method"; } "m"() { return 5; } }
            try { t(class B { static ["prototype"]() {} }); } catch (e) { t(e.name); }
            result = [o.a, o.b, o.c(), Object.getPrototypeOf(o) === proto, o["x-y"], new A().constructor === A, new A().m(), o.inherited];
        `);
        expect(count(output, (node) => (node.type === "Property" || node.type === "MethodDefinition") && node.key.type === "Literal" && node.key.value !== "x-y")).toBe(3);
    });

    it("writes { a: a } as { a }, but not for __proto__", async () => {
        const output = await sameBehaviour(`
            var a = 1, proto = { inherited: 2 };
            result = (function (__proto__) { var o = { a: a, "b": a, __proto__: __proto__ }; return [o.a, o.inherited, Object.keys(o)]; })(proto);
        `);
        expect(count(output, (node) => node.type === "Property" && node.shorthand)).toBe(1);
    });

    it("inverts negated equality and && / ||, but not negated ordering comparisons (NaN)", async () => {
        const output = await sameBehaviour("var n = NaN, a = 1, b = '1'; result = [!(a == b), !(a === b), !(a != b), !(a !== b), !(n < 1), !(n >= 1), !(t(a) && t(0)), !(t(0) || t(b))];");
        const negatedEquality = count(
            output,
            (node) => isNot(node) && (node.argument.type === "LogicalExpression" || (node.argument.type === "BinaryExpression" && ["==", "===", "!=", "!=="].includes(node.argument.operator)))
        );
        expect(negatedEquality).toBe(0);
    });

    it("turns && / || statements into if, but not ??", async () => {
        const output = await sameBehaviour("var a = 0, b = 1; a && t(1); b && t(2); a || t(3); b || t(4); a ?? t(5); null ?? t(6);");
        expect(count(output, (node) => node.type === "ExpressionStatement" && node.expression.type === "LogicalExpression" && node.expression.operator !== "??")).toBe(0);
    });

    it("drops !! where only truthiness counts, keeps it where the value is used", async () => {
        const output = await sameBehaviour(`
            var a = null, b = "b", r = [];
            if (!!a) t(1); if (!!b && !!t(2)) t(3); while (!!a) {} r.push(!!b ? 1 : 2, !!!b, !!b, !!b && b, a ? 1 : !!b);
            if (!!a ?? b) t(4);
            for (!!t(5); ;) break;
            result = r;
        `);
        // Left: `!!b`, `!!b && b` and `a ? 1 : !!b` (values), `!!a ?? b` (`??` keeps a falsy left side), the for-init.
        expect(count(output, (node) => isNot(node) && isNot(node.argument))).toBe(5);
    });

    it("inlines strings into templates, escaping what a template would read differently, but not in tagged templates", async () => {
        const output = await sameBehaviour(
            'var x = 1; result = [`a${"b"}c`, `$${"{"}x}`, `${"$"}{x}`, `${"`\\\\"}\\r${x}${"\\r\\n\\u2028"}`, `${"\\0"}1`, `\\0${"1"}`, `a${"\\0"}${"1"}`, `\\\\0${"1"}`, String.raw`a${"b"}c`, ((s, v) => s.raw.length + v)`a${"b"}c`];'
        );
        expect(count(output, (node) => node.type === "TemplateLiteral" && node.expressions.some((e) => e.type === "Literal"))).toBe(2);
    });

    it("turns statement and return ternaries into if/else", async () => {
        const output = await sameBehaviour("var a = 0; a ? t(1) : t(2); function f(x) { return x ? t(3) : x === 0 ? t(4) : t(5); } result = [f(1), f(0), f(null)];");
        expect(count(output, (node) => node.type === "ConditionalExpression")).toBe(0);
    });

    it("inverts an if whose consequent is empty", async () => {
        const output = await sameBehaviour("var f = t(1), o = t(2), log = [];\nif (f === o) {} else { f = o; log.push(f); }\nif (t(3)) ; else log.push(4);\nresult = log;\n");
        expect(output).toContain("if (f !== o) {\n  f = o;");
        expect(output).toContain("if (!t(3)) {\n  log.push(4);");
    });

    it("truncates number operands of bitwise operators as the operators do", async () => {
        const output = await sameBehaviour(
            "var x = 12345; result = [x & 4294967297, x | 1.5, x ^ -4294967296, x << 33, x >> 4294967327, x >>> 32.5, 4294967295 >>> x, 4294967296 << x, 2147483648 | x, 8589934593 >> x];"
        );
        expect(count(output, (node) => node.type === "Literal" && typeof node.value === "number" && (node.value > 4294967295 || !Number.isInteger(node.value)))).toBe(0);
    });

    it("spells typeof x > 'u' as a comparison with 'undefined'", async () => {
        const output = await sameBehaviour("var d = 1; result = [typeof u > 'u', typeof d > 'u', typeof u < 'u', typeof d < 'u', 'u' < typeof u, 'u' > typeof d];");
        expect(count(output, (node) => node.type === "Literal" && node.value === "u")).toBe(0);
    });

    it("drops no-op unary operators of statements, not typeof of an undeclared name or operators that convert", async () => {
        const output = await sameBehaviour(`
            var o = { valueOf() { t("valueOf"); return 1; } };
            void t(1); !t(2); typeof t(3); void 0; typeof undeclaredName; -o; +o; ~o; l: void 0;
            function f() { return void t(4); }
            result = f();
        `);
        expect(count(output, (node) => node.type === "ExpressionStatement" && node.expression.type === "UnaryExpression" && ["void", "!"].includes(node.expression.operator))).toBe(0);
        expect(count(output, (node) => node.type === "UnaryExpression" && node.operator === "void")).toBe(0);
    });

    it("puts constants on the right of comparisons, not shadowed or with-scoped names, and not across + or -", async () => {
        const output = await sameBehaviour(`
            var x = 2, r = [];
            r.push(1 === x, "a" < x, -1 <= x, undefined == x, 2 * t(x), NaN !== x, -Infinity < x, 1 === 2, "a" + x, 1 - x);
            try { (function () { r.push(undefined === t("after")); let undefined; })(); } catch (e) { r.push(e.name); }
            with ({ get NaN() { t("get"); return 0; } }) r.push(NaN === t("with"));
            result = r;
        `);
        expect(
            count(output, (node) => node.type === "BinaryExpression" && ["===", "<", "<=", "==", "*", "!=="].includes(node.operator) && node.left.type === "Literal" && node.right.type !== "Literal")
        ).toBe(0);
    });

    it("splits sequences into statements before a return, throw, if, switch or declaration", async () => {
        const output = await sameBehaviour(
            "function f(x) { t(1), t(2); if (t(3), x) { return t(4), t(5); } switch (t(6), x) { default: break; } let y = (t(7), x + 1); try { throw (t(8), y); } catch (e) { return e; } }\nresult = [f(0), f(1)];"
        );
        expect(count(output, (node) => node.type === "SequenceExpression")).toBe(0);
        expect(output).toContain("let y = x + 1;");
    });

    it("turns object-building IIFEs into object literals, not ones whose values use the builder's own bindings or the object", async () => {
        const output = await sameBehaviour(
            [
                'var a = (() => { var o; o = {}; o.channel = t("live"); o["x-y"] = 2; o[3] = t(3); return o; })();',
                "function g() { return function () { var o = {}; o.value = t(true); return o; }.apply(this, arguments); }\nvar b = g();",
                // A passed `this` is the caller's; a literal to start from; a store into a literal a property holds.
                'function h() { return function () { var o = { k: t(1) }; o.me = this.name; o.inner = {}; o.inner.deep = t(2); return o; }.call(this); }\nvar obj = { name: "obj", h: h };\nvar hh = obj.h();',
                "var c = function () { var o = {}; o.self = this === undefined; return o; }();", // its own this
                "function m() { return function () { var o = {}; o.count = arguments.length; return o; }.apply(this); }\nvar mm = m(1, 2);", // its own arguments
                "var d = (() => { var o = {}; o.again = o; return o; })();", // the object itself
                "var e = (() => { var o = {}; o.__proto__ = { p: 1 }; return o; })();", // a prototype, not a property
                "var n = (() => { var o = {}; o.box = t({}); o.box.v = 1; return o; })();", // a store into an object made elsewhere
                "var q = (() => { var o = { set h(v) { t(v); } }; o.h = 2; return o; })();", // a setter an assignment runs
                'var r = "outer";\nvar s = (() => { var r = { early: typeof r }; r.x = 1; return r; })();', // the object's name before it holds it
                "result = [a, b, hh, c.self, mm, d.again === d, e.p, n, q, s];",
            ].join("\n")
        );
        expect(output).toContain('var a = { channel: t("live"), "x-y": 2, 3: t(3) };');
        expect(output).toContain("return { value: t(true) };");
        expect(output).toContain("return { k: t(1), me: this.name, inner: { deep: t(2) } };");
        expect(count(output, isFunctionCall)).toBe(7);
        // At the top level reading `arguments` throws: that builder stays, so the script still throws there.
        expect(await sameBehaviour("var f = function () { var o = {}; o.v = 1; return o; }.apply(this, arguments);\nresult = f;")).toContain(".apply(this, arguments)");
    });

    it("writes escaped letters of regex patterns as letters and brackets as escapes, not a digit after a backreference or a control escape's letter", async () => {
        const output = await sameBehaviour(
            [
                "var r = [/\\x70\\x72\\u006fgress/i, /^(?:\\u0055\\x69|\\x49)\\x6e\\u0074$/, /[\\x61-\\x66_]+/, /(a)\\1\\x31/, /\\x5b\\x41\\x5d/, /\\c\\x41/];",
                'result = r.map(function (x) { return [x.test("PROGRESS"), x.test("Uint"), x.test("cafe"), x.test("aa1"), x.test("[A]"), x.test("\\\\cA")]; });',
            ].join("\n")
        );
        expect(output).toContain("/progress/i, /^(?:Ui|I)nt$/, /[a-f_]+/, /(a)\\1\\x31/, /\\[A\\]/, /\\c\\x41/");
    });

    it("writes legacy octal escapes and plain punctuation as characters, keeping backreferences and syntax", async () => {
        // With 101 groups, `\101` is a backreference to the last one, not `A`.
        const groups = "(a)".repeat(101);
        const output = await sameBehaviour(
            [
                `var r = [/^\\163\\137\\164h\\072/, /(a)(b)\\2\\1634/, /[\\163\\055]+/, /[\\x3a]/, /[:\\x3a]/v, /a{1\\x2c2}/, /\\061/, /${groups}\\101/];`,
                `result = r.map(function (x) { return [x.test("s_th:"), x.test("abbs4"), x.test("s-"), x.test(":"), x.test("a{1,2}"), x.test("1"), x.test("${"a".repeat(102)}"), x.test("${"a".repeat(101)}A")]; });`,
            ].join("\n")
        );
        // `[::]` would be a syntax error with the `v` flag.
        for (const pattern of ["/^s_th:/", "/(a)(b)\\2\\1634/", "/[s\\-]+/", "/[:]/", "/[:\\x3a]/v", "/a{1\\x2c2}/", "/1/", `${groups}\\101/`]) expect(output).toContain(pattern);
    });

    it("writes escaped digits and syntax characters plainly or as identity escapes, unless they would join what comes before", async () => {
        const output = await sameBehaviour(
            [
                "var r = [/\\u002e(srt|vtt)/, /\\x2f\\053\\x2d/, /[\\x29\\u0028\\x2d]/, /^(\\061|true)$/, /\\x4\\x41/, /a{\\x31}/, /[\\1\\x31]/, /\\x2e/u];",
                'result = r.map(function (x) { return [x.test("a.vtt"), x.test("/+-"), x.test("-"), x.test("1"), x.test("x4A"), x.test("J"), x.test("a{1}"), x.test("a"), x.test("\\u0001"), x.test("\\t")]; });',
            ].join("\n")
        );
        // Non-unicode `\x4` is the text `x4`, and `{` without a quantifier is a character; `\1` in a class is octal.
        for (const pattern of ["/\\.(srt|vtt)/", "/\\/\\+-/", "/[\\)\\(\\-]/", "/^(1|true)$/", "/\\x4\\x41/", "/a{\\x31}/", "/[\\1\\x31]/", "/\\./u"]) expect(output).toContain(pattern);
    });

    it("writes shuffled classes of letters and digits as sorted ranges and long quantifiers short, not in classes or with v", async () => {
        const output = await sameBehaviour(
            [
                "var r = [/^on[L-MKN-ZA-DF-JE-E]/, /[fea-dDE-FB-CA-A7-960-5]{2}/gi, /[^cba]x{0,}y{1,}z{0,1}?/, /[{0,}]/, /[cba\\-]/, /[ba]/v];",
                'result = r.map(function (x) { return ["onQ", "a9", "dxxyz", "{", "-", "b"].map(function (s) { x.lastIndex = 0; return x.test(s); }); });',
            ].join("\n")
        );
        for (const pattern of ["/^on[A-Z]/", "/[0-9A-Fa-f]{2}/gi", "/[^a-c]x*y+z??/", "/[{0,}]/", "/[cba\\-]/", "/[ba]/v"]) expect(output).toContain(pattern);
    });

    it("merges property assignments into the plain literal they follow, unless something could read the object meanwhile", async () => {
        const output = await sameBehaviour(
            [
                'function f(x) { var o = {}; o.a = t(x); o["b-c"] = 2; o[3] = function () { return o.a; }; var later = function () { return o; }; return [o, later()]; }',
                // A function declared anywhere exists from the start: `peek` could run while `p`'s values do.
                "function g() { var p = {}; p.a = peek(); p.b = 2; function peek() { return Object.keys(p).length; } return p; }",
                // An earlier closure sees the variable too.
                "function h() { var q; var look = function () { return typeof q; }; q = {}; q.a = look(); return q; }",
                "var o2 = {}; o2.self = typeof o2; o2.x = 1;",
                // A literal to start from, and stores into the literal its last property holds (values keep their order).
                "function k(x) { var o = { n: t(1), inner: {} }; o.inner.deep = t(x); o.extra = {}; o.extra.v = t(2); o.after = t(4); return o; }",
                "function k2(x) { var o = { inner: {}, n: t(1) }; o.inner.deep = t(x); var p = { inner: {}, other: {} }; p.inner.deep = t(x); return [o, p]; }",
                "function m() { var o = { set s(v) { t(v); } }; o.s = 3; return o; }",
                "result = [f(1)[0].a, f(2)[0][3](), g(), h(), o2, k(3), k2(5), m()];",
            ].join("\n")
        );
        expect(output).toContain('var o = { a: t(x), "b-c": 2 };\n  o[3] = function () {');
        expect(output).toContain("p.a = peek();");
        expect(output).toContain("q.a = look();");
        expect(output).toContain("o2.self = typeof o2;");
        expect(output).toContain("var o = { n: t(1), inner: { deep: t(x) }, extra: { v: t(2) }, after: t(4) };");
        for (const kept of ["o.inner.deep = t(x);", "p.inner.deep = t(x);", "o.s = 3;"]) expect(output).toContain(kept);
    });

    it("drops a neutral left operand anywhere, and a neutral right one where only truthiness counts", async () => {
        const output = await sameBehaviour(
            "var a = t(0), r = [];\nif (t(1) || false) r.push(1);\nif (a && true) r.push(2);\nr.push(false || t(3), true && t(4), a || false, t(5) && true);\nresult = r;\n"
        );
        expect(output).toContain("if (t(1)) {");
        expect(output).toContain("if (a) {");
        expect(output).toContain("r.push(t(3), t(4), a || false, t(5) && true);");
    });

    it("calls through (1, f) directly, not a method, eval, or inside a program with `with`", async () => {
        const output = await sameBehaviour(
            'var o = { m: function () { return this === o; } };\nfunction f(x) { return t(x); }\nfunction g() { var x = 1; return (0, eval)("typeof x"); }\nresult = [(1, f)(2), (0, o.m)(), g()];\n'
        );
        expect(output).toContain("result = [f(2), (0, o.m)(), g()];");
        expect(output).toContain('(0, eval)("typeof x")');
        const scoped = await sameBehaviour('var o = { f: function () { return this === o; } };\nfunction f() { return "global"; }\nwith (o) { result = [(1, f)()]; }\n');
        expect(scoped).toContain("(1, f)()");
    });

    it("runs a parameterless function's lone arrow IIFE as its body, not with parameters, a directive or an own arguments", async () => {
        const output = await sameBehaviour(
            [
                "var a = (function () { return (() => { var x = t(1); return [x, this === undefined, arguments.length]; })(); })();",
                // The arrow's `y` is its own (undefined until set), not the parameter.
                "var b = (function (y) { return (() => { var r = y; var y = 2; return r; })(); })(1);",
                // Strict code would see no `this`.
                'var c = (function () { return (() => { "use strict"; return this; })(); })();',
                // The arrow's `arguments` is its own variable, not the function's arguments object.
                "var d = (function () { return (() => { var r = typeof arguments; var arguments = 3; return r; })(); })();",
                "result = [a, b, typeof c, d];",
            ].join("\n")
        );
        expect(output).toContain("var a = function () {\n  var x = t(1);");
        expect(count(output, (node) => node.type === "ArrowFunctionExpression")).toBe(3);
    });

    it("turns a block left with `break label` from ifs into an if/else chain, not when other jumps name the label", async () => {
        const output = await sameBehaviour(
            [
                "function f(x) { var out = []; exit: { var k = x % 3; if (k === 0) { out.push(t('zero')); break exit; } if (k === 1) { out.push(t('one')); break exit; } out.push(t('other')); } out.push('end'); return out; }",
                "function g(x) { done: { if (x) { t(1); break done; } for (var i = 0; i < 2; i++) { if (i === x) break done; } t(2); } return x; }",
                "result = [f(0), f(1), f(2), g(0), g(1)];",
            ].join("\n")
        );
        expect(output).not.toContain("exit:");
        expect(output).toContain("} else if (k === 1) {");
        expect(output).toContain("done: {");
    });

    it("removes a label whose breaks end nested ifs at the end of its block, not one with a break before more code or a let after a break", async () => {
        const output = await sameBehaviour(
            [
                "function f(h, n, s) { var out = []; nested: { out.push(t('a')); if (h) { out.push(t('h')); if (n > 0) { out.push(t('n')); break nested; } if (s) { out.push(t('s')); } } else if (s) { out.push(t('else')); break nested; } } out.push('end'); return out; }",
                "function g(h) { early: { if (h) { if (h > 1) { t(1); break early; } t(2); } t(3); } return h; }",
                "function k() { stop: { t(1); break stop; var seen; } seen = 4; return typeof globalThis.seen; }",
                "function m(c) { scoped: { var get = function () { return y; }; if (c) { t(1); break scoped; } let y = 2; return get(); } return 0; }",
                "result = [f(0, 0, 0), f(0, 0, 1), f(1, 1, 1), f(1, 0, 1), f(1, 0, 0), g(0), g(1), g(2), k(), m(0), m(1)];",
            ].join("\n")
        );
        expect(output).not.toContain("nested:");
        expect(output).toContain('    } else if (s) {\n      out.push(t("s"));');
        for (const label of ["early: {", "stop: {", "scoped: {"]) expect(output).toContain(label);
    });

    it("returns instead of leaving a labeled block that ends a function, and keeps it elsewhere", async () => {
        const output = await sameBehaviour(
            [
                "function a(x) { var out = []; done: { if (x) { var i = 0; while (i < 3) { if (i === x) { out.push(t(i)); break done; } i++; } } out.push(t('after')); } return out; }",
                "function b(x, out) { done: { var inner = function () { done: { if (x) { break done; } out.push(t('inner')); } return 'inner'; }; out.push(inner()); if (x) { var i = 0; while (i < 3) { if (i === x) { out.push(t(i)); break done; } i++; } } out.push(t('after')); } }",
                "function g(x) { var out = []; if (x) { done: { var i = 0; while (i < 3) { if (i === x) { break done; } i++; } out.push(t('loop end')); } } out.push(t('after')); return out; }",
                "var log = [];\nb(1, log);\nb(0, log);",
                "result = [a(1), a(0), log, g(1), g(5)];",
            ].join("\n")
        );
        expect(output.match(/done:/g)).toHaveLength(2);
        expect(output).toContain("out.push(t(i));\n        return;");
    });

    it("drops a loop's label when its jumps leave or repeat that loop from no inner loop or switch", async () => {
        const output = await sameBehaviour(
            [
                "function c(n) { var out = []; plain: for (var i = 0; i < n; i++) { var g = function () { plain: while (true) { while (true) { break plain; } } return 1; }; if (i === 1) continue plain; if (i === 3) break plain; out.push(t(i + g())); } return out; }",
                "function d(n) { var out = []; nested: for (var i = 0; i < n; i++) { for (var j = 0; j < 2; j++) { if (j === i) continue nested; out.push(t(j)); } } return out; }",
                "function e(n) { var out = []; switched: for (var i = 0; i < n; i++) { switch (i) { case 2: break switched; default: out.push(t(i)); } } return out; }",
                "result = [c(5), d(3), e(4)];",
            ].join("\n")
        );
        // The inner function's own label stays (its break is in an inner loop).
        expect(output.match(/plain:/g)).toHaveLength(1);
        for (const label of ["nested:", "switched:"]) expect(output).toContain(label);
    });

    it("sends a labeled block's breaks where the jump after it goes, a loop's own breaks out of the block it ends, and drops code after a jump", async () => {
        const output = await sameBehaviour(
            [
                "function p(items) { var out = []; var i = 0; while (true) { inner: { if (i >= items.length) { break inner; } var v = items[i]; if (typeof v === 'string') { if (v === 'stop') { out.push(t('stop')); break inner; } i++; continue; } out.push(t(v)); i++; continue; } break; } return out; }",
                "function q(n) { var out = []; outer: { out.push(t('start')); for (var i = 0; i < n; i++) { if (i === 2) break outer; out.push(t(i)); } } out.push('end'); return out; }",
                "function s(n) { var out = []; for (var i = 0; i < n; i++) { skip: { switch (i) { case 1: break skip; default: out.push(t(i)); } out.push(t('after')); } continue; } return out; }",
                "function w(n) { var out = []; while (n-- > 0) { sw: { switch (n) { case 1: break sw; default: out.push(t(n)); } out.push(t('after')); } break; } return out; }",
                "function x(n) { var out = []; while (true) { lp: { for (var j = 0; j < 3; j++) { if (j === n) break lp; } out.push(t('none')); } break; } return out; }",
                "function v() { var out = []; for (var k = 0; k < 2; k++) { out.push(t(k)); continue; var hoisted = 1; } hoisted = 5; return [out, typeof globalThis.hoisted]; }",
                "function y(c) { var out = []; outer: { out.push(t('a')); inner: { if (c) { break inner; } out.push(t('b')); } break outer; out.push(t('dead')); } out.push(t('end')); return out; }",
                "result = [p([1, 'a', 'stop', 2]), p([3]), q(1), q(4), s(3), w(3), w(5), x(1), x(7), v(), y(0), y(1)];",
            ].join("\n")
        );
        for (const label of ["inner:", "outer:", "skip:"]) expect(output).not.toContain(label);
        for (const label of ["sw:", "lp:"]) expect(output).toContain(label);
        // The `break;` after the forwarded block followed a `continue;`: it went as unreachable.
        expect(output).toContain("    i++;\n    continue;\n  }\n  return out;");
    });

    it("assigns a value straight to the name a single-use local copies it to, not a local used again, a parameter or a global", async () => {
        const output = await sameBehaviour(
            [
                "function f(x) { var a; var b, c; a = {}; a.v = x; a.w = t(1); b = a; c = b; return c; }",
                "function g(x) { var a; var b; a = t(x); b = a; return [a, b]; }",
                "function k(a) { var b; a = t(2); b = a; return [b, arguments[0]]; }",
                "function define(x) { globalThis.later = 0; return x; }",
                'function u(x) { "use strict"; var a; a = define(x); later = a; return later; }',
                "var top;\nvar out;\ntop = t(3);\nout = top;",
                "result = [f(1), g(2), k(4), u(5), out];",
            ].join("\n")
        );
        expect(output).toContain("function f(x) {\n  var c;\n  c = {");
        for (const kept of ["b = a;\n  return [a, b];", "b = a;\n  return [b, arguments[0]];", "later = a;", "out = top;"]) expect(output).toContain(kept);
        // A direct eval may read the copy's source.
        const evaluated = await sameBehaviour('function e(x) { var a; var b; a = t(x); b = a; return [b, eval("a")]; }\nresult = e(6);');
        expect(evaluated).toContain("b = a;");
    });

    it("keeps random control flow behaving the same", async () => {
        for (let seed = 1; seed <= 40; seed++) {
            const code = `(function () {\n${flatten(generate(seed), mulberry32(seed))}\n})();`;
            const output = await unminify(code);
            for (const bits of [[true], [false], [true, false, true]]) expect(runTrace(output, bits)).toBe(runTrace(code, bits));
        }
    });
});
