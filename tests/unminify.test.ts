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

/** Output of the pass, after checking that it behaves as the input does. */
const sameBehaviour = async (input: string): Promise<string> => {
    const output = await unminify(input);
    expect(run(output)).toEqual(run(input));
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

    it("turns object-building IIFEs into object literals, not ones whose values use the builder's this or the object", async () => {
        const output = await sameBehaviour(
            [
                'var a = (() => { var o; o = {}; o.channel = t("live"); o["x-y"] = 2; o[3] = t(3); return o; })();',
                "function g() { return function () { var o = {}; o.value = t(true); return o; }.apply(this, arguments); }\nvar b = g();",
                "var c = function () { var o = {}; o.self = this === undefined; return o; }();", // its own this
                "var d = (() => { var o = {}; o.again = o; return o; })();", // the object itself
                "var e = (() => { var o = {}; o.__proto__ = { p: 1 }; return o; })();", // a prototype, not a property
                "result = [a, b, c.self, d.again === d, e.p];",
            ].join("\n")
        );
        expect(output).toContain('var a = { channel: t("live"), "x-y": 2, 3: t(3) };');
        expect(output).toContain("return { value: t(true) };");
        expect(count(output, (node) => node.type === "CallExpression" && node.callee.type !== "Identifier")).toBe(3);
        // At the top level reading `arguments` throws: that builder stays, so the script still throws there.
        expect(await sameBehaviour("var f = function () { var o = {}; o.v = 1; return o; }.apply(this, arguments);\nresult = f;")).toContain(".apply(this, arguments)");
    });

    it("writes escaped letters of regex patterns as letters, not digits, brackets or a control escape's letter", async () => {
        const output = await sameBehaviour(
            [
                "var r = [/\\x70\\x72\\u006fgress/i, /^(?:\\u0055\\x69|\\x49)\\x6e\\u0074$/, /[\\x61-\\x66_]+/, /(a)\\1\\x31/, /\\x5b\\x41\\x5d/, /\\c\\x41/];",
                'result = r.map(function (x) { return [x.test("PROGRESS"), x.test("Uint"), x.test("cafe"), x.test("aa1"), x.test("[A]"), x.test("\\\\cA")]; });',
            ].join("\n")
        );
        expect(output).toContain("/progress/i, /^(?:Ui|I)nt$/, /[a-f_]+/, /(a)\\1\\x31/, /\\x5bA\\x5d/, /\\c\\x41/");
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

    it("keeps random control flow behaving the same", async () => {
        for (let seed = 1; seed <= 40; seed++) {
            const code = `(function () {\n${flatten(generate(seed), mulberry32(seed))}\n})();`;
            const output = await unminify(code);
            for (const bits of [[true], [false], [true, false, true]]) expect(runTrace(output, bits)).toBe(runTrace(code, bits));
        }
    });
});
