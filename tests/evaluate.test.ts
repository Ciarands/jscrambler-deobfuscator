import { describe, expect, it } from "vitest";
import type { Expression, Node } from "../src/core/ast.js";
import { binary, evaluate, FAIL, unary, value, type Evaluation, type EvaluateEnv, type Value } from "../src/core/evaluate.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";
import { serialize } from "./helpers.js";

const templateOf = (code: string): Node => {
    let found: Node | undefined;
    traverse(parse(code), {
        TemplateLiteral: (path) => {
            found ??= path.node;
        },
    });
    if (found === undefined) throw new Error("no template literal");
    return found;
};

const expression = (code: string): Node => (parse(code).body[0] as unknown as { expression: Node }).expression;

const binaryExpression = (code: string) => {
    const node = expression(code);
    if (node.type !== "BinaryExpression") throw new Error(`not a binary expression: ${code}`);
    return node;
};

const VALUES: readonly Value[] = [
    0,
    -0,
    1,
    -1,
    1.5,
    -2.5,
    3,
    31,
    32,
    33,
    -33,
    2 ** 31,
    2 ** 31 - 1,
    -(2 ** 31) - 1,
    2 ** 32 + 5,
    2 ** 53 + 2,
    -(2 ** 40) - 3,
    Number.NaN,
    Number.POSITIVE_INFINITY,
    Number.NEGATIVE_INFINITY,
    "",
    "0",
    "1",
    "10",
    "9",
    " 12 ",
    "-0",
    "0x1f",
    "a",
    "b",
    "ab",
    "abc",
    null,
    undefined,
    true,
    false,
];

const HOST_BINARY: Readonly<Record<string, (a: number, b: number) => unknown>> = {
    "+": (a, b) => a + b,
    "-": (a, b) => a - b,
    "*": (a, b) => a * b,
    "/": (a, b) => a / b,
    "%": (a, b) => a % b,
    "**": (a, b) => a ** b,
    "==": (a, b) => a == b,
    "!=": (a, b) => a != b,
    "===": (a, b) => a === b,
    "!==": (a, b) => a !== b,
    "<": (a, b) => a < b,
    "<=": (a, b) => a <= b,
    ">": (a, b) => a > b,
    ">=": (a, b) => a >= b,
    "<<": (a, b) => a << b,
    ">>": (a, b) => a >> b,
    ">>>": (a, b) => a >>> b,
    "&": (a, b) => a & b,
    "|": (a, b) => a | b,
    "^": (a, b) => a ^ b,
};

const HOST_UNARY: Readonly<Record<string, (a: number) => unknown>> = {
    "-": (a) => -a,
    "+": (a) => +a,
    "!": (a) => !a,
    "~": (a) => ~a,
    typeof: (a) => (a === null ? "object" : typeof a),
    void: () => undefined,
};

const expectValue = (result: Evaluation, expected: unknown, message: string): void => {
    expect(result.ok, message).toBe(true);
    if (result.ok) expect(Object.is(result.value, expected), `${message}: got ${serialize(result.value)}, want ${serialize(expected)}`).toBe(true);
};

const globals: EvaluateEnv = { isGlobal: () => true };

describe("evaluate", () => {
    it("has no value for a template part with an invalid escape", () => {
        // Only a tagged template may contain one; its cooked value is null, not an empty string.
        expect(evaluate(templateOf("tag`\\unicode`")).ok).toBe(false);
        expect(evaluate(templateOf("tag`ok${1}\\xZ`")).ok).toBe(false);
        expect(evaluate(templateOf("`a${1}b`"))).toEqual({ ok: true, value: "a1b" });
    });

    it("negates fresh objects to false, but not literals that run code to build", () => {
        for (const code of ["![]", "![1, 'a']", "!{}", "!function () {}", "!(() => 1)"]) expect(evaluate(expression(code))).toEqual({ ok: true, value: false });
        for (const code of ["![f()]", "!{ a: f() }", "!{ get a() { return 1; } }"]) expect(evaluate(expression(code)).ok).toBe(false);
    });
});

describe("binary", () => {
    it.each(Object.keys(HOST_BINARY))("%s agrees with the host on every primitive pair", (operator) => {
        const host = HOST_BINARY[operator]!;
        for (const left of VALUES) for (const right of VALUES) expectValue(binary(operator, left, right), host(left as number, right as number), `${serialize(left)} ${operator} ${serialize(right)}`);
    });

    it.each(["in", "instanceof", "&&", "||", "??", ",", "=", "+=", "delete", ""])("refuses %j", (operator) => {
        for (const left of VALUES) for (const right of VALUES) expect(binary(operator, left, right), `${serialize(left)} ${operator} ${serialize(right)}`).toEqual(FAIL);
    });

    it("evaluates binary expressions in source through the same rules", () => {
        expectValue(evaluate(expression("'10' < '9'")), true, "'10' < '9'");
        expectValue(evaluate(expression("'10' < 9")), false, "'10' < 9");
        expectValue(evaluate(expression("-1 >>> 0")), 4294967295, "-1 >>> 0");
        expectValue(evaluate(expression("-1 >> 0")), -1, "-1 >> 0");
        expectValue(evaluate(expression("4294967301 | 0")), 5, "2 ** 32 + 5 | 0");
        expectValue(evaluate(expression("1 << 33")), 2, "1 << 33");
        expectValue(evaluate(expression("0 * -1")), -0, "0 * -1");
        expectValue(evaluate(expression("NaN === NaN"), globals), false, "NaN === NaN");
        expectValue(evaluate(expression("'1' + 2 - 1")), 11, "'1' + 2 - 1");
        expect(evaluate(expression("'a' in 'abc'")).ok).toBe(false);
        expect(evaluate(expression("1 instanceof 2")).ok).toBe(false);
        expect(evaluate(expression("f() + 1")).ok).toBe(false);
        expect(evaluate(expression("1 + f()")).ok).toBe(false);
        expect(evaluate(expression("1n + 1n")).ok).toBe(false);
        expect(evaluate(expression("/a/ + ''")).ok).toBe(false);
    });
});

describe("unary", () => {
    it.each(Object.keys(HOST_UNARY))("%s agrees with the host on every primitive", (operator) => {
        const host = HOST_UNARY[operator]!;
        for (const operand of VALUES) expectValue(unary(operator, operand), host(operand as number), `${operator} ${serialize(operand)}`);
    });

    it.each(["delete", "++", "--", "await", ""])("refuses %j", (operator) => {
        for (const operand of VALUES) expect(unary(operator, operand), `${operator} ${serialize(operand)}`).toEqual(FAIL);
    });

    it("evaluates unary expressions in source, but not delete", () => {
        expectValue(evaluate(expression("-0")), -0, "-0");
        expectValue(evaluate(expression("- -0")), 0, "- -0");
        expectValue(evaluate(expression("~2147483648")), 2147483647, "~2 ** 31");
        expectValue(evaluate(expression("typeof null")), "object", "typeof null");
        expect(evaluate(expression("void f")).ok).toBe(false);
        expect(evaluate(expression("delete 1")).ok).toBe(false);
        expect(evaluate(expression("typeof f")).ok).toBe(false);
    });
});

describe("evaluate expressions", () => {
    it.each<[string, Value]>([
        ["0 && f()", 0],
        ["'' && f()", ""],
        ["null && f()", null],
        ["1 && 2", 2],
        ["'a' || f()", "a"],
        ["0 || 'x'", "x"],
        ["0 || ''", ""],
        ["null ?? 1", 1],
        ["void 0 ?? 'd'", "d"],
        ["0 ?? f()", 0],
        ["'' ?? f()", ""],
        ["false ?? f()", false],
        ["1 ? 2 : f()", 2],
        ["0 ? f() : 3", 3],
        ["'' ? f() : 'e'", "e"],
        ["null ? f() : 1 ? 'n' : f()", "n"],
        ["(1, 2, 3)", 3],
        ["'abc'.length", 3],
        ["''.length", 0],
        ["'abc'[1]", "b"],
        ["'abc'[0][0]", "a"],
        ["'abc'[5]", undefined],
        ["'abc'['length']", 3],
        ["'abc'[2 - 1]", "b"],
        ["'abc'['1' * 1]", "b"],
        ["'abc'['len' + 'gth']", 3],
        ["('a' + 'bc').length", 3],
        ["`ab${1 + 1}`.length", 3],
    ])("%s is %j", (code, expected) => {
        expectValue(evaluate(expression(code)), expected, code);
    });

    it.each([
        "1 && f()",
        "f() && 0",
        "0 || f()",
        "null ?? f()",
        "void 0 ?? f()",
        "f() ?? 1",
        "1 ? f() : 2",
        "0 ? 1 : f()",
        "f() ? 1 : 1",
        "(f(), 2)",
        "(1, f())",
        "'abc'[-1]",
        "'abc'[1.5]",
        "'abc'[f()]",
        "'abc'.foo",
        "'abc'[5].length",
        "(1).length",
        "f().length",
        "a.b",
        "x",
    ])("%s has no value", (code) => {
        expect(evaluate(expression(code)).ok).toBe(false);
    });

    it("never looks at the side a logical or conditional expression skips", () => {
        const seen: string[] = [];
        const lookup = (node: Expression): Evaluation => {
            if (node.type === "Identifier") seen.push(node.name);
            return FAIL;
        };
        for (const code of ["0 && x", "1 || x", "0 ?? x", "1 ? 2 : x", "0 ? x : 2"]) evaluate(expression(code), { lookup });
        expect(seen).toEqual([]);
    });
});

describe("isGlobal", () => {
    it.each<[string, Value]>([
        ["undefined", undefined],
        ["NaN", Number.NaN],
        ["Infinity", Number.POSITIVE_INFINITY],
    ])("%s is known only when confirmed global", (name, expected) => {
        const node = expression(name);
        expect(evaluate(node).ok).toBe(false);
        expect(evaluate(node, {}).ok).toBe(false);
        expect(evaluate(node, { isGlobal: () => false }).ok).toBe(false);
        const asked: Node[] = [];
        expectValue(
            evaluate(node, {
                isGlobal: (identifier) => {
                    asked.push(identifier);
                    return true;
                },
            }),
            expected,
            name
        );
        expect(asked).toEqual([node]);
    });

    it("leaves other identifiers unknown even when global", () => {
        for (const name of ["globalThis", "window", "atob", "x", "Math"]) expect(evaluate(expression(name), globals).ok, name).toBe(false);
    });

    it("gates each occurrence separately", () => {
        const shadowed = binaryExpression("NaN + Infinity");
        const env: EvaluateEnv = { isGlobal: (identifier) => identifier === shadowed.right };
        expect(evaluate(shadowed, env).ok).toBe(false);
        expectValue(evaluate(expression("-Infinity"), globals), Number.NEGATIVE_INFINITY, "-Infinity");
    });

    it("decodes atob only when its callee is confirmed global", () => {
        const call = expression("atob('bmF2aWdhdG9y')");
        if (call.type !== "CallExpression") throw new Error("not a call");
        expect(evaluate(call).ok).toBe(false);
        expect(evaluate(call, { isGlobal: () => false }).ok).toBe(false);
        const asked: Node[] = [];
        const env: EvaluateEnv = {
            isGlobal: (identifier) => {
                asked.push(identifier);
                return true;
            },
        };
        expectValue(evaluate(call, env), "navigator", "atob('bmF2aWdhdG9y')");
        expect(asked).toEqual([call.callee]);
        expectValue(evaluate(expression("atob('bmF2' + 'aWdhdG9y')"), globals), "navigator", "atob of a concatenation");
        expectValue(evaluate(expression("atob('')"), globals), "", "atob('')");
    });

    it.each([
        "atob('AAEC')",
        "atob('!!')",
        "atob(1)",
        "atob(f())",
        "atob()",
        "atob('bmF2', 'aWdhdG9y')",
        "atob(...['bmF2aWdhdG9y'])",
        "btoa('navigator')",
        "window.atob('bmF2aWdhdG9y')",
        "atob?.('bmF2aWdhdG9y')",
    ])("%s has no value even with atob global", (code) => {
        expect(evaluate(expression(code), globals).ok).toBe(false);
    });
});

describe("lookup", () => {
    it("gives identifiers and whole expressions a value", () => {
        const knowsX: EvaluateEnv = { lookup: (node) => (node.type === "Identifier" && node.name === "x" ? value(4) : FAIL) };
        expectValue(evaluate(expression("x"), knowsX), 4, "x");
        expectValue(evaluate(expression("x * 2 + 1"), knowsX), 9, "x * 2 + 1");
        expect(evaluate(expression("y + 1"), knowsX).ok).toBe(false);
        expectValue(evaluate(expression("f(g())"), { lookup: (node) => (node.type === "CallExpression" ? value("called") : FAIL) }), "called", "f(g())");
    });

    it("takes precedence over the built-in rules", () => {
        expectValue(evaluate(expression("1 + 2"), { lookup: (node) => (node.type === "BinaryExpression" ? value("x") : FAIL) }), "x", "1 + 2");
        expectValue(evaluate(expression("NaN"), { lookup: () => value(0), isGlobal: () => true }), 0, "NaN");
    });

    it("is not consulted for literals", () => {
        const seen: string[] = [];
        const lookup = (node: Expression): Evaluation => {
            seen.push(node.type);
            return value("looked up");
        };
        expectValue(evaluate(expression("1"), { lookup }), 1, "1");
        expectValue(evaluate(expression("'s'"), { lookup }), "s", "'s'");
        expectValue(evaluate(expression("null"), { lookup }), null, "null");
        expect(seen).toEqual([]);
    });

    it("falls back to the built-in rules when it refuses", () => {
        const seen: string[] = [];
        const lookup = (node: Expression): Evaluation => {
            seen.push(node.type);
            return FAIL;
        };
        expectValue(evaluate(expression("-(1 + 2)"), { lookup }), -3, "-(1 + 2)");
        expect(seen).toEqual(["UnaryExpression", "BinaryExpression"]);
        expectValue(evaluate(expression("Infinity"), { lookup, isGlobal: () => true }), Number.POSITIVE_INFINITY, "Infinity");
    });
});

describe("cache", () => {
    it("stores every visited node's result", () => {
        const node = binaryExpression("1 + f()");
        const cache = new WeakMap<Node, Evaluation>();
        expect(evaluate(node, { cache }).ok).toBe(false);
        expect(cache.get(node)?.ok).toBe(false);
        expect(cache.get(node.left)).toEqual({ ok: true, value: 1 });
        expect(cache.get(node.right)?.ok).toBe(false);
    });

    it("reuses a cached result instead of consulting lookup again", () => {
        const node = binaryExpression("x + 1");
        const cache = new WeakMap<Node, Evaluation>();
        let calls = 0;
        const lookup = (n: Expression): Evaluation => {
            if (n.type !== "Identifier") return FAIL;
            calls++;
            return value(calls);
        };
        expectValue(evaluate(node, { cache, lookup }), 2, "first");
        expectValue(evaluate(node, { cache, lookup }), 2, "second");
        expect(calls).toBe(1);
        expectValue(evaluate(node.left, { cache, lookup }), 1, "x alone");
        expect(calls).toBe(1);
    });

    it("reuses a cached failure", () => {
        const node = expression("x");
        const cache = new WeakMap<Node, Evaluation>();
        expect(evaluate(node, { cache }).ok).toBe(false);
        expect(evaluate(node, { cache, lookup: () => value(1) }).ok).toBe(false);
    });

    it("returns a pre-seeded entry as-is, also for a nested node", () => {
        const node = binaryExpression("1 + 2");
        const seeded = value(40);
        const cache = new WeakMap<Node, Evaluation>([[node.right, seeded]]);
        expectValue(evaluate(node, { cache }), 41, "1 + <40>");
        const top = new WeakMap<Node, Evaluation>([[node, seeded]]);
        expect(evaluate(node, { cache: top })).toBe(seeded);
    });

    it("does not change results without a cache", () => {
        const node = expression("'abc'[1] + 'abc'.length");
        expectValue(evaluate(node), "b3", "uncached");
        expectValue(evaluate(node, { cache: new WeakMap() }), "b3", "cached");
    });
});
