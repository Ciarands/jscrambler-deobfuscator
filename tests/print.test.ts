import { readFileSync } from "node:fs";
import { describe, expect, it } from "vitest";
import type { ExpressionStatement, IfStatement, Node, Program, Statement } from "../src/core/ast.js";
import { valueToNode } from "../src/core/build.js";
import { parse } from "../src/core/parse.js";
import { print, printStatement } from "../src/core/print.js";
import { flatten, generate, mulberry32, runTrace } from "./fuzz/programs.js";
import { observe, serialize } from "./helpers.js";

/** The AST without positions and source spellings: what a re-parse of the printed code must give back. */
const shape = (node: unknown): unknown => {
    if (Array.isArray(node)) return node.map(shape);
    if (typeof node === "bigint") return `${node}n`;
    if (typeof node === "number" && Object.is(node, -0)) return "-0";
    if (node instanceof RegExp) return String(node);
    if (node === null || typeof node !== "object") return node;
    const out: Record<string, unknown> = {};
    for (const [key, value] of Object.entries(node)) if (key !== "start" && key !== "end" && key !== "range" && key !== "raw") out[key] = shape(value);
    return out;
};

const roundTrips = (code: string): void => {
    const program = parse(code);
    const printed = print(program);
    expect(shape(parse(printed))).toEqual(shape(program));
    for (const statement of program.body) expect(shape(parse(printStatement(statement as Statement).source).body)).toEqual(shape([statement]));
};

/** Every construct whose printing needs care: precedence, statement-start ambiguities, literals, classes, modules. */
const SCRIPT = readFileSync(new URL("fixtures/print-script.txt", import.meta.url), "utf8");
const MODULE = readFileSync(new URL("fixtures/print-module.txt", import.meta.url), "utf8");

const isShown = (code: number): boolean =>
    code === 0x0a || (code >= 0x20 && code < 0x7f) || (code > 0xa0 && code !== 0x2028 && code !== 0x2029 && code !== 0x200b && code !== 0xfeff && (code < 0xd800 || code > 0xdfff));

describe("print", () => {
    it("prints code that parses back to the same tree, as a program and statement by statement", () => {
        roundTrips(SCRIPT);
        roundTrips(MODULE);
        roundTrips(`export default class {}`);
        roundTrips(`export default async function () {}`);
        roundTrips(`export default (class {});`);
        roundTrips(`#!/usr/bin/env node\nx;`);
        roundTrips(`"use strict"; 'use\\x20strict'; ("not a directive"); function f() { "use strict"; ("x"); }`);
    });

    it("round-trips random control flow, and the printed code runs the same", () => {
        for (let seed = 1; seed <= 40; seed++) {
            const body = flatten(generate(seed), mulberry32(seed));
            const program = parse(`(function () {\n${body}\n})();`);
            const printed = print(program);
            expect(shape(parse(printed))).toEqual(shape(program));
            expect(runTrace(printed, [true, false, true])).toBe(runTrace(`(function () {\n${body}\n})();`, [true, false, true]));
        }
    });

    it("prints built string and number literals as the same values, invisible characters escaped", () => {
        const strings = ["\ud800x", "\udc00", "😀\ud83d", "\u00001", "\x07\x7f\x9f", "\u2028\u2029", "\u200b\ufeff\xa0", "'\"`${}", "\\", "\r\n\t\b\f\v", "</script>"];
        const numbers = [0.5, 1e6, 1e21, 1e-7, 5e-324, 1.7976931348623157e308, 123456789012, 0.1 + 0.2, 2 ** 53 + 2];
        const program = parse("x = [];");
        const array = ((program.body[0] as ExpressionStatement).expression as { right: { elements: Node[] } }).right;
        array.elements = [...strings, ...numbers].map((value) => valueToNode(value, [0, 0]));
        const printed = print(program);
        expect(observe(`${printed}; result = x;`)).toBe(serialize([...strings, ...numbers]));
        // Invisible and lone characters are escapes, so the file stays valid text that shows them.
        expect([...printed].filter((char) => !isShown(char.codePointAt(0) ?? 0))).toEqual([]);
        expect(printed).toContain("1000000");
        expect(printed).toContain("0.5");
        expect(printed).toContain("1e21");
    });

    it("keeps an else with its own if when the then-branch is a bare if", () => {
        // `if (a) { if (b) t(1); } else t(2);` with the block taken away: the else still belongs to the outer if.
        const program = parse("if (a) { if (b) t(1); } else t(2);");
        const outer = program.body[0] as IfStatement;
        outer.consequent = (outer.consequent as { body: Statement[] }).body[0] as Statement;
        expect(observe(print(program), { globals: () => ({ a: true, b: false }), trace: true })).toBe(serialize([[], undefined]));
    });

    it("parenthesizes a string statement where it would read as a directive", () => {
        const program = parse("function f() { x; return this; }");
        const body = (program.body[0] as { body: { body: Statement[] } }).body.body;
        body[0] = { type: "ExpressionStatement", expression: valueToNode("use strict", [0, 0]), start: 0, end: 0 } as unknown as Statement;
        expect(observe(`${print(program)}; result = f() === undefined;`)).toBe("false");
    });

    it("keeps a built negative number apart from what precedes and follows it", () => {
        const program = parse("x = a - b; y = c.d;");
        const subtract = (program.body[0] as ExpressionStatement).expression as { right: { right: Node } };
        subtract.right.right = { type: "Literal", value: -1, raw: null, start: 0, end: 0 } as unknown as Node;
        const member = (program.body[1] as ExpressionStatement).expression as { right: { object: Node } };
        member.right.object = { type: "Literal", value: -1.5, raw: null, start: 0, end: 0 } as unknown as Node;
        expect(observe(`${print(program as Program)}; result = [x, y];`, { globals: () => ({ a: 5, b: 0 }) })).toBe(serialize([6, undefined]));
    });

    it("keeps short lists on one line and puts long ones one item per line", () => {
        expect(print(parse("f([1, 2], { a: 1, b: 2 }, function () { return 1; });"))).toBe("f([1, 2], { a: 1, b: 2 }, function () {\n  return 1;\n});\n");
        const long = Array.from({ length: 12 }, (_, i) => `"item number ${i}"`).join(", ");
        expect(print(parse(`x = [${long}];`)).split("\n")).toHaveLength(15);
        expect(print(parse("x = { a: function () { return 1; } };"))).toBe("x = {\n  a: function () {\n    return 1;\n  }\n};\n");
    });
});
