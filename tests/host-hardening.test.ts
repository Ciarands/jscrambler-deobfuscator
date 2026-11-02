import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { EXIT_FAILED, EXIT_OK, EXIT_USAGE, runCli } from "../src/cli/main.js";
import { isBindingName } from "../src/core/ast.js";
import { valueToNode } from "../src/core/build.js";
import { pushAll, spliceList } from "../src/core/list.js";
import { parse } from "../src/core/parse.js";
import { print } from "../src/core/print.js";
import { NestingError, traverse } from "../src/core/traverse.js";
import type { Node } from "../src/core/ast.js";
import { createLogger, sanitizeLine } from "../src/logger.js";
import { deobfuscate } from "../src/index.js";
import { observe } from "./helpers.js";

// oxlint-disable-next-line no-control-regex -- the characters the output must not hold
const UNSAFE = /[\0-\x08\x0b-\x1f\x7f-\x9f\u061c\u200b-\u200f\u202a-\u202e\u2060-\u2069\ufeff]/u;

/** The AST without positions and source text: what the program means (a directive's value is its literal's). */
const shape = (code: string): string => JSON.stringify(parse(code), (key, value) => (["start", "end", "range", "raw", "pattern", "directive"].includes(key) ? undefined : value));

describe("printer: control and format characters", () => {
    const cases = [
        ["an untagged template", "result = `A\u001b]0;T\u0007B\u202eC\u0085${1}\u2066D`;"],
        ["a regex body", "result = [/x\u202ey\u001b/.test('x\u202ey\u001b'), /a\u200fb/.test('a\u200fb'), /[^\u0085]/.test('\u0085')];"],
        ["a unicode regex body", "result = /[\u{e0001}\u202e]+/u.exec('\u{e0001}\u202e')[0].length;"],
        ["an identity escape in a regex", "result = /\\\u202e/.test('\u202e');"],
        ["a directive", "function f() { 'a\u001bb\u202e'; return this; } result = typeof f();"],
        ["an escaped line separator in a directive", "function f() { 'a\\\u2028b'; return 1; } result = f();"],
    ] as const;

    for (const [name, source] of cases) {
        it(`escapes ${name} and prints the same program`, () => {
            const output = print(parse(source));
            expect(output).not.toMatch(UNSAFE);
            expect(observe(output)).toBe(observe(source));
            expect(shape(output)).toBe(shape(source));
            expect(print(parse(output))).toBe(output);
        });
    }

    it("keeps a template's cooked value and a regex's matches", () => {
        const source = "result = [`\u001b${'x'}\u202e`, /\u001b[\u202e]/.test('\u001b\u202e')];";
        const output = print(parse(source));
        expect(output).toContain("\\x1B");
        expect(output).toContain("\\u202E");
        expect(observe(output)).toBe(observe(source));
    });

    it("escapes the hashbang", () => {
        const output = print(parse("#!/usr/bin/env node \u001b]0;T\u0007\nx = 1;"));
        expect(output).not.toMatch(UNSAFE);
        expect(output.startsWith("#!/usr/bin/env node ")).toBe(true);
    });

    it("keeps a tagged template's raw text and warns", () => {
        const source = "result = String.raw`a\u202eb`;";
        const warnings: string[] = [];
        const output = print(parse(source), (message) => warnings.push(message));
        expect(output).toContain("\u202e");
        expect(warnings).toHaveLength(1);
        expect(observe(output)).toBe(observe(source));
    });

    it("prints a replaced directive's literal, not the stale directive", () => {
        const program = parse("function f() { 'use strict'; return 1; }");
        let replaced = false;
        traverse(program, {
            Literal(literal) {
                if (literal.node.value !== "use strict") return;
                literal.replace({ ...literal.node, value: "other" } as Node);
                replaced = true;
            },
        });
        expect(replaced).toBe(true);
        const output = print(program);
        expect(output).not.toContain("use strict");
        expect(output).toContain('("other");');
    });
});

describe("log lines", () => {
    it("render control, bidi and separator characters as escapes, and stay one line", () => {
        expect(sanitizeLine("a\u001b]52;c;eA==\u0007b\nc\u202ed\u0085\te\ud800")).toBe("a\\x1B]52;c;eA==\\x07b\\x0Ac\\u{202E}d\\x85\te\\u{D800}");
    });

    it("are cut at 4 KiB", () => {
        const line = sanitizeLine("x".repeat(10_000));
        expect(line.length).toBe(4096);
        expect(line.endsWith("…")).toBe(true);
    });

    it("carry no raw escape characters from guest-made names", async () => {
        const lines: string[] = [];
        const code = `function G() {}
G.a = 1;
Math["\\u001b]52;c;eA==\\u0007"] = Math.abs;
Array.prototype["\\u001b]52;c;eA==\\u0007"] = Array.prototype.join;
`;
        await deobfuscate(code, { logger: createLogger("debug", (line) => lines.push(line)) });
        expect(lines.some((line) => line.includes("\\x1B]52"))).toBe(true);
        for (const line of lines) expect(line).not.toMatch(UNSAFE);
    });
});

describe("names", () => {
    it("reserved words and literals are no binding names", () => {
        for (const name of ["true", "false", "null", "this", "super", "let", "yield", "await", "static", "arguments", "eval", "enum", "class"]) expect(isBindingName(name)).toBe(false);
        for (const name of ["H0", "document", "undefined", "$", "_x"]) expect(isBindingName(name)).toBe(true);
    });

    it("a host alias of a reserved word stays as it is", async () => {
        const code = `function G() {}
G.a = 1;
(function () {
  Object.defineProperty(globalThis, "H0", { get: function () { return globalThis["true"]; }, set: function (v) { globalThis["true"] = v; }, configurable: true });
})();
if (!H0) result = 1;
`;
        const output = (await deobfuscate(code)).code;
        expect(output).toContain("if (!H0)");
        expect(output).not.toMatch(/!\s*true/);
    });
});

describe("shadow-proof values", () => {
    it("writes undefined, NaN and Infinity so that no binding of the name changes them", () => {
        const names = { declaresName: (name: string) => name === "undefined" || name === "NaN" || name === "Infinity" };
        const printed = (value: undefined | number) => {
            const program = parse("x = 0;");
            const statement = program.body[0] as Node & { expression: { right: Node } };
            statement.expression.right = valueToNode(value, [0, 0], names);
            return print(program);
        };
        expect(printed(undefined)).toBe("x = void 0;\n");
        expect(printed(Number.NaN)).toBe("x = (0 / 0);\n");
        expect(printed(-Infinity)).toBe("x = -1e999;\n");
        const free = { declaresName: () => false };
        expect(valueToNode(undefined, [0, 0], free)).toMatchObject({ type: "Identifier", name: "undefined" });
        expect(valueToNode(undefined, [0, 0])).toMatchObject({ type: "UnaryExpression", operator: "void" });
    });

    it("a decoder result undefined stays undefined under a parameter named undefined", async () => {
        const code = `function d(k) { return [1, void 0, 0 / 0][k]; }
function f(undefined, NaN) { return [d(1), d(2)]; }
result = f(5, 6);
`;
        const output = (await deobfuscate(code)).code;
        expect(output).not.toContain("d(1)");
        expect(observe(output)).toBe(observe(code));
    });
});

describe("huge and deep inputs", () => {
    it("splits a 300k-term comma statement", async () => {
        const code = `var a = 0;\n${"a,".repeat(300_000)}a;\n`;
        const output = (await deobfuscate(code, { passes: ["normalize"] })).code;
        expect(output.split("\n").filter((line) => line === "a;")).toHaveLength(300_001);
    });

    it("list edits take any number of items", () => {
        const list = [1, 2, 3];
        const many = Array.from({ length: 500_000 }, (_, i) => i);
        spliceList(list, 1, 1, many);
        expect(list.length).toBe(500_002);
        expect([list[0], list[1], list[500_000], list[500_001]]).toEqual([1, 0, 499_999, 3]);
        spliceList(list, 1, 500_000, [9]);
        expect(list).toEqual([1, 9, 3]);
        spliceList(list, 3, 5, [4]);
        expect(list).toEqual([1, 9, 3, 4]);
        pushAll(list, many);
        expect(list.length).toBe(500_004);
    });

    it("a nesting deeper than the stack fails with a clear error", () => {
        let node: Node = { type: "Literal", value: 1, raw: "1", start: 0, end: 0 } as Node;
        for (let i = 0; i < 200_000; i++) node = { type: "ArrayExpression", elements: [node], start: 0, end: 0 } as Node;
        expect(() => traverse(node, { enter() {} })).toThrow(NestingError);
        const program = { type: "Program", body: [{ type: "ExpressionStatement", expression: node, start: 0, end: 0 }], sourceType: "script", hashbang: null, comments: [], start: 0, end: 0 };
        expect(() => print(program as never)).toThrow(NestingError);
    });
});

describe("cli output files", () => {
    let dir: string;
    beforeEach(async () => {
        dir = await fs.mkdtemp(path.join(os.tmpdir(), "jsd-out-"));
    });
    afterEach(async () => {
        await fs.rm(dir, { recursive: true, force: true });
    });

    const cli = async (argv: string[]) => {
        let stderr = "";
        const code = await runCli(argv, { cwd: dir, stdout: () => {}, stdoutIsTTY: false, stderr: (text) => (stderr += text), readStdin: async () => "", stdinIsTTY: true, version: "0" });
        return { code, stderr };
    };
    const write = async (relative: string, content: string) => {
        await fs.mkdir(path.dirname(path.join(dir, relative)), { recursive: true });
        await fs.writeFile(path.join(dir, relative), content);
    };

    it("never overwrites a report without --force", async () => {
        await write("in.js", "x=1");
        await write("report.json", "keep");
        const result = await cli(["in.js", "-o", "out.js", "--report", "report.json"]);
        expect(result.code).toBe(EXIT_FAILED);
        expect(await fs.readFile(path.join(dir, "report.json"), "utf8")).toBe("keep");
        expect((await cli(["in.js", "-o", "out2.js", "--report", "report.json", "--force"])).code).toBe(EXIT_OK);
        expect(await fs.readFile(path.join(dir, "report.json"), "utf8")).toContain('"files"');
    });

    it("never overwrites dump files without --force", async () => {
        await write("in.js", "x=1");
        expect((await cli(["in.js", "-o", "a.js", "--dump-dir", "dump"])).code).toBe(EXIT_OK);
        expect((await cli(["in.js", "-o", "b.js", "--dump-dir", "dump"])).code).toBe(EXIT_FAILED);
        expect((await cli(["in.js", "-o", "c.js", "--dump-dir", "dump", "--force"])).code).toBe(EXIT_OK);
    });

    it("leaves no temporary files", async () => {
        await write("src/a.js", "a=1");
        expect((await cli(["src", "-o", "out"])).code).toBe(EXIT_OK);
        expect(await fs.readdir(path.join(dir, "out"))).toEqual(["a.js"]);
    });

    it("refuses a symbolic link as output, even with --force", async (context) => {
        await write("in.js", "x=1");
        await write("elsewhere.js", "keep");
        try {
            await fs.symlink(path.join(dir, "elsewhere.js"), path.join(dir, "out.js"));
        } catch {
            context.skip();
        }
        const result = await cli(["in.js", "-o", "out.js", "--force"]);
        expect(result.code).toBe(EXIT_FAILED);
        expect(result.stderr).toContain("symbolic link");
        expect(await fs.readFile(path.join(dir, "elsewhere.js"), "utf8")).toBe("keep");
    });

    it("refuses an output directory that is the input directory under another name", async (context) => {
        await write("src/a.js", "a=1");
        try {
            await fs.symlink(path.join(dir, "src"), path.join(dir, "alias"), "junction");
        } catch {
            context.skip();
        }
        const result = await cli(["src", "-o", "alias", "--force"]);
        expect(result.code).toBe(EXIT_USAGE);
        expect(await fs.readFile(path.join(dir, "src/a.js"), "utf8")).toBe("a=1");
    });

    it("refuses targets that differ only in case", async (context) => {
        await write("src/A.js", "a=1");
        await write("src/a.js", "b=2");
        if ((await fs.readdir(path.join(dir, "src"))).length < 2) context.skip();
        const result = await cli(["src", "-o", "out"]);
        expect(result.code).toBe(EXIT_USAGE);
        expect(result.stderr).toContain("differ only in case");
    });

    it("quotes file names in progress lines", async (context) => {
        try {
            await write("src/a\u001b]0;x.js", "a=1");
        } catch {
            context.skip();
        }
        const result = await cli(["src", "-o", "out"]);
        expect(result.code).toBe(EXIT_OK);
        expect(result.stderr).not.toMatch(UNSAFE);
        expect(result.stderr).toContain('ok: "src');
    });
});
