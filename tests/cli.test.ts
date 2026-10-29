import fs from "node:fs/promises";
import os from "node:os";
import path from "node:path";
import { afterEach, beforeEach, describe, expect, it } from "vitest";
import { EXIT_FAILED, EXIT_OK, EXIT_USAGE, runCli } from "../src/cli/main.js";

let dir: string;

beforeEach(async () => {
    dir = await fs.mkdtemp(path.join(os.tmpdir(), "jsd-cli-"));
});

afterEach(async () => {
    await fs.rm(dir, { recursive: true, force: true });
});

const write = async (relative: string, content: string): Promise<string> => {
    const full = path.join(dir, relative);
    await fs.mkdir(path.dirname(full), { recursive: true });
    await fs.writeFile(full, content);
    return full;
};

const read = (relative: string): Promise<string> => fs.readFile(path.join(dir, relative), "utf8");

const run = async (argv: string[], stdin?: string) => {
    let stdout = "";
    let stderr = "";
    const code = await runCli(argv, {
        cwd: dir,
        stdout: (text) => (stdout += text),
        stderr: (text) => (stderr += text),
        readStdin: async () => stdin ?? "",
        stdinIsTTY: stdin === undefined,
        version: "9.9.9",
    });
    return { code, stdout, stderr };
};

describe("cli", () => {
    it("writes a single file to stdout", async () => {
        await write("in.js", "x=1+2");
        const result = await run(["in.js"]);
        expect(result.code).toBe(EXIT_OK);
        expect(result.stdout).toBe("x = 3;\n");
        expect(result.stderr).toBe("");
    });

    it("reads stdin when no input is given", async () => {
        const result = await run([], "y=2");
        expect(result.code).toBe(EXIT_OK);
        expect(result.stdout).toBe("y = 2;\n");
    });

    it("fails with usage when there is no input and stdin is a terminal", async () => {
        const result = await run([]);
        expect(result.code).toBe(EXIT_USAGE);
        expect(result.stderr).toContain("Usage:");
    });

    it("refuses to overwrite an existing output file unless forced", async () => {
        await write("in.js", "x=1");
        await write("out.js", "keep me");
        const refused = await run(["in.js", "-o", "out.js"]);
        expect(refused.code).toBe(EXIT_FAILED);
        expect(refused.stderr).toContain("already exists, use --force");
        expect(await read("out.js")).toBe("keep me");

        const forced = await run(["in.js", "-o", "out.js", "--force"]);
        expect(forced.code).toBe(EXIT_OK);
        expect(await read("out.js")).toBe("x = 1;\n");
    });

    it("mirrors a directory, skipping non-source files, node_modules and its own output", async () => {
        await write("src/a.js", "a=1");
        await write("src/nested/b.mjs", "export const b=2");
        await write("src/readme.txt", "not code");
        await write("src/node_modules/dep.js", "dep=1");
        await write("src/out/old.js", "old=1");
        const result = await run(["src", "-o", "src/out"]);
        expect(result.code).toBe(EXIT_OK);
        expect(await read("src/out/a.js")).toBe("a = 1;\n");
        expect(await read("src/out/nested/b.mjs")).toBe("export const b = 2;\n");
        await expect(read("src/out/readme.txt")).rejects.toThrow();
        await expect(read("src/out/node_modules/dep.js")).rejects.toThrow();
        await expect(read("src/out/out/old.js")).rejects.toThrow();
        expect(result.stderr).toContain("2 file(s): 2 ok, 0 failed");
    });

    it("needs -o for a directory and won't write over the input directory", async () => {
        await write("src/a.js", "a=1");
        expect((await run(["src"])).code).toBe(EXIT_USAGE);
        expect((await run(["src", "-o", "src"])).code).toBe(EXIT_USAGE);
    });

    it("checks every target before writing anything in a batch", async () => {
        await write("src/a.js", "a=1");
        await write("src/b.js", "b=1");
        await write("out/b.js", "keep me");
        const result = await run(["src", "-o", "out"]);
        expect(result.code).toBe(EXIT_FAILED);
        await expect(read("out/a.js")).rejects.toThrow();
        expect(await read("out/b.js")).toBe("keep me");
    });

    it("keeps going past a broken file and exits 1", async () => {
        await write("src/a.js", "a=1");
        await write("src/broken.js", "var x = ;");
        await write("src/c.js", "c=3");
        const result = await run(["src", "-o", "out"]);
        expect(result.code).toBe(EXIT_FAILED);
        expect(await read("out/a.js")).toBe("a = 1;\n");
        expect(await read("out/c.js")).toBe("c = 3;\n");
        expect(result.stderr).toMatch(/error: src[\\/]broken\.js: .*\(1:9\)/);
        expect(result.stderr).toContain("3 file(s): 2 ok, 1 failed");
    });

    it("still prints errors with --quiet, and nothing else", async () => {
        await write("src/a.js", "a=1");
        await write("src/broken.js", "var x = ;");
        const result = await run(["src", "-o", "out", "--quiet"]);
        expect(result.code).toBe(EXIT_FAILED);
        expect(result.stderr.trim().split("\n")).toEqual([expect.stringMatching(/^error: src[\\/]broken\.js/)]);
    });

    it("rejects unknown passes and flags with a usage error", async () => {
        await write("in.js", "x=1");
        expect((await run(["in.js", "--passes", "nope"])).code).toBe(EXIT_USAGE);
        expect((await run(["in.js", "--skip", "nope"])).code).toBe(EXIT_USAGE);
        expect((await run(["in.js", "--bogus"])).code).toBe(EXIT_USAGE);
        expect((await run(["in.js", "-q", "-v"])).code).toBe(EXIT_USAGE);
        expect((await run(["missing.js"])).code).toBe(EXIT_USAGE);
    });

    it("writes a JSON report with one entry per file", async () => {
        await write("src/a.js", "a=1");
        await write("src/broken.js", "var x = ;");
        await run(["src", "-o", "out", "--report", "report.json"]);
        const report = JSON.parse(await read("report.json")) as { files: { input: string; ok: boolean; error?: string }[] };
        expect(report.files.map((file) => [file.input.replaceAll("\\", "/"), file.ok])).toEqual([
            ["src/a.js", true],
            ["src/broken.js", false],
        ]);
        expect(report.files[1]?.error).toContain("(1:9)");
    });

    it("prints help and version", async () => {
        expect((await run(["--help"])).stdout).toContain("Usage:");
        expect((await run(["--version"])).stdout).toBe("9.9.9\n");
    });
});
