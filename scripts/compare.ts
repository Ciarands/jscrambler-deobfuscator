/**
 * Compare this rewrite with `main` on a folder of obfuscated samples (kept outside this repo).
 *
 *   npm run build && npx tsx scripts/compare.ts [samplesDir] [--main ../jsd-main] [--only a,b]
 *
 * `--main` is a worktree of the `main` branch with its dependencies installed (never modified). Both tools run each
 * sample end to end (read, deobfuscate, write) with logging off, one after the other in this process. The rewrite runs
 * from `dist/` (the build users run; it must be newer than every source file). Outputs go to
 * .compare/<sample>/{main.js,rewrite.js}; the table shows wall clock and the shared metrics for both, and whether the
 * rewrite is faster and no worse on machines, switches and deep calls.
 */
import { mkdirSync, readdirSync, readFileSync, rmSync, statSync, writeFileSync } from "node:fs";
import path from "node:path";
import { pathToFileURL } from "node:url";
import { parseArgs } from "node:util";
import type { deobfuscate as Deobfuscate } from "../src/index.js";
import type { Metrics } from "./metrics.js";
import { errorMetrics, measure } from "./metrics.js";

/** Newest modification time of the files under `dir`. */
const newest = (dir: string): number =>
    Math.max(...readdirSync(dir, { withFileTypes: true }).map((entry) => (entry.isDirectory() ? newest(path.join(dir, entry.name)) : statSync(path.join(dir, entry.name)).mtimeMs)));
const built = path.resolve("dist/index.js");
if (statSync(built, { throwIfNoEntry: false }) === undefined || statSync(built).mtimeMs < newest(path.resolve("src"))) {
    throw new Error("dist/ is missing or older than src/: run `npm run build` first");
}
const { deobfuscate } = (await import(pathToFileURL(built).href)) as { deobfuscate: typeof Deobfuscate };

const { values, positionals } = parseArgs({ allowPositionals: true, options: { main: { type: "string" }, only: { type: "string" } } });
const samplesDir = path.resolve(positionals[0] ?? process.env["SAMPLES_DIR"] ?? "../jscrambler-samples");
const mainDir = path.resolve(values.main ?? "../jsd-main");
const only = values.only?.split(",").map((s) => s.trim());
const outRoot = path.resolve(".compare");

type ProcessSample = (input: string, output: string) => Promise<boolean>;
// The `main` worktree's location is chosen at run time (`--main`), so this import can't be static.
const { processSample } = (await import(pathToFileURL(path.join(mainDir, "src/deobfuscator.js")).href)) as { processSample: ProcessSample };

const ignore = () => {};
const ok = (better: boolean) => (better ? "ok" : "WORSE");

/** `main` narrates every step on the console; keep that out of the table, but keep what it reports as errors. */
const quietly = async <T>(run: () => Promise<T>): Promise<{ result: T; errors: string[] }> => {
    const errors: string[] = [];
    const saved = { log: console.log, warn: console.warn, error: console.error };
    const capture = (...args: unknown[]) => void errors.push(args.map(String).join(" "));
    Object.assign(console, { log: ignore, warn: ignore, error: capture });
    try {
        return { result: await run(), errors };
    } finally {
        Object.assign(console, saved);
    }
};

const runMain = async (input: string, output: string): Promise<Metrics> => {
    const start = performance.now();
    const { result, errors } = await quietly(() => processSample(input, output));
    const ms = performance.now() - start;
    if (!result) return errorMetrics(ms, errors.join(" | ") || "main reported a failure");
    return measure(readFileSync(output, "utf8"), ms);
};

const runRewrite = async (input: string, output: string): Promise<Metrics> => {
    const start = performance.now();
    try {
        const { code } = await deobfuscate(readFileSync(input, "utf8"), { filename: path.basename(input) });
        writeFileSync(output, code);
        return measure(code, performance.now() - start);
    } catch (error) {
        return errorMetrics(performance.now() - start, error);
    }
};

/** Per criterion: faster, and no worse on machines, switches, deep calls. */
const verdict = (main: Metrics, rewrite: Metrics): string => {
    if (rewrite.error !== undefined) return `rewrite ERROR ${rewrite.error.slice(0, 60)}`;
    if (main.error !== undefined) return `main ERROR ${main.error.slice(0, 60)}`;
    return [
        `speed ${ok(rewrite.ms < main.ms)}`,
        `machines ${ok(rewrite.machines <= main.machines)}`,
        `switches ${ok(rewrite.switches <= main.switches)}`,
        `deep calls ${ok(rewrite.deepCalls <= main.deepCalls)}`,
    ].join(", ");
};

const files = readdirSync(samplesDir)
    .filter((file) => file.endsWith(".js") && (only === undefined || only.some((name) => file.includes(name))))
    .toSorted();

const rows: string[][] = [];
const results: Record<string, { main: Metrics; rewrite: Metrics }> = {};
for (const file of files) {
    const name = path.basename(file, ".js");
    const dir = path.join(outRoot, name);
    rmSync(dir, { recursive: true, force: true });
    mkdirSync(dir, { recursive: true });
    const input = path.join(samplesDir, file);
    const main = await runMain(input, path.join(dir, "main.js"));
    const rewrite = await runRewrite(input, path.join(dir, "rewrite.js"));
    results[name] = { main, rewrite };
    rows.push([
        name,
        `${main.ms} / ${rewrite.ms}`,
        `${main.machines} / ${rewrite.machines}`,
        `${main.switches} / ${rewrite.switches}`,
        `${main.deepCalls} / ${rewrite.deepCalls}`,
        `${main.bytes} / ${rewrite.bytes}`,
        verdict(main, rewrite),
    ]);
}

writeFileSync(path.join(outRoot, "compare.json"), `${JSON.stringify(results, null, 2)}\n`);
const header = ["sample", "ms main / rewrite", "machines", "switches", "deep calls", "bytes", "verdict"];
const widths = header.map((h, i) => Math.max(h.length, ...rows.map((r) => (r[i] ?? "").length)));
const fmt = (row: string[]) => row.map((cell, i) => cell.padEnd(widths[i] ?? 0)).join("  ");
console.log(fmt(header));
for (const row of rows) console.log(fmt(row));
console.log(`\noutputs: ${path.relative(process.cwd(), outRoot)}/<sample>/{main,rewrite}.js`);
