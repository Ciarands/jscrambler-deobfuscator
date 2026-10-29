/**
 * Run the pipeline over a folder of obfuscated samples (kept outside this repo) and record what happened.
 *
 *   npm run corpus -- [samplesDir] [--only a,b] [--dump] [--passes x,y] [--skip x,y] [--out dir]
 *
 * samplesDir defaults to $SAMPLES_DIR, then ../jscrambler-samples. For each sample this writes to <out>/<name>/
 * (out defaults to .corpus):
 *   out.js       final output
 *   log.txt      every log line (debug level), with source locations
 *   passes/      with --dump: the code after each pass (00-input.js, 01-<pass>.js, ...)
 * and prints a metrics table, with the change since the previous run (.corpus/summary.json).
 */
import { existsSync, mkdirSync, readdirSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import path from "node:path";
import { parseArgs } from "node:util";
import { dumpHooks } from "../src/cli/dump.js";
import { deobfuscate } from "../src/deobfuscate.js";
import { createLogger } from "../src/logger.js";
import type { Counted, Metrics } from "./metrics.js";
import { COUNTED, errorMetrics, measure } from "./metrics.js";

const { values, positionals } = parseArgs({
    allowPositionals: true,
    options: { only: { type: "string" }, dump: { type: "boolean" }, passes: { type: "string" }, skip: { type: "string" }, out: { type: "string" } },
});
const list = (value: string | undefined) =>
    value
        ?.split(",")
        .map((s) => s.trim())
        .filter(Boolean);

const samplesDir = path.resolve(positionals[0] ?? process.env["SAMPLES_DIR"] ?? "../jscrambler-samples");
const outRoot = path.resolve(values.out ?? ".corpus");
const only = list(values.only);

const summaryPath = path.join(outRoot, "summary.json");
const previous: Record<string, Metrics> = existsSync(summaryPath) ? JSON.parse(readFileSync(summaryPath, "utf8")) : {};
const summary: Record<string, Metrics> = { ...previous };

const files = readdirSync(samplesDir)
    .filter((file) => file.endsWith(".js"))
    .filter((file) => only === undefined || only.some((name) => file.includes(name)))
    .toSorted();

const rows: string[][] = [];
for (const file of files) {
    const name = path.basename(file, ".js");
    const dir = path.join(outRoot, name);
    rmSync(dir, { recursive: true, force: true });
    mkdirSync(dir, { recursive: true });
    const lines: string[] = [];
    const logger = createLogger("debug", (line) => lines.push(line));
    const code = readFileSync(path.join(samplesDir, file), "utf8");
    const start = performance.now();
    let metrics: Metrics;
    try {
        const result = await deobfuscate(code, {
            filename: file,
            logger,
            passes: list(values.passes),
            skip: list(values.skip),
            ...(values.dump ? dumpHooks(path.join(dir, "passes")) : {}),
        });
        const ms = performance.now() - start;
        writeFileSync(path.join(dir, "out.js"), result.code);
        metrics = measure(result.code, ms);
    } catch (error) {
        metrics = errorMetrics(performance.now() - start, error);
        lines.push(`ERROR ${String(error)}`);
    }
    writeFileSync(path.join(dir, "log.txt"), `${lines.join("\n")}\n`);
    summary[name] = metrics;

    const before = previous[name];
    const delta = (key: Counted) => {
        const now = metrics[key];
        const was = before?.[key];
        return was === undefined || was === now ? String(now) : `${now} (${now - was > 0 ? "+" : ""}${now - was})`;
    };
    rows.push([name, metrics.error ? `ERROR ${metrics.error.slice(0, 60)}` : delta("bytes"), String(metrics.ms), ...COUNTED.slice(1).map(delta)]);
}

writeFileSync(summaryPath, `${JSON.stringify(summary, null, 2)}\n`);
const header = ["sample", "bytes", "ms", ...COUNTED.slice(1)];
const widths = header.map((h, i) => Math.max(h.length, ...rows.map((r) => (r[i] ?? "").length)));
const fmt = (row: string[]) => row.map((cell, i) => cell.padEnd(widths[i] ?? 0)).join("  ");
console.log(fmt(header));
for (const row of rows) console.log(fmt(row));
console.log(`\nlogs and output: ${path.relative(process.cwd(), outRoot)}/<sample>/`);
