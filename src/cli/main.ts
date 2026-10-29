import fs from "node:fs/promises";
import path from "node:path";
import { parseArgs } from "node:util";
import { ParseError } from "../core/parse.js";
import { deobfuscate } from "../deobfuscate.js";
import type { DeobfuscateReport } from "../deobfuscate.js";
import { createLogger } from "../logger.js";
import type { Logger, LogLevel } from "../logger.js";
import { ALL_PASSES } from "../passes/index.js";
import { selectPasses, UnknownPassError } from "../pipeline/run.js";
import type { PassSelection } from "../pipeline/run.js";

export const EXIT_OK = 0;
export const EXIT_FAILED = 1;
export const EXIT_USAGE = 2;

export interface CliEnv {
    readonly cwd: string;
    readonly stdout: (text: string) => void;
    readonly stderr: (text: string) => void;
    readonly readStdin: () => Promise<string>;
    readonly stdinIsTTY: boolean;
    readonly version: string;
}

const USAGE = `Usage: jscrambler-deobfuscator [input] [options]

Deobfuscates a file, every .js/.mjs/.cjs file in a directory, or stdin when no input is given.
Output goes to stdout unless -o is set.

Options:
  -o, --output <path>    Output file, or output directory when the input is a directory
  -f, --force            Overwrite existing output files
      --passes <list>    Only run these passes (comma-separated)
      --skip <list>      Skip these passes (comma-separated)
      --list-passes      Print the available passes and exit
      --report <file>    Write a JSON report to <file>
  -q, --quiet            Only print errors
  -v, --verbose          Print debug output, including parse error code frames
  -h, --help             Print this help and exit
      --version          Print the version and exit

Exit codes: 0 success, 1 a file failed, 2 usage error.
`;

const SOURCE_EXTENSIONS: Record<string, true> = { ".js": true, ".mjs": true, ".cjs": true };

interface FileResult {
    readonly input: string;
    readonly output: string;
    readonly ok: boolean;
    readonly error?: string;
    readonly report?: DeobfuscateReport;
}

class UsageError extends Error {}

const splitList = (value: string | undefined): string[] | undefined =>
    value === undefined
        ? undefined
        : value
              .split(",")
              .map((name) => name.trim())
              .filter((name) => name.length > 0);

const errorMessage = (error: unknown): string => (error instanceof Error ? error.message : String(error));

const exists = async (target: string): Promise<boolean> => {
    try {
        await fs.access(target);
        return true;
    } catch {
        return false;
    }
};

const isInside = (child: string, parent: string): boolean => {
    const relative = path.relative(parent, child);
    return relative === "" || (!relative.startsWith("..") && !path.isAbsolute(relative));
};

/** Every source file under `root`, skipping node_modules and `exclude` (the output directory). */
const collectSources = async (root: string, exclude: string): Promise<string[]> => {
    const found: string[] = [];
    const walk = async (dir: string): Promise<void> => {
        const entries = await fs.readdir(dir, { withFileTypes: true });
        entries.sort((a, b) => a.name.localeCompare(b.name));
        for (const entry of entries) {
            const full = path.join(dir, entry.name);
            if (entry.isDirectory()) {
                if (entry.name !== "node_modules" && !isInside(full, exclude)) await walk(full);
            } else if (entry.isFile() && SOURCE_EXTENSIONS[path.extname(entry.name)] === true) {
                found.push(full);
            }
        }
    };
    await walk(root);
    return found;
};

const logFailure = (logger: Logger, label: string, error: unknown): void => {
    logger.error(`error: ${label}: ${errorMessage(error)}`);
    if (error instanceof ParseError) for (const frame of error.codeframes) logger.debug(frame);
};

export const runCli = async (argv: readonly string[], env: CliEnv): Promise<number> => {
    let values;
    let positionals;
    try {
        ({ values, positionals } = parseArgs({
            args: [...argv],
            allowPositionals: true,
            strict: true,
            options: {
                output: { type: "string", short: "o" },
                force: { type: "boolean", short: "f" },
                passes: { type: "string" },
                skip: { type: "string" },
                "list-passes": { type: "boolean" },
                report: { type: "string" },
                quiet: { type: "boolean", short: "q" },
                verbose: { type: "boolean", short: "v" },
                help: { type: "boolean", short: "h" },
                version: { type: "boolean" },
            },
        }));
    } catch (error) {
        env.stderr(`${errorMessage(error)}\n\n${USAGE}`);
        return EXIT_USAGE;
    }

    if (values.help) {
        env.stdout(USAGE);
        return EXIT_OK;
    }
    if (values.version) {
        env.stdout(`${env.version}\n`);
        return EXIT_OK;
    }
    if (values["list-passes"]) {
        for (const pass of ALL_PASSES) env.stdout(`${pass.name}\t${pass.description}\n`);
        return EXIT_OK;
    }

    const level: LogLevel = values.quiet ? "error" : values.verbose ? "debug" : "info";
    const logger = createLogger(level, (line) => env.stderr(`${line}\n`));
    const selection: PassSelection = { passes: splitList(values.passes), skip: splitList(values.skip) };

    try {
        if (values.quiet && values.verbose) throw new UsageError("--quiet and --verbose can't be used together");
        if (positionals.length > 1) throw new UsageError(`Expected at most one input, got ${positionals.length}`);
        selectPasses(ALL_PASSES, selection);

        const outputPath = values.output === undefined ? undefined : path.resolve(env.cwd, values.output);
        const options = { force: values.force === true, outputPath, selection, logger, env };
        const input = positionals[0];
        const results = input === undefined ? await runStdin(options) : await runPath(path.resolve(env.cwd, input), options);

        if (values.report !== undefined) {
            const reportPath = path.resolve(env.cwd, values.report);
            await fs.mkdir(path.dirname(reportPath), { recursive: true });
            await fs.writeFile(reportPath, `${JSON.stringify({ files: results }, null, 2)}\n`);
        }
        return results.every((result) => result.ok) ? EXIT_OK : EXIT_FAILED;
    } catch (error) {
        if (error instanceof UsageError || error instanceof UnknownPassError) {
            env.stderr(`${error.message}\n`);
            return EXIT_USAGE;
        }
        logger.error(`error: ${errorMessage(error)}`);
        return EXIT_FAILED;
    }
};

interface RunOptions {
    readonly force: boolean;
    readonly outputPath: string | undefined;
    readonly selection: PassSelection;
    readonly logger: Logger;
    readonly env: CliEnv;
}

const display = (env: CliEnv, target: string): string => path.relative(env.cwd, target) || ".";

/** Deobfuscate `code` and write it to `outputPath`, or stdout when there is none. */
const runOne = async (code: string, label: string, filename: string, outputPath: string | undefined, run: RunOptions): Promise<FileResult> => {
    const output = outputPath === undefined ? "<stdout>" : display(run.env, outputPath);
    try {
        const result = await deobfuscate(code, { ...run.selection, filename, logger: run.logger });
        if (outputPath === undefined) {
            run.env.stdout(result.code);
        } else {
            await fs.mkdir(path.dirname(outputPath), { recursive: true });
            await fs.writeFile(outputPath, result.code);
        }
        return { input: label, output, ok: true, report: result.report };
    } catch (error) {
        logFailure(run.logger, label, error);
        return { input: label, output, ok: false, error: errorMessage(error) };
    }
};

const refuseOverwrite = async (targets: readonly string[], run: RunOptions): Promise<void> => {
    if (run.force) return;
    const existing: string[] = [];
    for (const target of targets) if (await exists(target)) existing.push(target);
    if (existing.length === 0) return;
    const first = display(run.env, existing[0] ?? "");
    const more = existing.length > 1 ? ` (and ${existing.length - 1} more)` : "";
    throw new Error(`${first}${more} already exists, use --force to overwrite`);
};

const runStdin = async (run: RunOptions): Promise<FileResult[]> => {
    if (run.env.stdinIsTTY) throw new UsageError(`No input given and stdin is a terminal\n\n${USAGE}`);
    if (run.outputPath !== undefined) await refuseOverwrite([run.outputPath], run);
    return [await runOne(await run.env.readStdin(), "<stdin>", "stdin.js", run.outputPath, run)];
};

const runPath = async (inputPath: string, run: RunOptions): Promise<FileResult[]> => {
    const stat = await fs.stat(inputPath).catch(() => undefined);
    if (stat === undefined) throw new UsageError(`No such file or directory: ${display(run.env, inputPath)}`);

    if (stat.isFile()) {
        if (run.outputPath !== undefined) await refuseOverwrite([run.outputPath], run);
        const label = display(run.env, inputPath);
        return [await runOne(await fs.readFile(inputPath, "utf8"), label, path.basename(inputPath), run.outputPath, run)];
    }

    const outputDir = run.outputPath;
    if (outputDir === undefined) throw new UsageError("A directory input needs -o <directory>");
    if (outputDir === inputPath) throw new UsageError("The output directory can't be the input directory");

    const sources = await collectSources(inputPath, outputDir);
    if (sources.length === 0) {
        run.logger.warn(`No .js/.mjs/.cjs files in ${display(run.env, inputPath)}`);
        return [];
    }
    const targets = sources.map((source) => path.join(outputDir, path.relative(inputPath, source)));
    await refuseOverwrite(targets, run);

    const results: FileResult[] = [];
    for (const [index, source] of sources.entries()) {
        const target = targets[index] ?? outputDir;
        const label = display(run.env, source);
        const result = await runOne(await fs.readFile(source, "utf8"), label, path.basename(source), target, run);
        if (result.ok) run.logger.info(`ok: ${label} -> ${result.output}`);
        results.push(result);
    }
    const failed = results.filter((result) => !result.ok).length;
    run.logger.info(`${results.length} file(s): ${results.length - failed} ok, ${failed} failed`);
    return results;
};
