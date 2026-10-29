import type { Program } from "./core/ast.js";
import { SourceMap } from "./core/log.js";
import { parse } from "./core/parse.js";
import { print } from "./core/print.js";
import { silentLogger } from "./logger.js";
import type { Logger } from "./logger.js";
import { PIPELINE } from "./passes/index.js";
import { runPipeline, selectPasses } from "./pipeline/run.js";
import type { PassReport, PassSelection } from "./pipeline/run.js";

export interface DeobfuscateOptions extends PassSelection {
    /** Used in parse error messages. */
    readonly filename?: string;
    /** Defaults to a logger that prints nothing. */
    readonly logger?: Logger;
    /** Called once with the parsed input printed back, before any pass runs. For diffing against `afterPass` dumps. */
    readonly beforePasses?: (code: string) => void;
    /** Called after every pass run with the code at that point. Printing costs time, so only set this when needed. */
    readonly afterPass?: (report: PassReport, code: string) => void;
}

export interface DeobfuscateReport {
    readonly passes: readonly PassReport[];
    readonly durationMs: number;
}

export interface DeobfuscateResult {
    readonly code: string;
    readonly report: DeobfuscateReport;
}

/**
 * Deobfuscate one script or module.
 *
 * Throws `ParseError` when the input doesn't parse and `UnknownPassError` for bad pass names.
 * Async so the same API can run on the WASM parser in a browser later.
 */
export const deobfuscate = async (code: string, options: DeobfuscateOptions = {}): Promise<DeobfuscateResult> => {
    const start = performance.now();
    const logger = options.logger ?? silentLogger;
    const steps = selectPasses(PIPELINE, options);
    const program = parse(code, options.filename);
    options.beforePasses?.(print(program));
    const afterPass = options.afterPass;
    const reports = await runPipeline(program, steps, {
        logger,
        source: new SourceMap(code),
        afterPass: afterPass === undefined ? undefined : (report: PassReport, current: Program) => afterPass(report, print(current)),
    });
    return {
        code: print(program),
        report: { passes: reports, durationMs: performance.now() - start },
    };
};
