import { parse } from "./core/parse.js";
import { print } from "./core/print.js";
import { silentLogger } from "./logger.js";
import type { Logger } from "./logger.js";
import { ALL_PASSES } from "./passes/index.js";
import { runPasses, selectPasses } from "./pipeline/run.js";
import type { PassReport, PassSelection } from "./pipeline/run.js";

export interface DeobfuscateOptions extends PassSelection {
    /** Used in parse error messages. */
    readonly filename?: string;
    /** Defaults to a logger that prints nothing. */
    readonly logger?: Logger;
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
    const passes = selectPasses(ALL_PASSES, options);
    const program = parse(code, options.filename);
    const reports = runPasses(program, passes, logger);
    return {
        code: print(program),
        report: { passes: reports, durationMs: performance.now() - start },
    };
};
