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
    readonly filename?: string;
    readonly logger?: Logger;
    /** Called once with the parsed input printed back, before any pass runs. */
    readonly beforePasses?: (code: string) => void;
    /** Printing costs time, so only set this when needed. */
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

/** Throws `ParseError` on unparsable input and `UnknownPassError` for bad pass names. */
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
        code: print(program, (message) => logger.warn(`[print] ${message}`)),
        report: { passes: reports, durationMs: performance.now() - start },
    };
};
