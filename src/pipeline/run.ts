import type { Program } from "oxc-parser";
import type { Logger } from "../logger.js";
import type { Pass } from "./pass.js";

export interface PassSelection {
    /** Only run these passes. Omit to run every pass. */
    readonly passes?: readonly string[] | undefined;
    /** Skip these passes. */
    readonly skip?: readonly string[] | undefined;
}

export interface PassReport {
    readonly name: string;
    readonly changed: number;
    readonly durationMs: number;
    readonly stats: Readonly<Record<string, number>>;
}

export class UnknownPassError extends Error {
    readonly unknown: readonly string[];

    constructor(unknown: readonly string[], available: readonly string[]) {
        const list = available.length > 0 ? available.join(", ") : "(none)";
        super(`Unknown pass${unknown.length > 1 ? "es" : ""}: ${unknown.join(", ")}. Available: ${list}`);
        this.name = "UnknownPassError";
        this.unknown = unknown;
    }
}

/** Pick the passes to run, keeping registry order. Throws on names that don't exist. */
export const selectPasses = (all: readonly Pass[], selection: PassSelection): readonly Pass[] => {
    const names = new Set(all.map((pass) => pass.name));
    const requested = [...(selection.passes ?? []), ...(selection.skip ?? [])];
    const unknown = [...new Set(requested.filter((name) => !names.has(name)))];
    if (unknown.length > 0) throw new UnknownPassError(unknown, [...names]);

    const only = selection.passes ? new Set(selection.passes) : undefined;
    const skip = new Set(selection.skip ?? []);
    return all.filter((pass) => (only === undefined || only.has(pass.name)) && !skip.has(pass.name));
};

export const runPasses = (program: Program, passes: readonly Pass[], logger: Logger): readonly PassReport[] =>
    passes.map((pass) => {
        const start = performance.now();
        const result = pass.run({ program, logger });
        const report: PassReport = {
            name: pass.name,
            changed: result.changed,
            durationMs: performance.now() - start,
            stats: result.stats ?? {},
        };
        logger.debug(`${pass.name}: ${report.changed} change(s) in ${report.durationMs.toFixed(1)}ms`);
        return report;
    });
