import type { Program } from "../core/ast.js";
import { createPassLog } from "../core/log.js";
import type { SourceMap } from "../core/log.js";
import { ScopeInfo } from "../core/scope.js";
import type { Logger } from "../logger.js";
import { isGroup } from "./pass.js";
import type { Pass, PipelineStep } from "./pass.js";
import { Facts } from "./facts.js";

export interface PassSelection {
    /** Only run these passes. Omit to run every pass. */
    readonly passes?: readonly string[] | undefined;
    /** Skip these passes. */
    readonly skip?: readonly string[] | undefined;
}

export interface PassReport {
    readonly name: string;
    /** Fixpoint group the pass ran in, if any. */
    readonly group?: string;
    /** 1-based round within the group. */
    readonly round?: number;
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

/** Every pass in a pipeline, groups flattened, in order. */
export const passesOf = (steps: readonly PipelineStep[]): readonly Pass[] => steps.flatMap((step) => (isGroup(step) ? step.passes : [step]));

/** Keep the selected passes (dropping groups that end up empty). Throws on names that don't exist. */
export const selectPasses = (steps: readonly PipelineStep[], selection: PassSelection): readonly PipelineStep[] => {
    const names = new Set(passesOf(steps).map((pass) => pass.name));
    const requested = [...(selection.passes ?? []), ...(selection.skip ?? [])];
    const unknown = [...new Set(requested.filter((name) => !names.has(name)))];
    if (unknown.length > 0) throw new UnknownPassError(unknown, [...names]);

    const only = selection.passes ? new Set(selection.passes) : undefined;
    const skip = new Set(selection.skip ?? []);
    const keep = (pass: Pass): boolean => (only === undefined || only.has(pass.name)) && !skip.has(pass.name);
    return steps.flatMap((step): PipelineStep[] => {
        if (!isGroup(step)) return keep(step) ? [step] : [];
        const passes = step.passes.filter(keep);
        return passes.length > 0 ? [{ ...step, passes }] : [];
    });
};

export interface RunOptions {
    readonly logger: Logger;
    readonly source: SourceMap;
    /** Called after every pass run, e.g. to dump the program for inspection. */
    readonly afterPass?: ((report: PassReport, program: Program) => void) | undefined;
}

export const runPipeline = async (program: Program, steps: readonly PipelineStep[], options: RunOptions): Promise<readonly PassReport[]> => {
    const reports: PassReport[] = [];
    const facts = new Facts();
    let scope: ScopeInfo | undefined;
    /** The cached analysis predates expression-only changes: refreshed (removed references dropped) on next use. */
    let stale = false;
    const currentScope = (): ScopeInfo => {
        if (scope === undefined) scope = new ScopeInfo(program);
        else if (stale) scope.refresh(program);
        stale = false;
        return scope;
    };

    const runPass = async (pass: Pass, group?: { name: string; round: number }): Promise<PassReport> => {
        const log = createPassLog(pass.name, options.logger, options.source);
        const start = performance.now();
        const result = await pass.run({
            program,
            log,
            facts,
            scope: currentScope,
        });
        if (result.changed > 0) {
            if (result.bindingsChanged === false) {
                stale = true;
            } else {
                scope = undefined;
                stale = false;
            }
        }
        const report: PassReport = {
            name: pass.name,
            ...(group === undefined ? {} : { group: group.name, round: group.round }),
            changed: result.changed,
            durationMs: performance.now() - start,
            stats: result.stats ?? {},
        };
        const stats = Object.entries(report.stats)
            .map(([key, value]) => `${key}=${value}`)
            .join(" ");
        const where = group === undefined ? "" : ` (${group.name} round ${group.round})`;
        options.logger.info(`[${pass.name}] ${report.changed} change(s) in ${report.durationMs.toFixed(0)}ms${where}${stats ? `: ${stats}` : ""}`);
        reports.push(report);
        options.afterPass?.(report, program);
        return report;
    };

    try {
        for (const step of steps) {
            if (!isGroup(step)) {
                await runPass(step);
                continue;
            }
            // A pass whose last run changed nothing, with nothing changed since, would change nothing again: passes
            // are deterministic, and facts only change outside groups (emulate).
            let version = 0;
            const quietAt = new Map<Pass, number>();
            let round = 1;
            for (; round <= step.maxRounds; round++) {
                let changed = 0;
                for (const pass of step.passes) {
                    if (quietAt.get(pass) === version) continue;
                    const report = await runPass(pass, { name: step.group, round });
                    if (report.changed > 0) {
                        version++;
                        quietAt.delete(pass);
                    } else {
                        quietAt.set(pass, version);
                    }
                    changed += report.changed;
                }
                if (changed === 0) break;
            }
            if (round > step.maxRounds) options.logger.warn(`[${step.group}] still changing after ${step.maxRounds} rounds, stopped`);
        }
    } finally {
        facts.dispose();
    }
    return reports;
};
