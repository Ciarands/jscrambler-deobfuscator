import type { Program } from "../core/ast.js";
import type { PassLog } from "../core/log.js";
import type { ScopeInfo } from "../core/scope.js";
import type { Facts } from "./facts.js";

export interface PassContext {
    readonly program: Program;
    readonly log: PassLog;
    readonly facts: Facts;
    /** Computed on first use; redone after binding changes, refreshed after expression-only changes. */
    scope(): ScopeInfo;
}

export interface PassResult {
    /** 0 means the program is untouched. */
    readonly changed: number;
    /**
     * `false` when changes only replaced expressions in place (no declaration added/removed, nothing moved scope): the
     * scope analysis is then refreshed instead of redone. Also `false` when the only new declarations belong to a new
     * function whose code names nothing but them: nothing outside can reach them, and identifiers the analysis
     * doesn't know resolve to nothing, as for any node made since the last refresh. Defaults to true.
     */
    readonly bindingsChanged?: boolean;
    readonly stats?: Readonly<Record<string, number>>;
}

export interface Pass {
    readonly name: string;
    readonly description: string;
    run(context: PassContext): PassResult | Promise<PassResult>;
}

/** Passes run in order, repeatedly, until a full round changes nothing. */
export interface FixpointGroup {
    readonly group: string;
    readonly passes: readonly Pass[];
    /** Hitting it is logged as a warning. */
    readonly maxRounds: number;
}

export type PipelineStep = Pass | FixpointGroup;

export const isGroup = (step: PipelineStep): step is FixpointGroup => "group" in step;
