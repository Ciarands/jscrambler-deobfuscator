import type { Program } from "../core/ast.js";
import type { PassLog } from "../core/log.js";
import type { ScopeInfo } from "../core/scope.js";
import type { Facts } from "./facts.js";

export interface PassContext {
    readonly program: Program;
    /** Logs prefixed with the pass name; give it a node to print where that node was in the original input. */
    readonly log: PassLog;
    /** What earlier passes learned (e.g. the emulated runtime model), shared for this run. */
    readonly facts: Facts;
    /**
     * Scope analysis of the program, computed on first use. It is redone after a pass that changed bindings, and
     * refreshed (removed references dropped) after passes that changed only expressions.
     */
    scope(): ScopeInfo;
}

export interface PassResult {
    /** Number of changes made. 0 means the program is untouched. */
    readonly changed: number;
    /**
     * `false` when the changes only replaced expressions in place: no declaration added or removed, no code moved to
     * another scope. The next passes then reuse the scope analysis, refreshed: references that left with the replaced
     * expressions are dropped, and nodes created since are unknown to it (they resolve to nothing). Defaults to true.
     */
    readonly bindingsChanged?: boolean;
    /** Pass-specific counts, e.g. `{ found: 3, unflattened: 2, skipped: 1 }`. */
    readonly stats?: Readonly<Record<string, number>>;
}

export interface Pass {
    readonly name: string;
    readonly description: string;
    run(context: PassContext): PassResult | Promise<PassResult>;
}

/** Passes that feed each other. They run in order, repeatedly, until a full round changes nothing. */
export interface FixpointGroup {
    readonly group: string;
    readonly passes: readonly Pass[];
    /** Safety cap on rounds. Hitting it is logged as a warning. */
    readonly maxRounds: number;
}

export type PipelineStep = Pass | FixpointGroup;

export const isGroup = (step: PipelineStep): step is FixpointGroup => "group" in step;
