import { createContext, runInContext } from "node:vm";
import type { Node } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";

export interface Run {
    /** Host values the program sees as globals, made afresh for each run so no run sees what another left. */
    readonly globals?: () => Record<string, unknown>;
    /** Code run first in the program's own realm, for stand-ins that must be guest objects. */
    readonly prelude?: string;
    /** `window` is the global object, as in a page. */
    readonly window?: boolean;
    /** `setTimeout` queues its callback; the queue runs in order after the script, as a page's event loop runs it. */
    readonly timers?: boolean;
    /** A global `t` returns what it is passed and records it; the records come before the report. */
    readonly trace?: boolean;
    /** Bound on the script, in milliseconds. */
    readonly timeout?: number;
    /** What the run shows, read from the global object once everything ran; its `result` by default. */
    readonly report?: (global: Record<string, unknown>) => unknown;
}

const tag = (value: object): string => Object.prototype.toString.call(value).slice(8, -1);

const isError = (value: unknown): value is { name: unknown; message: unknown } => typeof value === "object" && value !== null && tag(value) === "Error";

/** JSON that also tells apart what JSON merges: `undefined`, `NaN`, the infinities, `-0`, bigints, functions, symbols, maps, sets, regexps and errors. */
export const serialize = (value: unknown): string =>
    JSON.stringify(value, (_, v: unknown) => {
        if (v === undefined) return "<undefined>";
        if (typeof v === "number") return Number.isFinite(v) && !Object.is(v, -0) ? v : `<${Object.is(v, -0) ? "-0" : String(v)}>`;
        if (typeof v === "bigint") return `<${v}n>`;
        if (typeof v === "symbol") return `<${String(v)}>`;
        if (typeof v === "function") return `<function ${v.name}>`;
        if (typeof v !== "object" || v === null) return v;
        if (isError(v)) return `<${String(v.name)}: ${String(v.message)}>`;
        // Tags, not `instanceof`: the values come from another realm.
        const kind = tag(v);
        if (kind === "RegExp") return `<${String(v)}>`;
        return kind === "Map" || kind === "Set" ? { [`<${kind}>`]: Array.from(v as Iterable<unknown>) } : v;
    }) as string;

const thrown = (error: unknown): string => `threw ${isError(error) ? `${String(error.name)}: ${String(error.message)}` : serialize(error)}`;

/**
 * Runs a self-written test program in a fresh node:vm realm and returns what it observably did: the report (the global
 * `result` by default), then `threw <error>` for every uncaught throw, in order. Timer callbacks still run after the
 * script threw, and one that throws doesn't stop the others, as in a page.
 */
export const observe = (source: string, run: Run = {}): string => {
    const queue: (() => void)[] = [];
    const trace: unknown[] = [];
    const global = createContext({
        ...run.globals?.(),
        ...(run.timers === true && { setTimeout: (callback: () => void) => queue.push(callback) }),
        ...(run.trace === true && { t: (value: unknown) => (trace.push(value), value) }),
    });
    if (run.window === true) global["window"] = runInContext("this", global);
    if (run.prelude !== undefined) runInContext(run.prelude, global);
    const errors: unknown[] = [];
    try {
        runInContext(source, global, run.timeout === undefined ? {} : { timeout: run.timeout });
    } catch (error) {
        errors.push(error);
    }
    for (const callback of queue) {
        try {
            callback();
        } catch (error) {
            errors.push(error);
        }
    }
    const report = run.report === undefined ? global["result"] : run.report(global);
    return [serialize(run.trace === true ? [trace, report] : report), ...errors.map(thrown)].join("; ");
};

const LOOPS: Readonly<Record<string, true>> = { ForStatement: true, ForInStatement: true, ForOfStatement: true, WhileStatement: true, DoWhileStatement: true };

/** Control-flow machines in the code: loops whose body is, or holds directly, a `switch`. */
export const machinesLeft = (code: string): number => {
    let count = 0;
    traverse(parse(code), {
        SwitchStatement: (path) => {
            const holder: Node | null = path.parent?.type === "BlockStatement" ? (path.parentPath?.parent ?? null) : path.parent;
            if (holder !== null && LOOPS[holder.type] === true) count++;
        },
    });
    return count;
};
