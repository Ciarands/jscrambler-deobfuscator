import type { Logger } from "../logger.js";
import type { Node } from "./ast.js";

/** Turns offsets in the original source into `line:column` and short code snippets for log lines. */
export class SourceMap {
    readonly #source: string;
    readonly #lineStarts: number[] = [0];

    constructor(source: string) {
        this.#source = source;
        for (let i = source.indexOf("\n"); i !== -1; i = source.indexOf("\n", i + 1)) this.#lineStarts.push(i + 1);
    }

    /** `line:column` (1-based) of an offset in the original source. */
    location(offset: number): string {
        let low = 0;
        let high = this.#lineStarts.length - 1;
        while (low < high) {
            const mid = (low + high + 1) >> 1;
            if ((this.#lineStarts[mid] ?? 0) <= offset) low = mid;
            else high = mid - 1;
        }
        return `${low + 1}:${offset - (this.#lineStarts[low] ?? 0) + 1}`;
    }

    /** Original source of a node on one line, cut to `max` characters. */
    snippet(node: Node, max = 80): string {
        const [start, end] = node.range ?? [node.start, node.end];
        const text = this.#source.slice(start, Math.min(end, start + max * 4)).replace(/\s+/g, " ");
        return text.length > max ? `${text.slice(0, max - 3)}...` : text;
    }
}

/**
 * Logging for one pass. Every line is prefixed with the pass name; passing a node appends where it was in the
 * original input and what it looked like, so a log line can be traced back to the obfuscated source.
 */
export interface PassLog {
    info(message: string, node?: Node): void;
    debug(message: string, node?: Node): void;
    warn(message: string, node?: Node): void;
    /** Whether debug lines are written: check it before building a costly debug message. */
    readonly debugging: boolean;
}

const ignore = (): void => {};

export const createPassLog = (pass: string, logger: Logger, source: SourceMap): PassLog => {
    const format = (message: string, node?: Node): string =>
        node === undefined ? `[${pass}] ${message}` : `[${pass}] ${message} @ ${source.location(node.range?.[0] ?? node.start)} \`${source.snippet(node)}\``;
    // A line at a level nobody writes isn't formatted (the location lookup and the snippet are what cost).
    const enabled = (level: "info" | "debug" | "warn"): boolean => logger.enabled?.(level) ?? true;
    const debugging = enabled("debug");
    return {
        info: enabled("info") ? (message, node) => logger.info(format(message, node)) : ignore,
        debug: debugging ? (message, node) => logger.debug(format(message, node)) : ignore,
        warn: enabled("warn") ? (message, node) => logger.warn(format(message, node)) : ignore,
        debugging,
    };
};
