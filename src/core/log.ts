import type { Logger } from "../logger.js";
import type { Node } from "./ast.js";

export class SourceMap {
    readonly #source: string;
    readonly #lineStarts: number[] = [0];

    constructor(source: string) {
        this.#source = source;
        for (let i = source.indexOf("\n"); i !== -1; i = source.indexOf("\n", i + 1)) this.#lineStarts.push(i + 1);
    }

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

    snippet(node: Node, max = 80): string {
        const [start, end] = node.range ?? [node.start, node.end];
        const text = this.#source.slice(start, Math.min(end, start + max * 4)).replace(/\s+/g, " ");
        return text.length > max ? `${text.slice(0, max - 3)}...` : text;
    }
}

export interface PassLog {
    info(message: string, node?: Node): void;
    debug(message: string, node?: Node): void;
    warn(message: string, node?: Node): void;
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
