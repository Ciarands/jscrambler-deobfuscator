import { parseSync } from "oxc-parser";
import type { OxcError, Program } from "oxc-parser";

export class ParseError extends Error {
    /** Formatted code frames, one per parser error. These repeat the whole source line, which can be huge in minified input. */
    readonly codeframes: readonly string[];

    constructor(message: string, codeframes: readonly string[]) {
        super(message);
        this.name = "ParseError";
        this.codeframes = codeframes;
    }
}

const location = (code: string, offset: number): string => {
    let line = 1;
    let lineStart = 0;
    for (let i = code.indexOf("\n"); i !== -1 && i < offset; i = code.indexOf("\n", i + 1)) {
        line += 1;
        lineStart = i + 1;
    }
    return `${line}:${offset - lineStart + 1}`;
};

const describe = (code: string, error: OxcError): string => {
    const start = error.labels[0]?.start;
    return start === undefined ? error.message : `${error.message} (${location(code, start)})`;
};

/**
 * Parse source into an ESTree program.
 *
 * `range` is always on: scope analysis needs it, and every node a pass creates must copy it.
 * Parenthesized expressions are not kept as separate nodes.
 */
export const parse = (code: string, filename = "input.js"): Program => {
    const result = parseSync(filename, code, {
        lang: "js",
        sourceType: "unambiguous",
        range: true,
        preserveParens: false,
    });
    if (result.errors.length > 0) {
        const details = result.errors.map((error) => describe(code, error)).join("; ");
        throw new ParseError(
            `Failed to parse ${filename}: ${details}`,
            result.errors.map((error) => error.codeframe ?? error.message),
        );
    }
    return result.program;
};
