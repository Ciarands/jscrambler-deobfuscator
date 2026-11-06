import { parseSync } from "oxc-parser";
import type { OxcError, Program } from "oxc-parser";
import { SourceMap } from "./log.js";

export class ParseError extends Error {
    /** Codeframes repeat the whole source line, which can be huge in minified input. */
    readonly codeframes: readonly string[];

    constructor(message: string, codeframes: readonly string[]) {
        super(message);
        this.name = "ParseError";
        this.codeframes = codeframes;
    }
}

const describe = (source: SourceMap, error: OxcError): string => {
    const start = error.labels[0]?.start;
    return start === undefined ? error.message : `${error.message} (${source.location(start)})`;
};

/** `range` is always on (scope analysis needs it). Parenthesized expressions are not kept as nodes. */
export const parse = (code: string, filename = "input.js"): Program => {
    const result = parseSync(filename, code, {
        lang: "js",
        sourceType: "unambiguous",
        range: true,
        preserveParens: false,
    });
    if (result.errors.length > 0) {
        const source = new SourceMap(code);
        const details = result.errors.map((error) => describe(source, error)).join("; ");
        throw new ParseError(
            `Failed to parse ${filename}: ${details}`,
            result.errors.map((error) => error.codeframe ?? error.message)
        );
    }
    return result.program;
};
