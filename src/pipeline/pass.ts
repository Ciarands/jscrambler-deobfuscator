import type { Program } from "oxc-parser";
import type { Logger } from "../logger.js";

export interface PassContext {
    readonly program: Program;
    readonly logger: Logger;
}

export interface PassResult {
    /** Number of changes made. 0 means the program is untouched. */
    readonly changed: number;
    /** Pass-specific counts, e.g. `{ found: 3, unflattened: 2, skipped: 1 }`. */
    readonly stats?: Readonly<Record<string, number>>;
}

export interface Pass {
    readonly name: string;
    readonly description: string;
    run(context: PassContext): PassResult;
}
