import { printSync } from "oxc-codegen";
import type { Program } from "oxc-parser";

/** Print an ESTree program. Two-space indent; comments are not printed. */
export const print = (program: Program): string => printSync(program, { indent: "  " }).code;
