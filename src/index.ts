export { deobfuscate } from "./deobfuscate.js";
export type { DeobfuscateOptions, DeobfuscateReport, DeobfuscateResult } from "./deobfuscate.js";
export { ParseError } from "./core/parse.js";
export { UnknownPassError } from "./pipeline/run.js";
export type { PassReport, PassSelection } from "./pipeline/run.js";
export type { FixpointGroup, Pass, PassContext, PassResult, PipelineStep } from "./pipeline/pass.js";
export { PIPELINE } from "./passes/index.js";
export { createLogger, silentLogger } from "./logger.js";
export type { Logger, LogLevel } from "./logger.js";
