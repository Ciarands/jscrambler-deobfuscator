export { deobfuscate, parseCode, generateCode, applyTransformer, applyTransformers } from "./deobfuscator.js";

export { buildPipeline, sortByPriority, filterByPriorityRange, filterByNames, excludeByNames, getTransformerNames } from "./pipeline.js";

export { processFile, processDirectory, readFile, writeFile, isDirectory, getFiles } from "./io.js";

export { createLogger, silentLogger, defaultLogger } from "./logger.js";

export { ALL_TRANSFORMERS, getTransformerByName, getAllTransformerNames } from "./transformers/index.js";

export type { Transformer, TransformResult, PipelineConfig, DeobfuscationResult, FileProcessingResult, BatchProcessingResult, Logger, LogLevel } from "./types.js";

export { TransformerPriority } from "./types.js";
