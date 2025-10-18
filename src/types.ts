import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";

export enum TransformerPriority {
    PREPARE = 0,
    CONTROL_FLOW_UNFLATTENER = 100,
}

export interface Transformer {
    readonly name: string;
    readonly description: string;
    readonly priority: TransformerPriority;
    readonly visitor: Visitor<any>; // extend File later, we'll pass some stuff like logger too so cant use File type rn
}

export interface TransformResult<T> {
    readonly success: boolean;
    readonly data?: T;
    readonly error?: Error;
}

export interface PipelineConfig {
    readonly transformers?: readonly Transformer[];
    readonly minPriority?: TransformerPriority;
    readonly maxPriority?: TransformerPriority;
    readonly enabledTransformers?: readonly string[];
    readonly disabledTransformers?: readonly string[];
}

export interface DeobfuscationResult {
    readonly code: string;
    readonly ast: File;
}

export interface FileProcessingResult {
    readonly success: boolean;
    readonly inputPath: string;
    readonly outputPath: string;
    readonly error?: Error;
}

export interface BatchProcessingResult {
    readonly total: number;
    readonly successful: number;
    readonly failed: number;
    readonly results: readonly FileProcessingResult[];
}

export type LogLevel = "silent" | "error" | "warn" | "info" | "debug";

export interface Logger {
    readonly error: (message: string, ...args: any[]) => void;
    readonly warn: (message: string, ...args: any[]) => void;
    readonly info: (message: string, ...args: any[]) => void;
    readonly debug: (message: string, ...args: any[]) => void;
}
