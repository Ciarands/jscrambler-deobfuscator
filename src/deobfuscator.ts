import * as babel from "@babel/core";
import traverseModule from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer, DeobfuscationResult, TransformResult, Logger } from "./types.js";
import { defaultLogger } from "./logger.js";

const traverse = typeof traverseModule === "function" ? traverseModule : (traverseModule as any).default;

export const parseCode = (code: string): TransformResult<File> => {
    try {
        const ast = babel.parseSync(code, { sourceType: "script" });
        if (!ast) {
            return {
                success: false,
                error: new Error("Failed to parse code into AST"),
            };
        }
        return { success: true, data: ast };
    } catch (error) {
        return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
        };
    }
};

export const generateCode = (ast: File): TransformResult<string> => {
    try {
        const result = babel.transformFromAstSync(ast, undefined, {
            sourceType: "script",
            code: true,
        });

        if (!result || !result.code) {
            return {
                success: false,
                error: new Error("Failed to generate code from AST"),
            };
        }

        return { success: true, data: result.code };
    } catch (error) {
        return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
        };
    }
};

export const applyTransformer = (ast: File, transformer: Transformer, logger: Logger = defaultLogger): TransformResult<File> => {
    try {
        logger.debug(`Applying transformer: ${transformer.name} (priority: ${transformer.priority})`);
        if (transformer.description) {
            logger.debug(`  ${transformer.description}`);
        }
        traverse(ast, transformer.visitor, undefined, { logger });
        return { success: true, data: ast };
    } catch (error) {
        return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
        };
    }
};

export const applyTransformers = (ast: File, transformers: readonly Transformer[], logger: Logger = defaultLogger): TransformResult<File> => {
    logger.info(`Applying ${transformers.length} transformer(s)`);

    for (const transformer of transformers) {
        const result = applyTransformer(ast, transformer, logger);
        if (!result.success) {
            logger.error(`Failed to apply transformer ${transformer.name}:`, result.error);
            return result;
        }
    }

    return { success: true, data: ast };
};

export const deobfuscate = (code: string, transformers: readonly Transformer[], logger: Logger = defaultLogger): TransformResult<DeobfuscationResult> => {
    const parseResult = parseCode(code);
    if (!parseResult.success || !parseResult.data) {
        logger.error("Failed to parse code:", parseResult.error);
        return { success: false, error: parseResult.error };
    }

    const ast = parseResult.data;

    const transformResult = applyTransformers(ast, transformers, logger);
    if (!transformResult.success) {
        return { success: false, error: transformResult.error };
    }

    const generateResult = generateCode(ast);
    if (!generateResult.success || !generateResult.data) {
        logger.error("Failed to generate code:", generateResult.error);
        return { success: false, error: generateResult.error };
    }

    return {
        success: true,
        data: {
            code: generateResult.data,
            ast,
        },
    };
};
