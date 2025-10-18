import fs from "fs";
import path from "path";
import type { Transformer, FileProcessingResult, BatchProcessingResult, TransformResult, Logger } from "./types.js";
import { deobfuscate } from "./deobfuscator.js";
import { defaultLogger } from "./logger.js";

export const isDirectory = (filepath: string): boolean => {
    try {
        return fs.statSync(filepath).isDirectory();
    } catch {
        return false;
    }
};

export const readFile = (filepath: string): TransformResult<string> => {
    try {
        const content = fs.readFileSync(filepath, "utf-8");
        return { success: true, data: content };
    } catch (error) {
        return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
        };
    }
};

export const writeFile = (filepath: string, content: string): TransformResult<void> => {
    try {
        const dir = path.dirname(filepath);
        if (!fs.existsSync(dir)) {
            fs.mkdirSync(dir, { recursive: true });
        }
        fs.writeFileSync(filepath, content, "utf-8");
        return { success: true };
    } catch (error) {
        return {
            success: false,
            error: error instanceof Error ? error : new Error(String(error)),
        };
    }
};

export const getFiles = (directory: string, extensions: readonly string[]): readonly string[] => {
    try {
        return fs
            .readdirSync(directory)
            .filter((file) => extensions.some((ext) => file.endsWith(ext)))
            .map((file) => path.join(directory, file));
    } catch {
        return [];
    }
};

export const processFile = (inputPath: string, outputPath: string, transformers: readonly Transformer[], logger: Logger = defaultLogger): FileProcessingResult => {
    const basename = path.basename(inputPath);
    logger.info(`\nProcessing: ${basename}`);

    const readResult = readFile(inputPath);
    if (!readResult.success || !readResult.data) {
        logger.error(`Failed to read ${basename}:`, readResult.error);
        return {
            success: false,
            inputPath,
            outputPath,
            error: readResult.error,
        };
    }

    const deobfResult = deobfuscate(readResult.data, transformers, logger);
    if (!deobfResult.success || !deobfResult.data) {
        logger.error(`Failed to deobfuscate ${basename}:`, deobfResult.error);
        return {
            success: false,
            inputPath,
            outputPath,
            error: deobfResult.error,
        };
    }

    const writeResult = writeFile(outputPath, deobfResult.data.code);
    if (!writeResult.success) {
        logger.error(`Failed to write ${basename}:`, writeResult.error);
        return {
            success: false,
            inputPath,
            outputPath,
            error: writeResult.error,
        };
    }

    logger.info(`Completed: ${basename} -> ${path.basename(outputPath)}`);
    return {
        success: true,
        inputPath,
        outputPath,
    };
};

export const processDirectory = (inputDir: string, outputDir: string, extensions: readonly string[], transformers: readonly Transformer[], logger: Logger = defaultLogger): BatchProcessingResult => {
    const files = getFiles(inputDir, extensions);

    if (files.length === 0) {
        logger.info(`No files found in ${inputDir} matching extensions: ${extensions.join(", ")}`);
        return {
            total: 0,
            successful: 0,
            failed: 0,
            results: [],
        };
    }

    logger.info(`Found ${files.length} file(s) to process`);

    const results = files.map((inputFile) => {
        const outputFile = path.join(outputDir, path.basename(inputFile));
        return processFile(inputFile, outputFile, transformers, logger);
    });

    const successful = results.filter((r) => r.success).length;
    const failed = results.filter((r) => !r.success).length;

    logger.info(`\n--------------------------------------`);
    logger.info(`Batch processing complete:`);
    logger.info(`  Total: ${results.length}`);
    logger.info(`  Successful: ${successful}`);
    logger.info(`  Failed: ${failed}`);
    logger.info(`--------------------------------------`);

    if (failed > 0) {
        logger.info(`\nFailed files:`);
        results
            .filter((r) => !r.success)
            .forEach((r) => {
                logger.error(`  - ${path.basename(r.inputPath)}: ${r.error?.message}`);
            });
    }

    return {
        total: results.length,
        successful,
        failed,
        results,
    };
};
