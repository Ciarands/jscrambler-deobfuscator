import { Command } from "commander";
import fs from "fs";
import path from "path";
import { createLogger } from "./logger.js";
import { buildPipeline } from "./pipeline.js";
import { ALL_TRANSFORMERS } from "./transformers/index.js";
import { processFile, processDirectory, isDirectory } from "./io.js";
import type { LogLevel } from "./types.js";

const program = new Command();

program
    .name("jscrambler-deobfuscator")
    .description("Deobfuscate JavaScript files obfuscated with Jscrambler")
    .version("1.0.0")
    .argument("<input>", "Input file or directory to process")
    .option("-o, --output <path>", "Output file or directory path")
    .option("-e, --extensions <extensions>", "File extensions to process (comma-separated)", ".js")
    .option("-v, --verbose", "Enable verbose output")
    .option("-s, --silent", "Suppress all output except errors")
    .option("--debug", "Enable debug logging")
    .action(async (input: string, options: { output?: string; extensions: string; verbose?: boolean; silent?: boolean; debug?: boolean }) => {
        try {
            const logLevel: LogLevel = options.debug ? "debug" : options.silent ? "silent" : options.verbose ? "info" : "info";
            const logger = createLogger(logLevel);
            const inputPath = path.resolve(input);
            if (!fs.existsSync(inputPath)) {
                logger.error(`Error: Input path does not exist: ${inputPath}`);
                process.exit(1);
            }

            const extensions = options.extensions
                .split(",")
                .map((ext) => ext.trim())
                .filter((ext) => ext.length > 0);

            const pipeline = buildPipeline(ALL_TRANSFORMERS);
            logger.debug(`Built pipeline with ${pipeline.length} transformer(s)`);

            const isDir = isDirectory(inputPath);
            const outputPath = options.output
                ? path.resolve(options.output)
                : isDir
                  ? path.join(path.dirname(inputPath), "output")
                  : (() => {
                        const ext = path.extname(inputPath);
                        const base = path.basename(inputPath, ext);
                        const dir = path.dirname(inputPath);
                        return path.join(dir, `${base}.deobfuscated${ext}`);
                    })();

            logger.info(`--------------------------------------`);
            logger.info(`JSCrambler Deobfuscator`);
            logger.info(`--------------------------------------`);
            logger.info(`Input:  ${inputPath}`);
            logger.info(`Output: ${outputPath}`);
            if (isDir) {
                logger.info(`Extensions: ${extensions.join(", ")}`);
            }
            logger.info(`--------------------------------------`);

            if (isDir) {
                const result = processDirectory(inputPath, outputPath, extensions, pipeline, logger);
                if (result.failed > 0) {
                    process.exit(1);
                }
            } else {
                const result = processFile(inputPath, outputPath, pipeline, logger);
                if (!result.success) {
                    logger.error(`Failed to process file`);
                    process.exit(1);
                }
            }
        } catch (error) {
            console.error("Fatal error:", error);
            process.exit(1);
        }
    });

process.on("unhandledRejection", (reason) => {
    console.error("Unhandled rejection:", reason);
    process.exit(1);
});

program.parse();
