import fs from "fs";
import os from "os";
import path from "path";
import { processFile } from "../src/io.js";
import { buildPipeline } from "../src/pipeline.js";
import { ALL_TRANSFORMERS } from "../src/transformers/index.js";
import { silentLogger } from "../src/logger.js";

describe("processFile", () => {
    let tmpDir: string;
    let inputFile: string;
    let outputFile: string;
    const pipeline = buildPipeline(ALL_TRANSFORMERS);

    beforeEach(() => {
        tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "jscrambler-deobf-ps-"));
        inputFile = path.join(tmpDir, "input.js");
        outputFile = path.join(tmpDir, "output.js");
        fs.writeFileSync(inputFile, "var a = 1; function f(){ return a + 1 } f();\n", "utf-8");
    });

    afterEach(() => {
        if (fs.existsSync(tmpDir)) {
            fs.rmSync(tmpDir, { recursive: true, force: true });
        }
    });

    it("generates output without throwing and writes file", () => {
        const result = processFile(inputFile, outputFile, pipeline, silentLogger);
        expect(result.success).toBe(true);
        expect(fs.existsSync(outputFile)).toBe(true);
        const size = fs.statSync(outputFile).size;
        expect(size).toBeGreaterThan(0);
    });
});
