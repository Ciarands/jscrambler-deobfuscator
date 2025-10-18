import fs from "fs";
import os from "os";
import path from "path";
import { processDirectory } from "../src/io.js";
import { buildPipeline } from "../src/pipeline.js";
import { ALL_TRANSFORMERS } from "../src/transformers/index.js";
import { silentLogger } from "../src/logger.js";

describe("processDirectory", () => {
    let tmpDir: string;
    let outDir: string;
    const pipeline = buildPipeline(ALL_TRANSFORMERS);

    beforeEach(() => {
        tmpDir = fs.mkdtempSync(path.join(os.tmpdir(), "jscrambler-deobf-pd-"));
        outDir = path.join(tmpDir, "out");
        fs.mkdirSync(outDir, { recursive: true });
        fs.writeFileSync(path.join(tmpDir, "a.js"), "var x = 1; x + 2;\n", "utf-8");
        fs.writeFileSync(path.join(tmpDir, "b.js"), "function g(){ return 3 } g();\n", "utf-8");
        fs.writeFileSync(path.join(tmpDir, "c.txt"), "ignore\n", "utf-8");
    });

    afterEach(() => {
        if (fs.existsSync(tmpDir)) {
            fs.rmSync(tmpDir, { recursive: true, force: true });
        }
    });

    it("processes only .js files and writes outputs", () => {
        const result = processDirectory(tmpDir, outDir, [".js"], pipeline, silentLogger);
        expect(result.total).toBe(2);
        expect(result.failed).toBe(0);
        expect(result.successful).toBe(2);

        const outFiles = fs.readdirSync(outDir).filter((f) => f.endsWith(".js"));
        expect(outFiles.sort()).toEqual(["a.js", "b.js"].sort());
        outFiles.forEach((f) => {
            const p = path.join(outDir, f);
            expect(fs.existsSync(p)).toBe(true);
            expect(fs.statSync(p).size).toBeGreaterThan(0);
        });
    });
});
