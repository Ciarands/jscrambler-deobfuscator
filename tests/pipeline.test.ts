import { describe, expect, it } from "vitest";
import { SourceMap } from "../src/core/log.js";
import { parse } from "../src/core/parse.js";
import { silentLogger } from "../src/logger.js";
import type { Pass, PassResult } from "../src/pipeline/pass.js";
import { runPipeline } from "../src/pipeline/run.js";

/** Changes the program on its first run only. */
const changesOnce = (name: string, settled: boolean): Pass => {
    let runs = 0;
    return { name, description: name, run: (): PassResult => (runs++ === 0 ? { changed: 1, bindingsChanged: false, settled } : { changed: 0 }) };
};

const idle: Pass = { name: "idle", description: "idle", run: () => ({ changed: 0 }) };

const passRuns = async (first: Pass): Promise<string[]> => {
    const source = "x;";
    const reports = await runPipeline(parse(source), [{ group: "g", passes: [first, idle], maxRounds: 4 }], { logger: silentLogger, source: new SourceMap(source) });
    return reports.map((report) => `${report.name} ${report.round}`);
};

describe("fixpoint groups", () => {
    it("rerun a pass that changed something, after the others", async () => {
        expect(await passRuns(changesOnce("once", false))).toEqual(["once 1", "idle 1", "once 2"]);
    });

    it("don't rerun a settled pass while nothing else changes", async () => {
        expect(await passRuns(changesOnce("once", true))).toEqual(["once 1", "idle 1"]);
    });
});
