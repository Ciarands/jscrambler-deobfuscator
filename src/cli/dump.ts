import { mkdirSync, writeFileSync } from "node:fs";
import path from "node:path";
import type { PassReport } from "../pipeline/run.js";

/** Pipeline hooks writing `00-input.js` and one file per pass run into `dir`, numbered in run order. */
export const dumpHooks = (dir: string) => {
    let count = 0;
    const write = (label: string, code: string) => {
        mkdirSync(dir, { recursive: true });
        writeFileSync(path.join(dir, `${String(count++).padStart(2, "0")}-${label}.js`), code);
    };
    return {
        beforePasses: (code: string) => write("input", code),
        afterPass: (report: PassReport, code: string) => write(report.round === undefined ? report.name : `${report.name}-r${report.round}`, code),
    };
};
