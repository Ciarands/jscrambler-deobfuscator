import path from "node:path";
import type { PassReport } from "../pipeline/run.js";
import { writeOutput } from "./write.js";

/** Writes `00-input.js` and one file per pass run into `dir`, numbered in run order; existing files only with `force`. */
export const dumpHooks = (dir: string, force: boolean) => {
    let count = 0;
    const write = (label: string, code: string) => {
        const file = path.join(dir, `${String(count++).padStart(2, "0")}-${label}.js`);
        writeOutput(file, code, force, file);
    };
    return {
        beforePasses: (code: string) => write("input", code),
        afterPass: (report: PassReport, code: string) => write(report.round === undefined ? report.name : `${report.name}-r${report.round}`, code),
    };
};
