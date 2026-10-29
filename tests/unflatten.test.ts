import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { emit, flatten, generate, mulberry32, runTrace } from "./fuzz/programs.js";

/**
 * Differential test for the unflattener: random structured program -> jscrambler-style flattening -> our pipeline
 * -> run original and result on the same inputs; traces must match and no machine may be left behind.
 */

const SEEDS = Number(process.env["FUZZ_SEEDS"] ?? 1500);
const SEED_BASE = Number(process.env["FUZZ_SEED"] ?? 1);

const inputsFor = (seed: number): boolean[][] => {
    const rng = mulberry32(seed * 7919);
    return Array.from({ length: 6 }, () => Array.from({ length: 9 }, () => rng() < 0.5));
};

const check = async (seed: number) => {
    const program = generate(seed);
    const structured = emit(program);
    const flat = flatten(program, mulberry32(seed));
    const { code, report } = await deobfuscate(`function f() {\n${flat}\n}`, { passes: ["unflatten"] });
    const body = `${code}\nreturn f();`;
    const inputs = inputsFor(seed);
    const expected = inputs.map((bits) => runTrace(structured, bits));
    const flatTraces = inputs.map((bits) => runTrace(flat, bits));
    const got = inputs.map((bits) => runTrace(body, bits));
    const stats = report.passes[0]?.stats ?? {};
    return { seed, structured, flat, code, expected, flatTraces, got, left: stats["skipped"] ?? 0 };
};

describe("unflatten (differential fuzz)", () => {
    it("the reference flattener preserves behaviour", async () => {
        for (let seed = SEED_BASE; seed < SEED_BASE + 200; seed++) {
            const r = await check(seed);
            expect(r.flatTraces, `seed ${seed}\n${r.structured}\n--- flattened\n${r.flat}`).toEqual(r.expected);
        }
    }, 60_000);

    it(`rebuilds ${SEEDS} random flattened programs with identical behaviour`, async () => {
        const failures: string[] = [];
        for (let seed = SEED_BASE; seed < SEED_BASE + SEEDS; seed++) {
            const r = await check(seed);
            if (r.left > 0) failures.push(`seed ${seed}: ${r.left} machine(s) left flattened\n--- flattened\n${r.flat}\n--- unflattened\n${r.code}`);
            else if (JSON.stringify(r.got) !== JSON.stringify(r.expected)) failures.push(`seed ${seed}: behaviour changed\n--- structured\n${r.structured}\n--- unflattened\n${r.code}`);
            if (failures.length >= 3) break;
        }
        expect(failures, failures.join("\n\n")).toEqual([]);
    }, 120_000);
});
