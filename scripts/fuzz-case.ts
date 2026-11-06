/** Dev-only: print one fuzz case (structured, flattened, unflattened, traces). `npx tsx scripts/fuzz-case.ts <seed>` */
import { deobfuscate } from "../src/index.js";
import { emit, flatten, generate, mulberry32, runTrace } from "../tests/fuzz/programs.js";

const seed = Number(process.argv[2] ?? 1);
const program = generate(seed);
const structured = emit(program);
const flat = flatten(program, mulberry32(seed));
const { code } = await deobfuscate(`function f() {\n${flat}\n}`, { passes: ["unflatten"] });
console.log("--- structured\n" + structured);
console.log("--- unflattened\n" + code);
const rng = mulberry32(seed * 7919);
const inputs = Array.from({ length: 6 }, () => Array.from({ length: 9 }, () => rng() < 0.5));
for (const bits of inputs) {
    const a = runTrace(structured, bits);
    const b = runTrace(`${code}\nreturn f();`, bits);
    if (a !== b) console.log(`--- differs for ${bits.map(Number).join("")}\nwant ${a}\ngot  ${b}`);
}
