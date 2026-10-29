import type { PipelineStep } from "../pipeline/pass.js";
import { aliases } from "./aliases.js";
import { argumentsArrays } from "./arguments-arrays.js";
import { calculators } from "./calculators.js";
import { cleanup } from "./cleanup.js";
import { codeLocks } from "./code-locks.js";
import { detectors } from "./detectors.js";
import { emulate } from "./emulate/index.js";
import { globalProxy } from "./global-proxy.js";
import { hashPredicates } from "./hash-predicates.js";
import { normalize } from "./normalize.js";
import { resolveCalls } from "./resolve-calls.js";
import { simplify } from "./simplify.js";
import { storageComparisons } from "./storage-comparisons.js";
import { unflatten } from "./unflatten/index.js";
import { unminify } from "./unminify/index.js";
import { wrappers } from "./wrappers.js";

/**
 * The pipeline, in run order. Each pass documents why it sits where it does. resolve-calls comes right after emulate:
 * decoded strings turn computed storage keys (`G[G.w(147)]`) into static ones, which the storage analysis of the
 * passes after it (what may change `G` after the prelude) needs. code-locks follows wrappers, which turned calls of
 * the locks' wrappers into direct calls; detectors (anti-debug checks, answered with what they say undebugged) comes
 * with it and reads the slot shapes too. calculators comes next, once: it reads calls of a calculator's methods
 * directly and through the wrappers left (`runtime.wrappers`), the removed lock and detector calls no longer stand
 * between a selector call and its calculation, and the simplify group after it folds the case expressions it puts in
 * (`7735 - 7280`). storage-comparisons folds the matrix predicates (`G.k.m[1][10] != G.k.m[3][10]`) once, before the
 * group: their paths are static from the start. The simplify group repeats until nothing changes: folding decides opaque predicates, dead branches
 * leave sequences for normalize to split, and machines whose states became constant are unflattened in the next
 * round; resolve-calls runs again there for calls of settled string decoders whose arguments only now became
 * constant (`G.w(S[7])` once `S[7] = 2572` is known). arguments-arrays then turns `var S = [arguments]` slot arrays
 * into parameters and locals: the passes before it (constants, code-locks, builders, calculators) read the slot
 * shapes, and the cleanup group after it drops the locals whose reads they already resolved. hash-predicates leads both
 * groups: it decides tests on the runtime's pure hash from the locals assigned right before them, so simplify drops
 * the dead branches and loops in the same round; in the cleanup group it sees the predicates whose locals were slots
 * until arguments-arrays. Cleanup comes after, when the runtime has no users left; removing it can make more locals
 * unused, so it repeats too. Unminify is last: it only changes how the code reads, into shapes (`if` for `a && b()`,
 * split declarations) the passes before it don't expect.
 */
export const PIPELINE: readonly PipelineStep[] = [
    normalize,
    unflatten,
    emulate,
    resolveCalls,
    globalProxy,
    aliases,
    wrappers,
    codeLocks,
    detectors,
    calculators,
    storageComparisons,
    { group: "simplify", passes: [hashPredicates, simplify, normalize, unflatten, resolveCalls], maxRounds: 8 },
    argumentsArrays,
    { group: "cleanup", passes: [hashPredicates, cleanup, simplify], maxRounds: 4 },
    unminify,
];
