import type { PipelineStep } from "../pipeline/pass.js";
import { aliases } from "./aliases.js";
import { argumentsArrays } from "./arguments-arrays.js";
import { calculators, calculatorsBound } from "./calculators/index.js";
import { cleanup } from "./cleanup.js";
import { codeLocks } from "./code-locks.js";
import { detectors } from "./detectors.js";
import { domainLocks } from "./domain-locks.js";
import { globalProxy } from "./global-proxy.js";
import { hashPredicates } from "./hash-predicates.js";
import { normalize } from "./normalize.js";
import { pureCalls } from "./pure-calls.js";
import { resolveCalls } from "./resolve-calls.js";
import { simplify } from "./simplify.js";
import { runtime } from "./runtime/index.js";
import { storageComparisons } from "./storage-comparisons.js";
import { unflatten } from "./unflatten/index.js";
import { unminify } from "./unminify/index.js";
import { wrappers } from "./wrappers.js";

/**
 * The pipeline, in run order; each pass documents why it sits where it does. Ordering constraints:
 * - resolve-calls right after runtime: decoded strings make computed storage keys static for later storage analyses.
 * - code-locks, detectors and domain-locks after wrappers, which turned lock wrapper calls into direct calls.
 * - calculators next: removed lock and detector calls no longer stand between a selector call and its calculation.
 * - storage-comparisons once before the simplify group: its paths are static from the start.
 * - The simplify group repeats to a fixpoint; resolve-calls and pure-calls rerun there as arguments become constant.
 * - arguments-arrays leads the cleanup group (earlier passes read the slot shapes); resolve-calls, code-locks,
 *   domain-locks and calculators-bound rerun after it on the plain locals, calculators-bound after the locks for the
 *   reason above; hash-predicates follows in both groups. Only calculators-bound binds arguments: before it, a slot
 *   argument may still become a local that goes in directly.
 * - Unminify last: it produces shapes the earlier passes don't expect.
 */
export const PIPELINE: readonly PipelineStep[] = [
    normalize,
    unflatten,
    runtime,
    resolveCalls,
    globalProxy,
    aliases,
    wrappers,
    codeLocks,
    detectors,
    domainLocks,
    calculators,
    storageComparisons,
    { group: "simplify", passes: [hashPredicates, simplify, normalize, unflatten, resolveCalls, pureCalls], maxRounds: 8 },
    { group: "cleanup", passes: [argumentsArrays, resolveCalls, codeLocks, domainLocks, calculatorsBound, hashPredicates, cleanup, simplify], maxRounds: 4 },
    unminify,
];
