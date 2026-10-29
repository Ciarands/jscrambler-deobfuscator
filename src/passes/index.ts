import type { PipelineStep } from "../pipeline/pass.js";

/** The pipeline, in run order: passes and fixpoint groups of passes. */
export const PIPELINE: readonly PipelineStep[] = [];
