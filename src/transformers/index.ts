import type { Transformer } from "../types.js";
import { prepareTransformer } from "./prepare.js";
import { setupFunctionsTransformer } from "./setupFunctions.js";
import { stringArraySolverTransformer } from "./stringArraySolver.js";
import { stateMachineSolverTransformer } from "./stateMachineSolver.js";
import { arrayBuilderTransformer } from "./arrayBuilder.js";
import { inlineStringArrayTransformer } from "./inlineStringArray.js";
import { inlineWrapperFunctionsTransformer } from "./inlineWrapperFunctions.js";
import { inlineSetupFunctionsTransformer } from "./inlineSetupFunctions.js";
import { controlFlowUnflattenerTransformer } from "./controlFlowUnflattener.js";
import { finalTransformer } from "./final.js";

export const ALL_TRANSFORMERS: readonly Transformer[] = Object.freeze([
    prepareTransformer,
    setupFunctionsTransformer,
    stringArraySolverTransformer,
    stateMachineSolverTransformer,
    arrayBuilderTransformer,
    inlineStringArrayTransformer,
    inlineWrapperFunctionsTransformer,
    inlineSetupFunctionsTransformer,
    controlFlowUnflattenerTransformer,
    finalTransformer,
]);

export const getTransformerByName = (name: string): Transformer | undefined => ALL_TRANSFORMERS.find((t) => t.name === name);
export const getAllTransformerNames = (): readonly string[] => ALL_TRANSFORMERS.map((t) => t.name);
