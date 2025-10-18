import type { Transformer } from "../types.js";
import { prepareTransformer } from "./prepare.js";
import { controlFlowUnflattener } from "./controlFlowUnflattener.js";

export const ALL_TRANSFORMERS: readonly Transformer[] = Object.freeze([prepareTransformer, controlFlowUnflattener]);

export const getTransformerByName = (name: string): Transformer | undefined => ALL_TRANSFORMERS.find((t) => t.name === name);
export const getAllTransformerNames = (): readonly string[] => ALL_TRANSFORMERS.map((t) => t.name);
