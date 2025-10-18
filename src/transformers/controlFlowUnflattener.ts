import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const controlFlowUnflattenerTransformer: Transformer = {
    name: "controlFlowUnflattener",
    description: "Unflattens control flow obfuscation",
    priority: TransformerPriority.CONTROL_FLOW_UNFLATTENER,
    visitor,
};
