import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const stateMachineSolverTransformer: Transformer = {
    name: "stateMachineSolver",
    description: "Solves state machine obfuscation patterns",
    priority: TransformerPriority.STATE_MACHINE_SOLVER,
    visitor,
};
