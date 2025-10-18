import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const setupFunctionsTransformer: Transformer = {
    name: "setupFunctions",
    description: "Identifies and processes setup functions",
    priority: TransformerPriority.SETUP_FUNCTIONS,
    visitor,
};
