import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const inlineWrapperFunctionsTransformer: Transformer = {
    name: "inlineWrapperFunctions",
    description: "Inlines wrapper function calls",
    priority: TransformerPriority.INLINE_WRAPPER_FUNCTIONS,
    visitor,
};
