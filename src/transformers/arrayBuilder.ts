import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const arrayBuilderTransformer: Transformer = {
    name: "arrayBuilder",
    description: "Processes array building operations",
    priority: TransformerPriority.ARRAY_BUILDER,
    visitor,
};
