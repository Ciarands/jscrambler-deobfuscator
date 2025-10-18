import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const inlineStringArrayTransformer: Transformer = {
    name: "inlineStringArray",
    description: "Inlines string array references with actual values",
    priority: TransformerPriority.INLINE_STRING_ARRAY,
    visitor,
};
