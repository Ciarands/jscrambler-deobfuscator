import type { Visitor } from "@babel/traverse";
import type { File } from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

const visitor: Visitor<File> = {};

export const prepareTransformer: Transformer = {
    name: "prepare",
    description: "Initial preparation and setup of the AST",
    priority: TransformerPriority.PREPARE,
    visitor,
};
