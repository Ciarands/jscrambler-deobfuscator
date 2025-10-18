import type { Transformer, PipelineConfig, TransformerPriority } from "./types.js";

export const sortByPriority = (transformers: readonly Transformer[]): readonly Transformer[] => [...transformers].sort((a, b) => a.priority - b.priority);

export const filterByPriorityRange = (transformers: readonly Transformer[], minPriority: TransformerPriority, maxPriority: TransformerPriority): readonly Transformer[] =>
    transformers.filter((t) => t.priority >= minPriority && t.priority <= maxPriority);

export const filterByNames = (transformers: readonly Transformer[], names: readonly string[]): readonly Transformer[] => transformers.filter((t) => names.includes(t.name));

export const excludeByNames = (transformers: readonly Transformer[], names: readonly string[]): readonly Transformer[] => transformers.filter((t) => !names.includes(t.name));

export const buildPipeline = (allTransformers: readonly Transformer[], config: PipelineConfig = {}): readonly Transformer[] => {
    let pipeline = config.transformers ?? allTransformers;

    if (config.minPriority !== undefined || config.maxPriority !== undefined) {
        const min = config.minPriority ?? Math.min(...pipeline.map((t) => t.priority));
        const max = config.maxPriority ?? Math.max(...pipeline.map((t) => t.priority));
        pipeline = filterByPriorityRange(pipeline, min, max);
    }

    if (config.enabledTransformers) {
        pipeline = filterByNames(pipeline, config.enabledTransformers);
    }

    if (config.disabledTransformers) {
        pipeline = excludeByNames(pipeline, config.disabledTransformers);
    }

    return sortByPriority(pipeline);
};

export const getTransformerNames = (pipeline: readonly Transformer[]): readonly string[] => pipeline.map((t) => t.name);
