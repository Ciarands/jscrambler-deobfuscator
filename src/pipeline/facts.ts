import type { Node } from "../core/ast.js";

/** What one pass learned and later passes need, for one run. */
export interface FactKey<T> {
    readonly name: string;
    /** Never set; only carries the type. */
    readonly type?: T;
}

export const factKey = <T>(name: string): FactKey<T> => ({ name });

/** `replacements` together do exactly what `originals` did. */
export type ReplacementListener = (originals: readonly Node[], replacements: readonly Node[]) => void;

export class Facts {
    readonly #values = new Map<string, unknown>();
    readonly #replacementListeners: ReplacementListener[] = [];

    get<T>(key: FactKey<T>): T | undefined {
        return this.#values.get(key.name) as T | undefined; // only `set` with the same key writes this name
    }

    set<T>(key: FactKey<T>, value: T): void {
        this.#values.set(key.name, value);
    }

    /**
     * Report statements replaced by equivalent ones so facts keyed by statement can follow them; each owner decides
     * what carries over. Removed statements aren't reported: their facts just stop applying.
     */
    replaced(originals: readonly Node[], replacements: readonly Node[]): void {
        for (const listener of this.#replacementListeners) listener(originals, replacements);
    }

    onReplace(listener: ReplacementListener): void {
        this.#replacementListeners.push(listener);
    }
}
