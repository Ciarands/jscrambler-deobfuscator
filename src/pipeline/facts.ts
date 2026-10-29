import type { Node } from "../core/ast.js";

/**
 * What one pass learned and later passes need (e.g. the emulated runtime model), for one deobfuscation run.
 * Keys are typed so readers get the type the writer stored.
 */
export interface FactKey<T> {
    readonly name: string;
    /** Never set; only carries the type. */
    readonly type?: T;
}

export const factKey = <T>(name: string): FactKey<T> => ({ name });

/** Told that the statements `originals` gave way to `replacements`, which together do exactly what they did. */
export type ReplacementListener = (originals: readonly Node[], replacements: readonly Node[]) => void;

export class Facts {
    readonly #values = new Map<string, unknown>();
    readonly #cleanups: (() => void)[] = [];
    readonly #replacementListeners: ReplacementListener[] = [];

    get<T>(key: FactKey<T>): T | undefined {
        return this.#values.get(key.name) as T | undefined; // only `set` with the same key writes this name
    }

    set<T>(key: FactKey<T>, value: T): void {
        this.#values.set(key.name, value);
    }

    /** Register cleanup for resources a fact holds (e.g. a sandbox). Runs when the deobfuscation run ends. */
    onDispose(cleanup: () => void): void {
        this.#cleanups.push(cleanup);
    }

    /**
     * Facts keyed by statement follow their statements through rewrites. A pass that replaces statements by
     * equivalent ones (splitting a sequence, keeping the branch an `if` takes, unflattening a machine) reports it here,
     * and each fact's owner decides what carries over (see `onReplace`). Nothing is told about removed statements:
     * their facts simply no longer apply to anything in the program.
     */
    replaced(originals: readonly Node[], replacements: readonly Node[]): void {
        for (const listener of this.#replacementListeners) listener(originals, replacements);
    }

    /** Follow statement replacements (see `replaced`), for facts keyed by statement. */
    onReplace(listener: ReplacementListener): void {
        this.#replacementListeners.push(listener);
    }

    dispose(): void {
        for (const cleanup of this.#cleanups.splice(0)) cleanup();
    }
}
