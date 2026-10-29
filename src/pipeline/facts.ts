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

export class Facts {
    readonly #values = new Map<string, unknown>();
    readonly #cleanups: (() => void)[] = [];

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

    dispose(): void {
        for (const cleanup of this.#cleanups.splice(0)) cleanup();
    }
}
