import type { Node } from "../../core/ast.js";
import { factKey } from "../../pipeline/facts.js";

/** From the global object for builtins (`[]` is the global object), from the storage object for the runtime. */
export type PropertyPath = readonly string[];

export const pathName = (path: PropertyPath): string => (path.length === 0 ? "globalThis" : path.join("."));

/** A property the obfuscator's setup function added to a builtin, standing in for an existing one. */
export interface Alias {
    /** Path from the global object: `[]`, `["String"]`, `["String", "prototype"]`. */
    readonly owner: PropertyPath;
    readonly alias: string;
    readonly original: string;
}

/**
 * `"static"`: `G.alias(a)` is `Owner.original(a)`; `"method"`: `G.alias(x, a)` is `x.original(a)`; `"call"`:
 * `G.alias(x, a)` is `Owner.original.call(x, a)`.
 */
export type CallStyle = "static" | "method" | "call";

/** A storage getter handing out a builtin: `G.alias()` is the builtin; arguments are passed on per `style`. */
export interface CallAlias {
    readonly key: string;
    readonly owner: PropertyPath;
    readonly original: string;
    readonly style: CallStyle;
    /**
     * `"method"` with `x` `null` or `undefined`: the call may go on (to another builtin) where `x.original(a)` throws,
     * so it stands for that only where `x` is neither.
     */
    readonly nullishCalls: boolean;
}

/** `G.name = function () { return typeof T === "function" ? T.apply(O, arguments) : T; }`, with T and O as storage paths. */
export interface Wrapper {
    readonly key: string;
    readonly target: PropertyPath;
    readonly receiver: PropertyPath | undefined;
    /**
     * The root statement assigning the wrapper's function, as the analyses use it: ordered against other statements
     * (`decoder.ts`), its function read for the receiver (`effects.ts`), kept or removed with the wrapper (`cleanup.ts`,
     * `storage-usage.ts`, calculators).
     */
    readonly definition: Node;
}

export interface RuntimeModel {
    /** `G`. */
    readonly storage: string;
    /** The program, or the lone top-level IIFE, whose scope declares the storage binding. */
    readonly root: Node;
    /** Storage keys holding the global object after the prelude (`getters.ts`'s slots, `index.ts`'s `globalKeysOf`). */
    readonly globalKeys: ReadonlySet<string>;
    readonly aliases: readonly Alias[];
    /**
     * Names the program added to builtins that read like a builtin property through a getter not proven to answer so
     * every time (`getters.ts`): not rewritten, so the setup call stays while the program names one.
     */
    readonly unprovenAliases: ReadonlySet<string>;
    readonly callAliases: ReadonlyMap<string, CallAlias>;
    /** `G.key()` is `globalThis[name]`; by key, the global property's name. */
    readonly globalReads: ReadonlyMap<string, string>;
    /**
     * Setup globals forwarding to a host global the builtins lack (`document`): reads/writes go to `globalThis[name]`
     * (model 10: the host's globals exist). By alias name.
     */
    readonly hostAliases: ReadonlyMap<string, string>;
    readonly wrappers: ReadonlyMap<string, Wrapper>;
    /**
     * Root `G.k = ...` statements whose right side changes no builtin, global or storage property (`getters.ts`'s
     * evaluator). By node, as `setup`.
     */
    readonly local: ReadonlySet<Node>;
    /**
     * Root call statements that defined aliases or storage properties. A statement replaced by one equivalent statement
     * keeps it (`Facts.replaced`); one split or removed loses it.
     */
    readonly setup: ReadonlySet<Node>;
    /** Storage keys the setup calls define, whatever the property (call-alias getters, proven or not, and data properties). */
    readonly setupKeys: ReadonlySet<string>;
    /**
     * Names the setup calls add to what `G`, a function, inherits (`Function.prototype`, `Object.prototype`), whatever
     * the property: aliases, or not.
     */
    readonly inheritedKeys: ReadonlySet<string>;
    /** Setup keys whose calls provably never use `G` as `this` (`getters.ts`). */
    readonly thisFreeKeys: ReadonlySet<string>;
    /**
     * Global properties the setup calls added. The setup call stays while the program names one: app code reaches
     * them only by name (model 9), other scripts not at all (model 2).
     */
    readonly setupGlobals: ReadonlySet<string>;
}

export const RUNTIME = factKey<RuntimeModel>("runtime");
