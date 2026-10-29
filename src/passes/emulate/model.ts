import type { Node } from "../../core/ast.js";
import type { Value } from "../../core/evaluate.js";
import { factKey } from "../../pipeline/facts.js";
import type { BuiltIdentities, CallStyle, Guest, LoggedCall, PropertyPath } from "./guest.js";

/** A property the obfuscator's setup function added to a builtin, standing in for an existing one. */
export interface Alias {
    /** Where it lives, as a path from the global object: `[]` (a global), `["String"]`, `["String", "prototype"]`. */
    readonly owner: PropertyPath;
    readonly alias: string;
    /** The builtin property with the same value. */
    readonly original: string;
}

/**
 * A getter on the storage object that hands out a builtin through a function (newer setup variant): `G.alias()` is the
 * builtin itself; with arguments it passes them on as its probed `style` says.
 */
export interface CallAlias {
    readonly key: string;
    readonly owner: PropertyPath;
    readonly original: string;
    readonly style: CallStyle;
}

/** `G.name = function () { return typeof T === "function" ? T.apply(O, arguments) : T; }`, with T and O as storage paths. */
export interface Wrapper {
    readonly key: string;
    /** `T` as a path on the storage object, e.g. `["k", "m"]`. */
    readonly target: PropertyPath;
    /** `O`, the `this` the target is applied with, when it is a storage path too. */
    readonly receiver: PropertyPath | undefined;
    /** The root statement that defined it (for log lines). */
    readonly definition: Node;
}

/** What running the obfuscator's runtime prelude in the sandbox revealed. */
export interface RuntimeModel {
    /** The object the runtime keeps everything on (`G`). */
    readonly storage: string;
    /** The program, or the lone top-level IIFE, whose scope declares the storage binding. */
    readonly root: Node;
    /** Keys of the storage object holding the global object. */
    readonly globalKeys: ReadonlySet<string>;
    readonly aliases: readonly Alias[];
    /** Call-style aliases on the storage object, by key. */
    readonly callAliases: ReadonlyMap<string, CallAlias>;
    /**
     * Getters on the storage object handing out a function whose zero-argument call reads a global property and
     * returns it: `G.key()` is `globalThis[name]`. By key, the global property's name.
     */
    readonly globalReads: ReadonlyMap<string, string>;
    /**
     * Setup globals forwarding to a global property the guest lacks, a host object (`document`, `console`): reading
     * one reads `globalThis[name]` (the host's getter twice; model 7 covers the host's own properties too), writing
     * one writes it. By the alias's name, the global property's name.
     */
    readonly hostAliases: ReadonlyMap<string, string>;
    /** Wrapper functions on the storage object, by key. */
    readonly wrappers: ReadonlyMap<string, Wrapper>;
    /**
     * Results of wrapper calls made while the prelude ran, by call site. Keyed by node: a site a later pass replaces
     * loses its result (resolve-calls logs how many).
     */
    readonly callResults: ReadonlyMap<Node, Value>;
    /** Wrapper calls made while the prelude ran that couldn't be tied to a call site (their sites are ambiguous). */
    readonly unmappedCalls: readonly LoggedCall[];
    /** The logged call behind each site in `callResults` (and sites whose result wasn't a primitive), by node like it. */
    readonly siteCalls: ReadonlyMap<Node, LoggedCall>;
    /**
     * Wrapper calls the guest made while it still matched a real run (before the statement from which it may differ),
     * in the order they were made: these say how the runtime's state really evolved.
     */
    readonly preludeCalls: readonly LoggedCall[];
    /**
     * For root statements `G.k = (function () {...})()` the guest ran: the identities of what they stored and of its
     * methods, right after they ran. By node, as `setup`.
     */
    readonly built: ReadonlyMap<Node, BuiltIdentities>;
    /** Root statements that ran without changing anything outside the storage object (builtins, globals). By node, as `setup`. */
    readonly pure: ReadonlySet<Node>;
    /**
     * Root call statements that defined aliases (the setup function's call). By node: a statement replaced by one
     * equivalent statement keeps it (`Facts.replaced`), one split into several or removed loses it; cleanup logs those.
     */
    readonly setup: ReadonlySet<Node>;
    /**
     * Storage keys the setup calls installed: the call-alias getters, including those whose style couldn't be probed.
     * Like call aliases, they hand out builtins and don't use the storage object as `this`.
     */
    readonly setupKeys: ReadonlySet<string>;
    /**
     * Global properties the setup calls added: alias holders, aliases of global builtins, accessors forwarding to host
     * properties the guest lacks. They go with the setup call, so it stays while the program names one: app code
     * reaches them only by name (model 9), other scripts not at all (model 2).
     */
    readonly setupGlobals: ReadonlySet<string>;
    /**
     * Root statements the guest ran to completion: what their top-level code wrote is in the snapshot. Statements that
     * replace executed ones (`Facts.replaced`) count as executed too.
     */
    readonly executed: ReadonlySet<Node>;
    /** The sandbox, still holding the runtime state after the prelude. */
    readonly guest: Guest;
}

export const RUNTIME = factKey<RuntimeModel>("runtime");
