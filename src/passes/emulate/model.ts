import type { Node } from "../../core/ast.js";
import type { Value } from "../../core/evaluate.js";
import { factKey } from "../../pipeline/facts.js";
import type { BuiltIdentities, CallStyle, Guest, LoggedCall, PropertyPath } from "./guest.js";

/** A property the obfuscator's setup function added to a builtin, standing in for an existing one. */
export interface Alias {
    /** Path from the global object: `[]`, `["String"]`, `["String", "prototype"]`. */
    readonly owner: PropertyPath;
    readonly alias: string;
    readonly original: string;
}

/** A storage getter handing out a builtin: `G.alias()` is the builtin; arguments are passed on per `style`. */
export interface CallAlias {
    readonly key: string;
    readonly owner: PropertyPath;
    readonly original: string;
    readonly style: CallStyle;
}

/** `G.name = function () { return typeof T === "function" ? T.apply(O, arguments) : T; }`, with T and O as storage paths. */
export interface Wrapper {
    readonly key: string;
    readonly target: PropertyPath;
    readonly receiver: PropertyPath | undefined;
    /** For log lines. */
    readonly definition: Node;
}

export interface RuntimeModel {
    /** `G`. */
    readonly storage: string;
    /** The program, or the lone top-level IIFE, whose scope declares the storage binding. */
    readonly root: Node;
    readonly globalKeys: ReadonlySet<string>;
    readonly aliases: readonly Alias[];
    readonly callAliases: ReadonlyMap<string, CallAlias>;
    /** `G.key()` is `globalThis[name]`; by key, the global property's name. */
    readonly globalReads: ReadonlyMap<string, string>;
    /**
     * Setup globals forwarding to a host global the guest lacks (`document`): reads/writes go to `globalThis[name]`
     * (model 7 covers the host's own properties). By alias name.
     */
    readonly hostAliases: ReadonlyMap<string, string>;
    readonly wrappers: ReadonlyMap<string, Wrapper>;
    /** Keyed by node: a site a later pass replaces loses its result (resolve-calls logs how many). */
    readonly callResults: ReadonlyMap<Node, Value>;
    /** Calls whose sites are ambiguous. */
    readonly unmappedCalls: readonly LoggedCall[];
    /** The logged call behind each site in `callResults` (and sites whose result wasn't a primitive), by node like it. */
    readonly siteCalls: ReadonlyMap<Node, LoggedCall>;
    /** Wrapper calls made while the guest still matched a real run, in order: the runtime's real state evolution. */
    readonly preludeCalls: readonly LoggedCall[];
    /** Identities of what root `G.k = (function () {...})()` statements stored, and of its methods. By node, as `setup`. */
    readonly built: ReadonlyMap<Node, BuiltIdentities>;
    /** Root statements that changed nothing outside the storage object. By node, as `setup`. */
    readonly pure: ReadonlySet<Node>;
    /**
     * Root call statements that defined aliases. A statement replaced by one equivalent statement keeps it
     * (`Facts.replaced`); one split or removed loses it.
     */
    readonly setup: ReadonlySet<Node>;
    /** Storage keys the setup calls installed (call-alias getters, probed or not); they don't use `G` as `this`. */
    readonly setupKeys: ReadonlySet<string>;
    /**
     * Global properties the setup calls added. The setup call stays while the program names one: app code reaches
     * them only by name (model 9), other scripts not at all (model 2).
     */
    readonly setupGlobals: ReadonlySet<string>;
    /** Root statements the guest ran to completion (including their `Facts.replaced` replacements). */
    readonly executed: ReadonlySet<Node>;
    readonly guest: Guest;
}

export const RUNTIME = factKey<RuntimeModel>("runtime");
