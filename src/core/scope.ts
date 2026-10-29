import { analyze } from "eslint-scope";
import type { Reference, Scope, ScopeManager, Variable } from "eslint-scope";
import { visitorKeys } from "oxc-parser";
import type { Node, Program } from "./ast.js";
import { forEachChild } from "./traverse.js";

export type { Reference, Scope, Variable };

/** eslint-scope is typed against `estree`; oxc produces the same ESTree shapes, so this is the one cast between the two. */
type EstreeNode = Parameters<ScopeManager["acquire"]>[0];
const asEstree = (node: Node): EstreeNode => node as unknown as EstreeNode;

/**
 * Child keys eslint-scope needs beyond its own (estraverse 5.3's, ESTree up to ES2021). Node types estraverse doesn't
 * know are walked by iteration (`fallback`), and eslint-scope handles classes, imports and exports itself, so the only
 * JS shape it would walk short is `import(source, options)`: the options can hold references. Kept this small on
 * purpose: esrecurse copies the merged keys into every visitor it creates, one per pattern, which made passing all
 * of oxc's keys the slowest part of the analysis. (Known gap, as before: eslint-scope doesn't visit decorators.)
 */
export const SCOPE_CHILD_KEYS: Readonly<Record<string, readonly string[]>> = { ImportExpression: visitorKeys["ImportExpression"] ?? ["source", "options"] };

/**
 * Scope analysis for one program, as it is right now.
 *
 * Any pass that changes bindings or references must ask for a fresh `ScopeInfo` afterwards (the pipeline does this).
 * Lookups are by node identity, so they only work for nodes that were in the program when it was analyzed.
 */
export class ScopeInfo {
    readonly manager: ScopeManager;
    readonly #references = new Map<Node, Reference>();
    readonly #declarations = new Map<Node, Variable>();

    constructor(program: Program) {
        this.manager = analyze(asEstree(program) as Parameters<typeof analyze>[0], {
            ecmaVersion: 2022,
            sourceType: program.sourceType === "module" ? "module" : "script",
            childVisitorKeys: SCOPE_CHILD_KEYS as Record<string, string[]>,
            fallback: "iteration",
        });
        for (const scope of this.manager.scopes) {
            for (const reference of scope.references) this.#references.set(reference.identifier as unknown as Node, reference);
            for (const variable of scope.variables) for (const id of variable.identifiers) this.#declarations.set(id as unknown as Node, variable);
        }
    }

    /**
     * Forget references whose identifier is no longer in `program`, after passes that only replaced expressions (no
     * binding added, removed or moved). The analysis is then what a fresh one would give, except that it doesn't know
     * the nodes created since: their identifiers resolve to nothing.
     */
    refresh(program: Program): void {
        const attached = new Set<Node>();
        const collect = (node: Node): void => {
            if (node.type === "Identifier") attached.add(node);
            forEachChild(node, collect);
        };
        collect(program);
        const live = (reference: Reference): boolean => attached.has(reference.identifier as unknown as Node);
        for (const scope of this.manager.scopes) {
            scope.references = scope.references.filter(live);
            scope.through = scope.through.filter(live);
            for (const variable of scope.variables) variable.references = variable.references.filter(live);
        }
        for (const identifier of this.#references.keys()) if (!attached.has(identifier)) this.#references.delete(identifier);
        this.#globals = undefined;
        this.#staticReferences = undefined;
    }

    /** The reference for an identifier that reads or writes a variable. */
    referenceOf(identifier: Node): Reference | undefined {
        return this.#references.get(identifier);
    }

    /** The variable an identifier declares or refers to. `undefined` for globals and names that resolve to nothing. */
    variableOf(identifier: Node): Variable | undefined {
        return this.#declarations.get(identifier) ?? this.#references.get(identifier)?.resolved ?? undefined;
    }

    /** True when the identifier is a reference that doesn't resolve to any declaration in the program. */
    isGlobalReference(identifier: Node): boolean {
        const reference = this.#references.get(identifier);
        return reference !== undefined && reference.resolved === null;
    }

    #globals: Map<string, Reference[]> | undefined;

    /**
     * References to `name` that no declaration in the program binds (host globals, implicit globals), anywhere in the
     * program. A script's top-level declarations resolve like any other: their references are on the variable.
     */
    globalReferences(name: string): readonly Reference[] {
        if (this.#globals === undefined) {
            this.#globals = new Map();
            for (const reference of this.manager.globalScope?.through ?? []) {
                const list = this.#globals.get(reference.identifier.name);
                if (list === undefined) this.#globals.set(reference.identifier.name, [reference]);
                else list.push(reference);
            }
        }
        return this.#globals.get(name) ?? [];
    }

    #declared: Set<string> | undefined;

    /** Whether any scope in the program declares `name` (e.g. a parameter called `undefined`). */
    declaresName(name: string): boolean {
        this.#declared ??= new Set(this.manager.scopes.flatMap((scope) => scope.variables.map((variable) => variable.name)));
        return this.#declared.has(name);
    }

    /**
     * Whether `name` is declared around the reference `site` (in its scope or one enclosing it), so the global of that
     * name isn't what `name` would mean there. `undefined` when `site` isn't a reference the analysis knows.
     */
    nameBoundAt(site: Node, name: string): boolean | undefined {
        const from = this.#references.get(site)?.from;
        if (from === undefined) return undefined;
        for (let scope: Scope | null = from; scope !== null; scope = scope.upper) if (scope.set.has(name)) return true;
        return false;
    }

    /** The variable `reference` names under static scoping (see `staticVariableOf`). */
    #resolveStatically(reference: Reference): Variable | undefined {
        const name = reference.identifier.name;
        for (let scope: Scope | null = reference.from; scope !== null; scope = scope.upper) {
            if (scope.type === "with") return undefined;
            const variable = scope.set.get(name);
            if (variable !== undefined) return variable;
        }
        return undefined;
    }

    /**
     * The variable an identifier refers to under static scoping: also where eslint-scope leaves it unresolved because a
     * direct `eval` made the scope dynamic. For analyses that take code an eval runs not to use this script's names
     * (it is another script's code). `undefined` for real globals, and through `with`.
     */
    staticVariableOf(identifier: Node): Variable | undefined {
        const known = this.variableOf(identifier);
        if (known !== undefined) return known;
        const reference = this.#references.get(identifier);
        return reference === undefined ? undefined : this.#resolveStatically(reference);
    }

    #staticReferences: Map<Variable, Reference[]> | undefined;

    /** Every reference to `variable` under static scoping (see `staticVariableOf`). */
    staticReferences(variable: Variable): readonly Reference[] {
        if (this.#staticReferences === undefined) {
            this.#staticReferences = new Map();
            for (const reference of this.manager.globalScope?.through ?? []) {
                const target = this.#resolveStatically(reference);
                if (target === undefined) continue;
                const list = this.#staticReferences.get(target);
                if (list === undefined) this.#staticReferences.set(target, [reference]);
                else list.push(reference);
            }
        }
        const unresolved = this.#staticReferences.get(variable);
        return unresolved === undefined ? variable.references : [...variable.references, ...unresolved];
    }

    /** The scope a function, block or program node creates, if any. */
    scopeOf(node: Node): Scope | null {
        return this.manager.acquire(asEstree(node));
    }
}
