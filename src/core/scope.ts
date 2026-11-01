import { analyze } from "eslint-scope";
import type { Reference, Scope, ScopeManager, Variable } from "eslint-scope";
import { visitorKeys } from "oxc-parser";
import type { MemberExpression, Node, Program } from "./ast.js";
import { forEachChild } from "./traverse.js";

export type { Reference, Scope, Variable };

/** eslint-scope is typed against `estree`; oxc produces the same ESTree shapes, so this is the one cast between the two. */
type EstreeNode = Parameters<ScopeManager["acquire"]>[0];
const asEstree = (node: Node): EstreeNode => node as unknown as EstreeNode;

/**
 * Child keys eslint-scope lacks: only `import(source, options)` would be walked short (options can hold references).
 * Kept minimal: esrecurse copies these keys into every visitor, so passing all of oxc's keys is slow.
 * Known gap: eslint-scope doesn't visit decorators.
 */
export const SCOPE_CHILD_KEYS: Readonly<Record<string, readonly string[]>> = { ImportExpression: visitorKeys["ImportExpression"] ?? ["source", "options"] };

/**
 * Parent pointers live on nodes under symbols (invisible to printer, comparison, `structuredClone`), stamped with the
 * walk that set them. A spread copy carries the fields along; `SELF` tells it apart from the original.
 */
const PARENT: unique symbol = Symbol("parent");
const STAMP: unique symbol = Symbol("stamp");
const SELF: unique symbol = Symbol("self");
type Marked = Node & { [PARENT]?: Node; [STAMP]?: number; [SELF]?: Node };
let stamps = 0;

const markedBy = (node: Node, stamp: number | undefined): node is Marked => (node as Marked)[STAMP] === stamp && (node as Marked)[SELF] === node;

/** Unresolved names that hold the global object (or, for `top`/`parent`, may: in a top-level window). */
const GLOBAL_OBJECT_NAMES: Record<string, true> = { globalThis: true, window: true, self: true, frames: true, top: true, parent: true };

/** Nodes whose code gets its own `this`: functions (not arrows), class fields and static blocks. */
const BINDS_THIS: Record<string, true> = { FunctionDeclaration: true, FunctionExpression: true, PropertyDefinition: true, AccessorProperty: true, StaticBlock: true };

/** Comparisons whose operands' values go nowhere. */
const EQUALITY: Record<string, true> = { "===": true, "!==": true, "==": true, "!=": true };

const spelledName = (node: Node): string | undefined => {
    switch (node.type) {
        case "Literal":
            return typeof node.value === "string" ? node.value : undefined;
        case "TemplateElement":
            return node.value.cooked ?? undefined;
        case "MemberExpression":
            return !node.computed && node.property.type === "Identifier" ? node.property.name : undefined;
        case "Property":
        case "MethodDefinition":
        case "PropertyDefinition":
        case "AccessorProperty":
            return !node.computed && node.key.type === "Identifier" ? node.key.name : undefined;
        default:
            return undefined;
    }
};

/** How code can reach the global object's properties other than by a binding's name, as of the last walk. */
export interface GlobalReach {
    /** Strings, template texts and static property names: a global so named may be reached as a property. */
    readonly spelled: ReadonlySet<string>;
    /** Computed members on an expression that may be the global object (`window[k]`, `this[k]` where `this` may be it). */
    readonly members: readonly MemberExpression[];
    /** Where the global object's value goes somewhere (`var g = window`, `f(this)`): any key may be read there. */
    readonly escapes: readonly Node[];
}

/**
 * Callers must ask for a fresh `ScopeInfo` after changing bindings or references (the pipeline does this).
 * Lookups are by node identity, so only nodes present at analysis time are known.
 */
export class ScopeInfo {
    readonly manager: ScopeManager;
    readonly #references = new Map<Node, Reference>();
    readonly #declarations = new Map<Node, Variable>();
    #generation = 0;
    #program: Program;
    #stamp: number | undefined;
    /** What the last walk found (`GlobalReach`); spelled names counted, so `forget` can take removed ones away. */
    #spelled = new Map<string, number>();
    #members: MemberExpression[] = [];
    #escapes: Node[] = [];

    constructor(program: Program) {
        this.#program = program;
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

    /** Changes only on refresh/forget; callers may cache against it. */
    get generation(): number {
        return this.#generation;
    }

    /** Drop references no longer in `program`; valid only when no binding was added, removed or moved. Nodes created since resolve to nothing. */
    refresh(program: Program): void {
        this.#generation++;
        this.#program = program;
        const stamp = this.#mark();
        const dropped = new Set<Reference>();
        for (const [identifier, reference] of this.#references) if (!markedBy(identifier, stamp)) dropped.add(reference);
        this.#drop(dropped);
    }

    /** Parent as of the last walk; none for nodes created or removed since. */
    parentOf(node: Node): Node | undefined {
        const stamp = this.#stamp ?? this.#mark();
        return markedBy(node, stamp) ? node[PARENT] : undefined;
    }

    /** See `GlobalReach`; from the last walk, without what `forget` took away since. */
    globalReach(): GlobalReach {
        const stamp = this.#stamp ?? this.#mark();
        const spelled = new Set<string>();
        for (const [name, count] of this.#spelled) if (count > 0) spelled.add(name);
        return { spelled, members: this.#members.filter((member) => markedBy(member, stamp)), escapes: this.#escapes.filter((node) => markedBy(node, stamp)) };
    }

    /** Whether `node` is the global object: `this` where it is (`thisIsGlobal`), or an unresolved global name for it. */
    #isGlobalObject(node: Node, thisIsGlobal: boolean): boolean {
        if (node.type === "ThisExpression") return thisIsGlobal;
        return node.type === "Identifier" && GLOBAL_OBJECT_NAMES[node.name] === true && this.#references.has(node) && this.staticVariableOf(node) === undefined;
    }

    /**
     * Point every node at its parent, in one walk in document order, collecting the global reach along: `this` may be
     * the global object at a script's top level and in a sloppy function (called unbound); its value goes nowhere as a
     * member's object, under `typeof` or in an equality.
     */
    #mark(): number {
        const program = this.#program;
        const stamp = ++stamps;
        this.#stamp = stamp;
        const spelled = new Map<string, number>();
        const members: MemberExpression[] = [];
        const escapes: Node[] = [];
        let parent: Node = program;
        let thisIsGlobal = program.sourceType === "script";
        let first: Node | undefined;
        let second: Node | undefined;
        const visit = (child: Node): void => {
            const above = parent;
            const marked = child as Marked;
            marked[PARENT] = above;
            marked[STAMP] = stamp;
            marked[SELF] = child;
            const name = spelledName(child);
            if (name !== undefined) spelled.set(name, (spelled.get(name) ?? 0) + 1);
            if (child.type === "ThisExpression" || child.type === "Identifier") {
                if (child !== first && child !== second && this.#isGlobalObject(child, thisIsGlobal)) escapes.push(child);
            } else if (child.type === "MemberExpression" && child.computed && this.#isGlobalObject(child.object, thisIsGlobal)) members.push(child);
            const outerThis = thisIsGlobal;
            const outerFirst = first;
            const outerSecond = second;
            if (child.type === "FunctionDeclaration" || child.type === "FunctionExpression") thisIsGlobal = this.scopeOf(child)?.isStrict === false;
            else if (BINDS_THIS[child.type] === true) thisIsGlobal = false;
            first = child.type === "MemberExpression" ? child.object : child.type === "UnaryExpression" && child.operator === "typeof" ? child.argument : undefined;
            second = undefined;
            if (child.type === "BinaryExpression" && EQUALITY[child.operator] === true) {
                first = child.left;
                second = child.right;
            }
            parent = child;
            forEachChild(child, visit);
            parent = above;
            thisIsGlobal = outerThis;
            first = outerFirst;
            second = outerSecond;
        };
        forEachChild(program, visit);
        this.#spelled = spelled;
        this.#members = members;
        this.#escapes = escapes;
        return stamp;
    }

    /** `refresh` for removed subtrees only, without walking the whole program. */
    forget(removed: Iterable<Node>): void {
        this.#generation++;
        const dropped = new Set<Reference>();
        const collect = (node: Node): void => {
            if (markedBy(node, this.#stamp)) {
                const name = spelledName(node);
                if (name !== undefined) this.#spelled.set(name, (this.#spelled.get(name) ?? 1) - 1);
            }
            (node as Marked)[STAMP] = 0;
            if (node.type === "Identifier") {
                const reference = this.#references.get(node);
                if (reference !== undefined) dropped.add(reference);
            }
            forEachChild(node, collect);
        };
        for (const node of removed) collect(node);
        this.#drop(dropped);
    }

    /** Take `dropped` out of every list that holds them: only the scopes and variables they were in change. */
    #drop(dropped: ReadonlySet<Reference>): void {
        if (dropped.size === 0) return;
        const scopes = new Set<Scope>();
        const variables = new Set<Variable>();
        for (const reference of dropped) {
            this.#references.delete(reference.identifier as unknown as Node);
            if (reference.resolved !== null) variables.add(reference.resolved);
            // A reference sits in its own scope's list and in `through` up to the scope that resolves it.
            for (let scope: Scope | null = reference.from; scope !== null; scope = scope.upper) {
                scopes.add(scope);
                if (reference.resolved !== null && scope === reference.resolved.scope) break;
            }
        }
        const live = (reference: Reference): boolean => !dropped.has(reference);
        for (const scope of scopes) {
            scope.references = scope.references.filter(live);
            scope.through = scope.through.filter(live);
        }
        for (const variable of variables) variable.references = variable.references.filter(live);
        this.#globals = undefined;
        this.#staticReferences = undefined;
    }

    referenceOf(identifier: Node): Reference | undefined {
        return this.#references.get(identifier);
    }

    variableOf(identifier: Node): Variable | undefined {
        return this.#declarations.get(identifier) ?? this.#references.get(identifier)?.resolved ?? undefined;
    }

    isGlobalReference(identifier: Node): boolean {
        const reference = this.#references.get(identifier);
        return reference !== undefined && reference.resolved === null;
    }

    #globals: Map<string, Reference[]> | undefined;

    /** Unbound references to `name`; script top-level declarations are bound, not global. */
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

    declaresName(name: string): boolean {
        this.#declared ??= new Set(this.manager.scopes.flatMap((scope) => scope.variables.map((variable) => variable.name)));
        return this.#declared.has(name);
    }

    /** Whether `name` is declared in scope at reference `site`; `undefined` when `site` is unknown. */
    nameBoundAt(site: Node, name: string): boolean | undefined {
        const from = this.#references.get(site)?.from;
        if (from === undefined) return undefined;
        for (let scope: Scope | null = from; scope !== null; scope = scope.upper) if (scope.set.has(name)) return true;
        return false;
    }

    #resolveStatically(reference: Reference): Variable | undefined {
        const name = reference.identifier.name;
        for (let scope: Scope | null = reference.from; scope !== null; scope = scope.upper) {
            if (scope.type === "with") return undefined;
            const variable = scope.set.get(name);
            if (variable !== undefined) return variable;
        }
        return undefined;
    }

    /** Like `variableOf`, but also resolves names eslint-scope left dynamic due to direct `eval`. `undefined` through `with`. */
    staticVariableOf(identifier: Node): Variable | undefined {
        const known = this.variableOf(identifier);
        if (known !== undefined) return known;
        const reference = this.#references.get(identifier);
        return reference === undefined ? undefined : this.#resolveStatically(reference);
    }

    #staticReferences: Map<Variable, Reference[]> | undefined;
    #mergedReferences = new Map<Variable, readonly Reference[]>();

    /** Every reference to `variable` under static scoping (see `staticVariableOf`). */
    staticReferences(variable: Variable): readonly Reference[] {
        if (this.#staticReferences === undefined) {
            this.#staticReferences = new Map();
            this.#mergedReferences = new Map();
            for (const reference of this.manager.globalScope?.through ?? []) {
                const target = this.#resolveStatically(reference);
                if (target === undefined) continue;
                const list = this.#staticReferences.get(target);
                if (list === undefined) this.#staticReferences.set(target, [reference]);
                else list.push(reference);
            }
        }
        const merged = this.#mergedReferences.get(variable);
        if (merged !== undefined) return merged;
        const unresolved = this.#staticReferences.get(variable);
        const references = unresolved === undefined ? variable.references : [...variable.references, ...unresolved];
        this.#mergedReferences.set(variable, references);
        return references;
    }

    scopeOf(node: Node): Scope | null {
        return this.manager.acquire(asEstree(node));
    }
}
