import { analyze, Reference as ScopeReference } from "eslint-scope";
import type { Reference, Scope, ScopeManager, Variable } from "eslint-scope";
import { visitorKeys } from "oxc-parser";
import type { CatchClause, Function as FunctionDeclaration, MemberExpression, Node, Program } from "./ast.js";
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
const SCOPE_CHILD_KEYS: Readonly<Record<string, readonly string[]>> = { ImportExpression: visitorKeys["ImportExpression"] ?? ["source", "options"] };

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

/** Unresolved names that always hold this realm's global object (`frames` is the window itself). */
export const OWN_GLOBAL_OBJECT_NAMES: Readonly<Record<string, true>> = { globalThis: true, window: true, self: true, frames: true };

/**
 * Unresolved names that may hold the global object: `top`/`parent` do in a top-level window, else they hold another
 * window (whose members a cross-origin read throws on), so analyses that need this realm's object use the set above.
 */
const GLOBAL_OBJECT_NAMES: Readonly<Record<string, true>> = { ...OWN_GLOBAL_OBJECT_NAMES, top: true, parent: true };

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

/** eslint-scope's own (untyped) check that a parameter default doesn't see the body's declarations. */
const resolves = (scope: Scope, reference: Reference, variable: Variable): boolean =>
    // oxlint-disable-next-line no-underscore-dangle -- eslint-scope's method, called for parity with its resolution
    (scope as Scope & { __isValidResolution(reference: Reference, variable: Variable): boolean }).__isValidResolution(reference, variable);

/**
 * Whether definitions make a `var` of their name in their scope an early error (so Annex B leaves a block function
 * alone). A block function in a block between does too by the spec, but V8 still binds the inner one function-wide:
 * both are allowed for (`#annexBBinds`, `annexBName`).
 */
const blocksAnnexB = (defs: readonly Variable["defs"][number][]): boolean =>
    defs.some(
        (def) =>
            def.type === "ClassName" ||
            def.type === "ImportBinding" ||
            def.type === "Parameter" ||
            (def.type === "Variable" && def.kind !== "var") ||
            // Annex B allows a `var` of a catch parameter's name only when the parameter is a plain identifier.
            (def.type === "CatchClause" && (def.node as unknown as CatchClause).param?.type !== "Identifier")
    );

/**
 * The statements directly in the list of the node a scope belongs to. A function body's are also those under labels
 * (a labelled function declaration there is a plain one); in a block, Annex B covers only functions directly in it.
 */
const listedStatements = (block: Node): Set<Node> => {
    let list: readonly Node[] = [];
    let throughLabels = false;
    if (block.type === "BlockStatement" || block.type === "StaticBlock") list = block.body;
    else if (block.type === "SwitchStatement") list = block.cases.flatMap((switchCase) => switchCase.consequent);
    else if (block.type === "Program") {
        list = block.body;
        throughLabels = true;
    } else if ((block.type === "FunctionDeclaration" || block.type === "FunctionExpression" || block.type === "ArrowFunctionExpression") && block.body?.type === "BlockStatement") {
        list = block.body.body;
        throughLabels = true;
    }
    const listed = new Set<Node>();
    for (const statement of list) {
        listed.add(statement);
        if (throughLabels) for (let labeled = statement; labeled.type === "LabeledStatement"; labeled = labeled.body) listed.add(labeled.body);
    }
    return listed;
};

/**
 * Callers must ask for a fresh `ScopeInfo` after changing bindings or references (the pipeline does this).
 * Lookups are by node identity, so only nodes present at analysis time are known.
 *
 * eslint-scope doesn't model Annex B: a sloppy block function `{ function f() {} }` also binds `f` function-wide.
 * Where its function (or script) has no variable `f`, references there resolve past that binding, so they are made
 * unknown here; where it has one, the block function's evaluation writes it, so that write is added to its references.
 * An `if` clause's function declaration (`if (x) function f() {}`) sits in a block of its own, which eslint-scope
 * doesn't make: references to the variable it gets instead are unknown too (`#clauseVariables`). A labelled function
 * declaration in a block (`{ l: function f() {} }`) is taken for one: Annex B covers only functions directly in a
 * block by the spec (V8 binds it function-wide too), so the same unknowns cover both.
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
    /** Per function scope (or a script's global scope), the names Annex B binds that no variable of it stands for. */
    readonly #annexBNames = new Map<Scope, Set<string>>();
    /** Every name in `#annexBNames` or of a `#clauseVariables`: the test before a scope walk. */
    readonly #annexBAny = new Set<string>();
    /** Annex B's writes of a block function into its function's variable of the name, by the declaration's name node. */
    readonly #annexBWrites = new Map<Node, Reference>();
    /** Sloppy `if` clauses' function declarations, and labelled ones in blocks. */
    readonly #clauseFunctions = new Set<Node>();
    /**
     * Variables eslint-scope gives `if` clauses' functions in the clause's scope. At function level that is the `var`
     * Annex B makes, written only when the `if` runs (or a parameter or lexical binding keeping Annex B away), though
     * its definition calls it a hoisted function; in a block (when nothing else there declares the name) it stands for
     * no binding.
     */
    readonly #clauseVariables = new Set<Variable>();

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
        this.#modelAnnexB();
    }

    #modelAnnexB(): void {
        const listed = new Map<Scope, Set<Node>>();
        for (const scope of this.manager.scopes) {
            if (scope.isStrict) continue;
            const functionLevel = scope === scope.variableScope;
            for (const variable of scope.variables) {
                const defs = variable.defs.filter((def) => def.type === "FunctionName" && def.node.type === "FunctionDeclaration");
                if (defs.length === 0) continue;
                let statements = listed.get(scope);
                if (statements === undefined) {
                    statements = listedStatements(scope.block as unknown as Node);
                    listed.set(scope, statements);
                }
                let clauses = 0;
                for (const def of defs) {
                    if (statements.has(def.node as unknown as Node)) continue;
                    this.#clauseFunctions.add(def.node as unknown as Node);
                    clauses++;
                }
                if (clauses > 0 && (functionLevel || clauses === variable.defs.length)) {
                    this.#clauseVariables.add(variable);
                    this.#annexBAny.add(variable.name);
                }
                if (functionLevel) continue;
                for (const def of defs) {
                    if (!this.#annexBBinds(variable, def.node as unknown as Node)) continue;
                    const target = scope.variableScope;
                    const existing = target.set.get(variable.name);
                    if (existing === undefined) {
                        const names = this.#annexBNames.get(target);
                        if (names === undefined) this.#annexBNames.set(target, new Set([variable.name]));
                        else names.add(variable.name);
                        this.#annexBAny.add(variable.name);
                        continue;
                    }
                    const write = new ScopeReference(def.name, scope, ScopeReference.WRITE, null, null, false, false);
                    write.resolved = existing;
                    this.#annexBWrites.set(def.name as unknown as Node, write);
                }
            }
        }
    }

    /**
     * Whether sloppy function declaration `declaration` of `variable` may also bind its name function-wide (Annex B),
     * when a `var` of the name would not clash with a lexical declaration (or parameter) on the way up. True for a
     * function-level declaration, whose binding already is function-wide.
     */
    #annexBBinds(variable: Variable, declaration: Node): boolean {
        const scope = variable.scope;
        if (scope.isStrict) return false;
        const target = scope.variableScope;
        // An `if` clause's function sits in a block of its own: its scope's other declarations of the name are on the way up.
        if (this.#clauseFunctions.has(declaration) && blocksAnnexB(variable.defs.filter((def) => !this.#clauseFunctions.has(def.node as unknown as Node)))) return false;
        for (let current: Scope | null = scope; current !== target && current !== null;) {
            current = current.upper;
            const other = current?.set.get(variable.name);
            if (other !== undefined && blocksAnnexB(other.defs)) return false;
        }
        return true;
    }

    /**
     * The function-wide name `declaration` binds (for a block function: besides its block binding): sloppy code only,
     * where Annex B applies (`#annexBBinds`); `undefined` also for a declaration made since the analysis. Also
     * `undefined` where a block function of the name in a block on the way up (or, for an `if` clause's function, in
     * its own) binds it anyway: by the spec this one then binds nothing function-wide (its `var` would clash with that
     * function), and a `var` kept for it there would be an early error.
     */
    annexBName(declaration: FunctionDeclaration): string | undefined {
        const variable = declaration.id === null ? undefined : this.#declarations.get(declaration.id);
        if (variable === undefined || !this.#annexBBinds(variable, declaration)) return undefined;
        const target = variable.scope.variableScope;
        if (variable.scope === target) return variable.name;
        for (let current: Scope | null = this.#clauseFunctions.has(declaration) ? variable.scope : variable.scope.upper; current !== null && current !== target; current = current.upper) {
            const other = current.set.get(variable.name);
            if (other?.defs.some((def) => def.type === "FunctionName" && def.node.type === "FunctionDeclaration" && !this.#clauseFunctions.has(def.node as unknown as Node)) === true) return undefined;
        }
        return variable.name;
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
        let writes = false;
        for (const identifier of this.#annexBWrites.keys()) {
            if (markedBy(identifier, stamp)) continue;
            this.#annexBWrites.delete(identifier);
            writes = true;
        }
        this.#drop(dropped, writes);
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
        let writes = false;
        const collect = (node: Node): void => {
            if (markedBy(node, this.#stamp)) {
                const name = spelledName(node);
                if (name !== undefined) this.#spelled.set(name, (this.#spelled.get(name) ?? 1) - 1);
            }
            (node as Marked)[STAMP] = 0;
            if (node.type === "Identifier") {
                const reference = this.#references.get(node);
                if (reference !== undefined) dropped.add(reference);
                if (this.#annexBWrites.delete(node)) writes = true;
            }
            forEachChild(node, collect);
        };
        for (const node of removed) collect(node);
        this.#drop(dropped, writes);
    }

    /**
     * Take `dropped` out of every list that holds them: only the scopes and variables they were in change. `writes`:
     * an Annex B write went with a removed block function.
     */
    #drop(dropped: ReadonlySet<Reference>, writes: boolean): void {
        if (dropped.size === 0 && !writes) return;
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
        this.#annexBRead = undefined;
    }

    referenceOf(identifier: Node): Reference | undefined {
        return this.#references.get(identifier);
    }

    variableOf(identifier: Node): Variable | undefined {
        const declared = this.#declarations.get(identifier);
        if (declared !== undefined) return declared;
        const reference = this.#references.get(identifier);
        if (reference === undefined || reference.resolved === null || this.#annexBTakes(reference)) return undefined;
        return reference.resolved;
    }

    isGlobalReference(identifier: Node): boolean {
        const reference = this.#references.get(identifier);
        return reference !== undefined && reference.resolved === null && !this.#annexBTakes(reference);
    }

    /** A global reference, or an identifier made since the analysis whose name no scope declares. */
    namesGlobal(identifier: Node): boolean {
        if (identifier.type !== "Identifier") return false;
        return this.isGlobalReference(identifier) || (!this.#references.has(identifier) && !this.declaresName(identifier.name));
    }

    #globals: Map<string, Reference[]> | undefined;

    /**
     * Unbound references to `name` under static scoping (script top-level declarations are bound, not global; model
     * 2: code a direct `eval` runs doesn't use the script's names), or `undefined` when a `with` may intercept it.
     */
    globalReferences(name: string): readonly Reference[] | undefined {
        if (this.#withIntercepts(name, null)) return undefined;
        if (this.#globals === undefined) {
            this.#globals = new Map();
            for (const reference of this.manager.globalScope?.through ?? []) {
                // A variable, or an Annex B binding (`false`).
                if (this.#resolveStatically(reference) !== undefined) continue;
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
        for (let scope: Scope | null = from; scope !== null; scope = scope.upper) if (scope.set.has(name) || this.#annexBBindsIn(scope, name, site)) return true;
        return false;
    }

    /**
     * Whether `scope` binds `name`: a variable of it, or a function-wide Annex B binding no variable stands for (which
     * the function's parameter defaults don't see; this doesn't tell them apart).
     */
    bindsName(scope: Scope, name: string): boolean {
        return scope.set.has(name) || this.#annexBNames.get(scope)?.has(name) === true;
    }

    /**
     * Whether `scope` holds an Annex B binding of `name` that no variable of it stands for, and code at `at` sees it: a
     * function's parameter list (defaults) doesn't see its body's `var`s.
     */
    #annexBBindsIn(scope: Scope, name: string, at: Node): boolean {
        if (this.#annexBNames.get(scope)?.has(name) !== true) return false;
        const block = scope.block as unknown as Node;
        return block.type === "Program" || at.start >= (block as Node & { body: Node }).body.start;
    }

    /**
     * Whether a sloppy block function's function-wide binding (Annex B) takes `reference` before any variable does, or
     * the variable that does stands for no binding (`#clauseVariables`).
     */
    #annexBTakes(reference: Reference): boolean {
        return this.#annexBTaker(reference) !== undefined;
    }

    /**
     * The function scope whose Annex B binding `reference` may name, when `#annexBTakes`: for a `#clauseVariables` one,
     * its function's (the binding its `if` clause's function makes there, if any).
     */
    #annexBTaker(reference: Reference): Scope | undefined {
        const identifier = reference.identifier as unknown as Node;
        const name = reference.identifier.name;
        if (!this.#annexBAny.has(name)) return undefined;
        for (let scope: Scope | null = reference.from; scope !== null; scope = scope.upper) {
            const variable = scope.set.get(name);
            if (variable !== undefined && resolves(scope, reference, variable)) return this.#clauseVariables.has(variable) ? scope.variableScope : undefined;
            if (this.#annexBBindsIn(scope, name, identifier)) return scope;
        }
        return undefined;
    }

    /** Per function scope, the names of its Annex B bindings no variable stands for that some reference may read. */
    #annexBRead: Map<Scope, Set<string>> | undefined;

    /**
     * Whether the function a declaration of `variable` makes may be reached other than through `variable`'s references
     * (and so run, or escape, where they don't show it). A sloppy block function's value also goes to its function-wide
     * binding when the declaration runs (Annex B), from where a read of that binding takes it; at a script's top level
     * that binding is a global object property. References to an `if` clause's function are unknown.
     */
    annexBEscapes(variable: Variable): boolean {
        if (this.#clauseVariables.has(variable)) return true;
        return variable.defs.some((def) => {
            if (def.type !== "FunctionName" || def.node.type !== "FunctionDeclaration" || variable.scope === variable.scope.variableScope) return false;
            if (!this.#annexBBinds(variable, def.node as unknown as Node)) return false;
            const target = variable.scope.variableScope;
            if (target.type === "global") return true;
            const existing = target.set.get(variable.name);
            if (existing !== undefined && this.staticReferences(existing).some((reference) => reference.isRead())) return true;
            if (this.#annexBRead === undefined) {
                const read = new Map<Scope, Set<string>>();
                for (const reference of this.#references.values()) {
                    const taker = reference.isRead() ? this.#annexBTaker(reference) : undefined;
                    if (taker === undefined) continue;
                    const names = read.get(taker);
                    if (names === undefined) read.set(taker, new Set([reference.identifier.name]));
                    else names.add(reference.identifier.name);
                }
                this.#annexBRead = read;
            }
            return this.#annexBRead.get(target)?.has(variable.name) === true;
        });
    }

    /**
     * The variable `reference` names under static scoping; `undefined` through `with` or for a global, `false` for an
     * Annex B binding or a variable that stands for none.
     */
    #resolveStatically(reference: Reference): Variable | false | undefined {
        const name = reference.identifier.name;
        for (let scope: Scope | null = reference.from; scope !== null; scope = scope.upper) {
            if (scope.type === "with") return undefined;
            const variable = scope.set.get(name);
            if (variable !== undefined && resolves(scope, reference, variable)) return !this.#clauseVariables.has(variable) && variable;
            if (this.#annexBBindsIn(scope, name, reference.identifier as unknown as Node)) return false;
        }
        return undefined;
    }

    /** Like `variableOf`, but also resolves names eslint-scope left dynamic due to direct `eval`. `undefined` through `with`. */
    staticVariableOf(identifier: Node): Variable | undefined {
        const known = this.variableOf(identifier);
        if (known !== undefined) return known;
        const reference = this.#references.get(identifier);
        return reference === undefined ? undefined : this.#resolveStatically(reference) || undefined;
    }

    #staticReferences: Map<Variable, Reference[]> | undefined;
    #mergedReferences = new Map<Variable, readonly Reference[]>();

    /**
     * Every reference to `variable` under static scoping (see `staticVariableOf`), with no `with` check: callers
     * resolve names with `staticVariableOf` or have refused `with` themselves. Others use `references`. Includes
     * Annex B's writes of block functions into it, whose identifier is the declaration's name.
     */
    staticReferences(variable: Variable): readonly Reference[] {
        if (this.#staticReferences === undefined) {
            const added = new Map<Variable, Reference[]>();
            const add = (target: Variable, reference: Reference): void => {
                const list = added.get(target);
                if (list === undefined) added.set(target, [reference]);
                else list.push(reference);
            };
            for (const reference of this.manager.globalScope?.through ?? []) {
                const target = this.#resolveStatically(reference);
                if (target !== undefined && target !== false) add(target, reference);
            }
            for (const write of this.#annexBWrites.values()) if (write.resolved !== null) add(write.resolved, write);
            this.#staticReferences = added;
            this.#mergedReferences = new Map();
        }
        const merged = this.#mergedReferences.get(variable);
        if (merged !== undefined) return merged;
        const own = this.#annexBAny.has(variable.name) ? variable.references.filter((reference) => !this.#annexBTakes(reference)) : variable.references;
        const added = this.#staticReferences.get(variable);
        const references = added === undefined ? own : [...own, ...added];
        this.#mergedReferences.set(variable, references);
        return references;
    }

    #withScopes: Scope[] | undefined;

    /**
     * Whether a reference to `name` inside a `with` may be a property of its object instead of the binding `scope`
     * has (`null`: none, a global).
     */
    #withIntercepts(name: string, scope: Scope | null): boolean {
        this.#withScopes ??= this.manager.scopes.filter((candidate) => candidate.type === "with");
        return this.#withScopes.some((within) => {
            if (!within.through.some((reference) => reference.identifier.name === name)) return false;
            for (let current = within.upper; current !== null; current = current.upper) {
                if (current === scope) return true;
                if (current.set.has(name) || this.#annexBBindsIn(current, name, within.block as unknown as Node)) return false;
            }
            return scope === null;
        });
    }

    /**
     * Every reference to `variable` in the program's own code, statically resolved (model 2: code a direct `eval`
     * runs doesn't use the script's names), or `undefined` when a `with` may intercept one. Never read
     * `variable.references`: eslint-scope leaves every reference in a `dynamic` scope (around a direct `eval`)
     * unresolved, so that list misses uses there.
     */
    references(variable: Variable): readonly Reference[] | undefined {
        return this.#withIntercepts(variable.name, variable.scope) ? undefined : this.staticReferences(variable);
    }

    /** The scope `node` opens; with `inner`, a named function expression's own scope rather than the one holding its name. */
    scopeOf(node: Node, inner = false): Scope | null {
        return this.manager.acquire(asEstree(node), inner);
    }
}

/** Whether `scope` is `block`'s scope or one nested in it. */
export const scopeWithin = (scope: Scope | null, block: Node): boolean => {
    for (let current = scope; current !== null; current = current.upper) if ((current.block as unknown as Node) === block) return true;
    return false;
};
