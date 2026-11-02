import type { Expression, FunctionLike, Node, Statement } from "../../core/ast.js";
import { keyName, propertyKey } from "../../core/ast.js";
import type { JsValue } from "../../core/builtins.js";
import { ArrayObject, Bound, Closure, hasOwn, isCallable, isObject, Native, PlainObject, typeOf } from "../../core/builtins.js";
import type { Value } from "../../core/evaluate.js";
import { closureBinding, Interpreter } from "../../core/interpret.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { scopeWithin } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import { builderOf, parentsWithin, returnsOf } from "./builders.js";
import { FUNCTION_NAMES, hostBindings } from "./decoder-host.js";
import type { PropertyPath, RuntimeModel } from "./model.js";
import type { StorageMatcher } from "./storage.js";
import { rootStatements } from "./storage.js";

/** Steps for building a data holder (a cyclic array) on the host. */
const BUILD_STEPS = 20_000_000;
const READ_STEPS = 100_000;

/** A `G.k` built on the host, and the objects the functions it holds may reach through their builder's variables. */
interface Built {
    readonly value: JsValue;
    readonly interpreter: Interpreter;
    readonly captured: ReadonlySet<object>;
}

/** What the snapshot needs of the storage effects (`effects.ts`), which in turn asks it about values. */
export interface SnapshotEffects {
    readonly preludeWritesTo: (path: PropertyPath) => number;
    /** A write, escape or (unless not `withCalls`) call besides root statement `built`'s own write that may change an object at or under `prefix`. */
    readonly changedWithin: (prefix: PropertyPath, built: Node, harmless?: (callee: PropertyPath) => boolean, withCalls?: boolean) => Node | undefined;
    readonly escapedInPrelude: (path: PropertyPath) => Node | undefined;
    /** A prelude call, from root statement `from` on, that may change `path` through the `this` it hands a function. */
    readonly preludeCallChanging: (path: PropertyPath, from: number) => Node | undefined;
}

/**
 * What a property may hold, from the builder's code: a function (`node`: the one function object it is, if known;
 * `thisFree`: none it may be uses `this`, so a call handing it one changes nothing through it).
 */
type Possible =
    | { readonly kind: "function"; readonly node: Node | undefined; readonly thisFree: boolean }
    | { readonly kind: "primitive"; readonly value: Value }
    | { readonly kind: "object" }
    | { readonly kind: "unknown" };

const UNKNOWN: Possible = { kind: "unknown" };

/**
 * Whether `fn` may change something through its `this` (not counting nested non-arrow functions): it uses `this` other
 * than to read a property whose value it then doesn't write, call as a method or read below (`this.k` as a value).
 */
const changesThroughThis = (fn: Node): boolean => {
    let found = false;
    traverse(fn, {
        enter(path) {
            if (found || (path.node !== fn && (path.node.type === "FunctionExpression" || path.node.type === "FunctionDeclaration"))) path.skip();
        },
        ThisExpression(path) {
            const member = path.parentPath;
            const above = member?.parent;
            const read =
                member !== null &&
                member !== undefined &&
                member.node.type === "MemberExpression" &&
                path.key === "object" &&
                !member.isWriteTarget() &&
                !(above?.type === "MemberExpression" && member.key === "object") &&
                !((above?.type === "CallExpression" || above?.type === "NewExpression") && member.key === "callee") &&
                !(above?.type === "UnaryExpression" && above.operator === "delete");
            if (!read) found = true;
        },
    });
    return found;
};

/** The properties of the object a builder returns: what each may ever hold, as far as the builder's code goes. */
interface Holder {
    /** By name: the values written to it (the literal's first), and whether the literal's is the only one. */
    readonly properties: ReadonlyMap<string, { readonly values: readonly Possible[] }>;
    /** Why a name not in `properties` may be one anyway (the slot shape's other slots), if it may. */
    readonly open: string | undefined;
}

/** Own properties functions may have (`arguments` and `caller` in some engines). */
const FUNCTION_OWN: Readonly<Record<string, true>> = { length: true, name: true, prototype: true, arguments: true, caller: true };

/** Whether code in `fn` may write a property named `name` of anything: `x.name = ...`, a computed key, or `delete`. */
const writesMember = (fn: Node, name: string): boolean => {
    let found = false;
    traverse(fn, {
        AssignmentExpression(path) {
            const left = path.node.left;
            if (left.type === "MemberExpression" && (propertyKey(left) ?? name) === name) found = true;
        },
        UnaryExpression(path) {
            if (path.node.operator === "delete") found = true;
        },
    });
    return found;
};

/**
 * The storage object's values after the prelude, from the code that builds them: what each path holds, of
 * which type, and which function or object it is.
 *
 * A path's value comes from the one root statement `G.k = ...` assigning its first key, and from nothing else: no other
 * write and no call handing a part of it as `this` may change it, in the prelude or later (`changedWithin`, model 3).
 * Model 1 (callbacks run after the top level completed) puts that statement's value in place before any code reading
 * it afterwards runs.
 *
 * - Functions and objects of a root object literal `G.k = {...}`, or of the object a builder `G.k = (function () {...})()`
 *   returns, keep their identity: that object (the builder's object literal, or a local holding one, or the slot shape
 *   of `builderOf`) is reached only through `G.k` and, in its own code, through that local; what each property may
 *   hold is every value the code writes there (`holderOf`). Its functions change nothing through `this` (they only
 *   read its properties, if they use it), so calling them through `G.k` changes nothing there either.
 * - Other builders' values are built once on the host (`core/interpret.ts`): only `G.k`'s paths reach the objects
 *   afterwards, and the effects analysis follows those, but for what the functions among them reach through their
 *   builder's variables (those aren't read). Identity is the host object's.
 *
 * Model 7 (builtins intact): inherited members are the standard ones.
 */
export class Snapshot {
    readonly #runtime: RuntimeModel;
    readonly #matcher: StorageMatcher;
    readonly #scopes: ScopeInfo;
    readonly #effects: SnapshotEffects;
    readonly #definitions = new Map<string, { statement: Statement; right: Expression } | string>();
    readonly #holders = new Map<Node, Holder | string>();
    readonly #hosted = new Map<string, Built | string>();
    /** By `calls` and key: why something else may change what a hosted value holds, or `undefined`. */
    readonly #changed = new Map<string, string | undefined>();
    readonly #ids = new WeakMap<object, number>();
    #nextId = 0;
    /** Paths being worked out: the effects analysis may ask back about them (through a call's `this`). */
    readonly #pending = new Set<string>();

    constructor(runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, effects: SnapshotEffects) {
        this.#runtime = runtime;
        this.#matcher = matcher;
        this.#scopes = scopes;
        this.#effects = effects;
    }

    /** `typeof` the value at `path`, read through data properties only (reading it runs no code). */
    typeAt(path: PropertyPath): { readonly type: string } | string {
        const value = this.#guarded(JSON.stringify(path), () => this.#valueAt(path, true));
        if (typeof value === "string") return value;
        if ("host" in value) return { type: typeOf(value.host) };
        return {
            type:
                value.possible.kind === "function"
                    ? "function"
                    : value.possible.kind === "primitive"
                      ? value.possible.value === null
                          ? "object"
                          : typeof value.possible.value
                      : value.possible.kind === "object"
                        ? "object"
                        : "unknown",
        };
    }

    /** The function at `path`: the one function object a builder's code puts there. */
    functionAt(path: PropertyPath): Node | string {
        const value = this.#guarded(JSON.stringify(path), () => this.#valueAt(path, true));
        if (typeof value === "string") return value;
        if ("host" in value || value.possible.kind !== "function") return "it isn't a function the builder's code names";
        return value.possible.node ?? "the builder's code may put several functions there";
    }

    /** A key equal for equal values: objects by identity (`o:`), numbers (`n:`) and strings (`s:`) by value. */
    keyAt(path: PropertyPath): { readonly key: string } | string {
        const value = this.#guarded(JSON.stringify(path), () => this.#valueAt(path, true));
        if (typeof value === "string") return value;
        if ("host" in value) {
            const v = value.host;
            if (isObject(v)) return { key: `o:${this.#idOf(v)}` };
            return typeof v === "number" ? { key: `n:${String(v)}` } : typeof v === "string" ? { key: `s:${v}` } : `it holds ${String(v)}`;
        }
        const { possible } = value;
        if (possible.kind === "function" && possible.node !== undefined) return { key: `o:${this.#idOf(possible.node)}` };
        if (possible.kind === "primitive")
            return typeof possible.value === "number"
                ? { key: `n:${String(possible.value)}` }
                : typeof possible.value === "string"
                  ? { key: `s:${possible.value}` }
                  : `it holds ${String(possible.value)}`;
        return "its value isn't known";
    }

    /** `left op right` for an equality operator: two objects by identity, two primitives by value (no conversion of an object). */
    compare(left: PropertyPath, right: PropertyPath, op: string): boolean | string {
        if (op !== "===" && op !== "!==" && op !== "==" && op !== "!=") return "not an equality";
        const a = this.#comparable(left);
        const b = this.#comparable(right);
        if (typeof a === "string") return a;
        if (typeof b === "string") return b;
        if (isObject(a.value) !== isObject(b.value)) return "an object compared with a primitive converts it";
        // Primitives only convert among themselves: `==` runs no program code.
        const equal = op === "===" || op === "!==" ? a.value === b.value : a.value == b.value;
        return op === "===" || op === "==" ? equal : !equal;
    }

    /**
     * Whether calling what `path` holds hands its `this` to no code that uses it: the value isn't callable, or is a
     * function of the builder's code that doesn't use `this`. Prelude calls handing `this` on aren't asked about here,
     * as the effects analysis judges those calls by this answer: the first change any of them made would need a
     * function that uses `this` while every path still holds what its builder put there, and this says none does.
     */
    thisFreeAt(path: PropertyPath): boolean {
        const value = this.#guarded(`this ${JSON.stringify(path)}`, () => this.#valueAt(path, false));
        if (typeof value === "string") return false;
        if ("host" in value) return !(value.host instanceof Closure) || !changesThroughThis(value.host.node);
        const { possible } = value;
        if (possible.kind === "unknown") return false;
        return possible.kind !== "function" || possible.thisFree;
    }

    #guarded<T>(id: string, work: () => T | string): T | string {
        if (this.#pending.has(id)) return "it depends on itself";
        this.#pending.add(id);
        try {
            return work();
        } finally {
            this.#pending.delete(id);
        }
    }

    #idOf(value: object): number {
        let id = this.#ids.get(value);
        if (id === undefined) {
            id = this.#nextId++;
            this.#ids.set(value, id);
        }
        return id;
    }

    #comparable(path: PropertyPath): { value: JsValue } | string {
        const value = this.#guarded(JSON.stringify(path), () => this.#valueAt(path, true));
        if (typeof value === "string") return value;
        if ("host" in value) return { value: value.host };
        const { possible } = value;
        if (possible.kind === "primitive") return { value: possible.value };
        return "only data values are compared";
    }

    /** `G` itself, or `(X = G)`. */
    #storageObject(node: Node): boolean {
        if (this.#matcher.isStorage(node)) return true;
        return node.type === "AssignmentExpression" && node.operator === "=" && this.#matcher.isStorage(node.right);
    }

    /** The one root statement `G.k = ...`. */
    #definition(key: string): { statement: Statement; right: Expression } | string {
        const known = this.#definitions.get(key);
        if (known !== undefined) return known;
        const found: { statement: Statement; right: Expression }[] = [];
        for (const statement of rootStatements(this.#runtime.root)) {
            if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") continue;
            const left = statement.expression.left;
            if (left.type === "MemberExpression" && this.#storageObject(left.object) && propertyKey(left) === key) found.push({ statement, right: statement.expression.right });
        }
        const [only] = found;
        const definition = only !== undefined && found.length === 1 ? only : found.length === 0 ? "no root statement assigns it" : "several root statements assign it";
        this.#definitions.set(key, definition);
        return definition;
    }

    /** `calls`: also refuse where a prelude call may change the value through the `this` it hands a function. */
    #valueAt(path: PropertyPath, calls: boolean): { readonly possible: Possible } | { readonly host: JsValue } | string {
        const [key, ...rest] = path;
        const runtime = this.#runtime;
        if (key === undefined) return "the storage object itself";
        if (runtime.setupKeys.has(key) || runtime.callAliases.has(key)) return `${runtime.storage}.${key} is a property the setup defined`;
        const definition = this.#definition(key);
        if (typeof definition === "string") {
            if (rest.length > 0 || FUNCTION_NAMES.includes(key) || this.#effects.preludeWritesTo([key]) > 0) return definition;
            return { possible: { kind: "primitive", value: undefined } };
        }
        if (this.#effects.preludeWritesTo(path) !== 1) return `the prelude writes ${runtime.storage}.${path.join(".")} besides where it is made`;
        if (this.#effects.escapedInPrelude(path) !== undefined) return `the prelude hands ${runtime.storage}.${path.join(".")} or a part above it to a call`;
        if (calls && this.#effects.preludeCallChanging(path, 0) !== undefined) return `a prelude call may change ${runtime.storage}.${path.join(".")} through its this`;
        const { right, statement } = definition;
        const ast = this.#astValue(right, rest);
        return typeof ast === "string" ? this.#hostValue(key, rest, statement, right, ast, calls) : { possible: ast };
    }

    /** What the AST says `right`, then `rest` below it, holds. */
    #astValue(right: Expression, rest: readonly string[]): Possible | string {
        const builder = right.type === "CallExpression" && (right.callee.type === "FunctionExpression" || right.callee.type === "ArrowFunctionExpression") ? right.callee : undefined;
        const source = builder ?? (right.type === "ObjectExpression" ? right : undefined);
        if (rest.length === 0) {
            if (right.type === "Identifier") {
                const variable = this.#scopes.variableOf(right);
                const def = variable?.defs[0]?.node as Node | undefined;
                if (variable !== undefined && variable.defs.length === 1 && def?.type === "FunctionDeclaration" && rootStatements(this.#runtime.root).includes(def) && !this.#written(variable))
                    return { kind: "function", node: def, thisFree: !changesThroughThis(def) };
            }
            const possible = this.#possible(right, undefined);
            if (possible.kind !== "unknown") return possible;
            return builder !== undefined && typeof this.#holderOf(builder) !== "string" ? { kind: "object" } : "its value isn't one the analysis tells";
        }
        if (source === undefined) return "it isn't an object literal or built by an immediately invoked function";
        const holder = this.#holderOf(source);
        if (typeof holder === "string") return holder;
        const [name, ...deeper] = rest as [string, ...string[]];
        const property = holder.properties.get(name);
        if (property === undefined) {
            if (holder.open !== undefined) return holder.open;
            if (deeper.length > 0) return "it reads below an inherited property";
            // Inherited from Object.prototype (model 7).
            return name in Object.prototype ? { kind: "function", node: undefined, thisFree: false } : { kind: "primitive", value: undefined };
        }
        const [first, ...others] = property.values;
        if (first === undefined) return "nothing writes it";
        const kinds = new Set(property.values.map((value) => value.kind));
        if (kinds.size === 1 && first.kind === "function") {
            if (deeper.length === 0)
                return others.length === 0 ? first : { kind: "function", node: undefined, thisFree: property.values.every((value) => value.kind === "function" && value.thisFree) };
            const [member, ...below] = deeper as [string, ...string[]];
            if (below.length > 0 || FUNCTION_OWN[member] === true || writesMember(source, member)) return "it reads a property of a function";
            const inherited = (Function.prototype as unknown as Record<string, unknown>)[member];
            return member in Function.prototype
                ? typeof inherited === "function"
                    ? { kind: "function", node: undefined, thisFree: false }
                    : "it reads an inherited accessor"
                : { kind: "primitive", value: undefined };
        }
        // The literal's own value, nothing else writing it there.
        if (others.length === 0 && deeper.length === 0 && (first.kind === "primitive" || first.kind === "object")) return first;
        return "the builder's code may put other than a function there";
    }

    #written(variable: Variable): boolean {
        return this.#scopes.staticReferences(variable).some((reference) => reference.isWrite());
    }

    /** A function value `node` in builder `fn` stands for. */
    #possible(node: Node, fn: FunctionLike | undefined, depth = 0): Possible {
        switch (node.type) {
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return node.async || (node.type === "FunctionExpression" && node.generator) ? UNKNOWN : { kind: "function", node, thisFree: !changesThroughThis(node) };
            case "Literal":
                return "regex" in node || typeof node.value === "bigint" ? UNKNOWN : { kind: "primitive", value: node.value as Value };
            case "ObjectExpression":
            case "ArrayExpression":
                return { kind: "object" };
            case "Identifier": {
                if (fn === undefined) return UNKNOWN;
                const variable = this.#scopes.variableOf(node);
                const def = variable?.defs[0];
                if (variable === undefined || variable.defs.length !== 1 || def === undefined || !scopeWithin(variable.scope, fn as unknown as Node)) return UNKNOWN;
                const declared = def.node as unknown as Node;
                if (declared.type === "FunctionDeclaration") return this.#written(variable) ? UNKNOWN : { kind: "function", node: declared, thisFree: !changesThroughThis(declared) };
                if (declared.type === "VariableDeclarator" && (declared.init?.type === "FunctionExpression" || declared.init?.type === "ArrowFunctionExpression")) {
                    const writes = this.#scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length;
                    return writes === 1 ? this.#possible(declared.init, fn, depth) : UNKNOWN;
                }
                return UNKNOWN;
            }
            case "CallExpression": {
                const callee = node.callee;
                if (
                    depth > 3 ||
                    (callee.type !== "FunctionExpression" && callee.type !== "ArrowFunctionExpression") ||
                    callee.async ||
                    (callee.type === "FunctionExpression" && callee.generator) ||
                    callee.body === null
                )
                    return UNKNOWN;
                const body = callee.body;
                const results =
                    body.type === "BlockStatement"
                        ? returnsOf(callee).map((ret) => (ret.type === "ReturnStatement" && ret.argument !== null ? this.#possible(ret.argument, callee, depth + 1) : UNKNOWN))
                        : [this.#possible(body, callee, depth + 1)];
                // A fresh function each time it runs: the call itself runs once where it stands.
                if (results.length === 0 || !results.every((result) => result.kind === "function")) return UNKNOWN;
                return { kind: "function", node: results.length === 1 ? node : undefined, thisFree: results.every((result) => result.kind === "function" && result.thisFree) };
            }
            default:
                return UNKNOWN;
        }
    }

    /**
     * The object a root `G.k = {...}` stores, or the one builder `fn` returns, by property: an object literal it returns,
     * a local `var Q = {...}` it returns whose every other use is `Q.name` (read, called or written with `=`), or
     * `builderOf`'s slot shape. None of its functions may change anything through `this`.
     */
    #holderOf(source: FunctionLike | (Node & { type: "ObjectExpression" })): Holder | string {
        const known = this.#holders.get(source);
        if (known !== undefined) return known;
        const holder = this.#computeHolder(source);
        this.#holders.set(source, holder);
        return holder;
    }

    #computeHolder(source: FunctionLike | (Node & { type: "ObjectExpression" })): Holder | string {
        const fn = source.type === "ObjectExpression" ? undefined : source;
        const properties = new Map<string, { values: Possible[] }>();
        const add = (name: string, value: Possible): void => {
            const entry = properties.get(name) ?? { values: [] };
            entry.values.push(value);
            properties.set(name, entry);
        };
        const literal = (object: Node & { type: "ObjectExpression" }): string | undefined => {
            for (const property of object.properties) {
                if (property.type !== "Property" || property.kind !== "init" || property.computed) return "its literal has a computed, spread or accessor property";
                const name = keyName(property.key);
                if (name === undefined || name === "__proto__") return "its literal sets a prototype or an odd key";
                add(name, property.method ? { kind: "function", node: property.value, thisFree: !changesThroughThis(property.value) } : this.#possible(property.value, fn));
            }
            return undefined;
        };
        const thisFree = (): string | undefined => {
            for (const { values } of properties.values()) {
                for (const value of values) if (value.kind === "function" && !value.thisFree) return "one of its functions may change something through this";
            }
            return undefined;
        };
        if (fn === undefined) return literal(source as Node & { type: "ObjectExpression" }) ?? thisFree() ?? { properties, open: undefined };
        if (fn.async || (fn.type === "FunctionExpression" && fn.generator) || fn.body?.type !== "BlockStatement") return "the builder isn't a plain function with a body";
        const returns = returnsOf(fn);
        const [returned] = returns;
        if (returns.length !== 1 || returned?.type !== "ReturnStatement" || returned.argument === null) return "the builder doesn't end in one return of what it built";
        const result = returned.argument;
        let open: string | undefined;
        if (result.type === "ObjectExpression") {
            const problem = literal(result);
            if (problem !== undefined) return problem;
        } else if (result.type === "Identifier") {
            const variable = this.#scopes.variableOf(result);
            const def = variable?.defs[0];
            const declarator = def?.node as unknown as Node | undefined;
            if (
                variable === undefined ||
                variable.defs.length !== 1 ||
                !scopeWithin(variable.scope, fn as unknown as Node) ||
                declarator?.type !== "VariableDeclarator" ||
                declarator.init?.type !== "ObjectExpression"
            )
                return "the builder doesn't return an object literal or a local holding one";
            const problem = literal(declarator.init);
            if (problem !== undefined) return problem;
            const references = this.#scopes.references(variable);
            if (references === undefined) return "its holder's uses can't be told";
            const parents = parentsWithin(fn as unknown as Node);
            for (const reference of references) {
                const identifier = reference.identifier as unknown as Node;
                if (reference.init === true || identifier === result) continue;
                const member = parents.get(identifier);
                if (member?.type !== "MemberExpression" || member.object !== identifier) return `its holder ${variable.name} is handed on`;
                const name = propertyKey(member);
                const above = parents.get(member);
                const written = above?.type === "AssignmentExpression" && above.left === member;
                if (above?.type === "UpdateExpression" || (above?.type === "UnaryExpression" && above.operator === "delete") || (written && above.operator !== "="))
                    return `its holder ${variable.name} has a property updated or deleted`;
                if (name === undefined) {
                    if (written) return `a computed write to its holder ${variable.name} may set any property`;
                    continue;
                }
                if (!written) continue;
                // Code making the write may run any number of times: a function it writes is no one object.
                const value = this.#possible(above.right, fn);
                add(name, value.kind === "function" ? { kind: "function", node: undefined, thisFree: value.thisFree } : value);
            }
        } else {
            const slots = fn.type === "FunctionExpression" ? builderOf(fn, this.#scopes) : "an arrow builder";
            if (typeof slots === "string") return slots;
            for (const [name, method] of slots.methods) add(name, { kind: "function", node: method, thisFree: !changesThroughThis(method) });
            for (const [name, closure] of slots.closures) add(name, { kind: "function", node: closure.fn, thisFree: !changesThroughThis(closure.fn) });
            open = "the builder's slot holder may have other properties";
        }
        return thisFree() ?? { properties, open };
    }

    /** A data holder built on the host; `rest` read below it (inherited members by the builtins themselves, model 7). */
    #hostValue(key: string, rest: readonly string[], statement: Statement, right: Expression, ast: string, calls: boolean): { readonly host: JsValue } | { readonly possible: Possible } | string {
        let built = this.#hosted.get(key);
        if (built === undefined) {
            built = this.#build(statement, right);
            this.#hosted.set(key, built);
        }
        if (typeof built === "string") return `${ast}; on the host: ${built}`;
        const id = `${calls} ${key}`;
        let changed = this.#changed.get(id);
        if (!this.#changed.has(id)) {
            this.#changed.set(id, "its value depends on itself");
            changed = this.#changedHost(key, statement, built, calls);
            this.#changed.set(id, changed);
        }
        if (changed !== undefined) return `${ast}; on the host: ${changed}`;
        let value = built.value;
        for (const [i, name] of rest.entries()) {
            if (isObject(value) && built.captured.has(value)) return "a function its builder made may change it";
            if (!(value instanceof ArrayObject || value instanceof PlainObject)) return "it reads below a value that isn't an array or a plain object";
            if (!hasOwn(value, name)) {
                if (i < rest.length - 1) return "it reads below an inherited property";
                const prototype: object = value instanceof ArrayObject ? Array.prototype : Object.prototype;
                if (!(name in prototype)) return { host: undefined };
                return typeof (prototype as Record<string, unknown>)[name] === "function" ? { possible: { kind: "function", node: undefined, thisFree: false } } : "it reads an inherited accessor";
            }
            const read = built.interpreter.member(value, name, READ_STEPS);
            if (!read.ok) return `reading it on the host refused: ${read.reason}`;
            value = read.value;
        }
        if (isObject(value) && built.captured.has(value)) return "a function its builder made may change it";
        return { host: value };
    }

    /**
     * Builds `G.k`'s value on the host: arrays, plain objects, primitives and functions of the builder's code (no
     * builtin). Afterwards only `G.k`'s paths reach its objects, but for what those functions' code may reach through
     * the variables of the builder they use (`captured`, refused where read); what they do through `this` is the
     * effects analysis's (it follows calls of `G.k`'s paths, `thisFreeAt`).
     */
    #build(statement: Statement, right: Expression): Built | string {
        const bindings = hostBindings({ runtime: this.#runtime, matcher: this.#matcher, scopes: this.#scopes }, statement);
        if (typeof bindings === "string") return bindings;
        const interpreter = new Interpreter({ outer: bindings.outer, aliases: bindings.aliases });
        const built = interpreter.evaluate(right, BUILD_STEPS);
        if (!built.ok) return `building it refused: ${built.reason}`;
        const seen = new Set<object>();
        const captured = new Set<object>();
        // Objects reachable from `start`, also through the variables the functions among them use: into `into`.
        const walk = (start: JsValue, into: Set<object>): string | undefined => {
            const work: JsValue[] = [start];
            while (work.length > 0) {
                const value = work.pop() as JsValue;
                if (!isObject(value) || into.has(value)) continue;
                into.add(value);
                if (value instanceof Bound || value instanceof Native) return "it holds a builtin or a bound function";
                if (value instanceof ArrayObject) for (const item of value.items) work.push(item);
                else if (value instanceof PlainObject) for (const item of value.props.values()) work.push(item);
                else if (value instanceof Closure) {
                    if (value.node.type === "ArrowFunctionExpression" && changesThroughThis(value.node)) return "a function it makes may change something through the this it closes over";
                    for (const name of this.#outerNames(value.node, right)) {
                        const bound = closureBinding(value, name);
                        if (bound === undefined) continue;
                        const problem = walk(bound.value, captured);
                        if (problem !== undefined) return problem;
                    }
                }
            }
            return undefined;
        };
        const problem = walk(built.value, seen);
        return problem ?? { value: built.value, interpreter, captured };
    }

    /** Names `fn`'s code uses of variables `within` declares outside `fn`. */
    #outerNames(fn: FunctionLike, within: Node): string[] {
        const names = new Set<string>();
        traverse(fn as unknown as Node, {
            Identifier: (path) => {
                const variable = this.#scopes.variableOf(path.node);
                if (variable !== undefined && scopeWithin(variable.scope, within) && !scopeWithin(variable.scope, fn as unknown as Node)) names.add(variable.name);
            },
        });
        return [...names];
    }

    /**
     * Why something besides its builder may change a hosted `G.k`, if it may: nothing reaching it through `G.k`'s paths
     * may (`changedWithin`; calls only when `calls`, as in `#valueAt`). A call of a path under `G.k` changes nothing
     * when what it calls is an own property holding data (calling it throws) or nothing the builtin prototypes have
     * (model 7): no other change makes it callable.
     */
    #changedHost(key: string, statement: Statement, built: Built, calls: boolean): string | undefined {
        const { interpreter } = built;
        const harmless = (callee: PropertyPath): boolean => {
            let parent = built.value;
            for (const [i, name] of callee.entries()) {
                if (i === 0) continue;
                if (!(parent instanceof ArrayObject || parent instanceof PlainObject)) return false;
                if (!hasOwn(parent, name)) return i === callee.length - 1 && !(name in (parent instanceof ArrayObject ? Array.prototype : Object.prototype));
                const read = interpreter.member(parent, name, READ_STEPS);
                if (!read.ok) return false;
                parent = read.value;
            }
            return !isCallable(parent);
        };
        return this.#effects.changedWithin([key], statement, harmless, calls) === undefined ? undefined : "something else may change what it holds";
    }
}
