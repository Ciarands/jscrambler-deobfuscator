import type { MemberExpression, Node } from "../../core/ast.js";
import { isFunctionNode, propertyKey } from "../../core/ast.js";
import type { PassLog } from "../../core/log.js";
import type { Reference, Scope, ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import { builderOf, returnsOf } from "./builders.js";
import type { PropertyPath } from "./guest.js";
import type { RuntimeModel } from "./model.js";
import type { StorageMatcher } from "./storage.js";
import { rootStatements, storageMatcher } from "./storage.js";

/**
 * When code runs, measured against the prelude (the root's statements, which the guest ran in order):
 * - `prelude`: only while the prelude runs, during root statements `first` to `last`. `reflected` when the snapshot
 *   holds its effects (every statement it runs in finished in the guest).
 * - `later`: at any time after the prelude (inside a function that may be called later).
 * - `never`: not at all (a function nothing refers to).
 */
type Timing = { readonly kind: "prelude"; readonly reflected: boolean; readonly first: number; readonly last: number } | { readonly kind: "later" } | { readonly kind: "never" };

const LATER: Timing = { kind: "later" };
const NEVER: Timing = { kind: "never" };

/**
 * Whether the function at `path` is invoked right where it is written (`(function () {...})()`, also through
 * `.call`/`.apply` or `new`), as a plain function (not async or generator, whose bodies run later), and can't get hold
 * of itself to run again (it doesn't use its own name).
 */
const invokedInPlace = (path: Path): boolean => {
    const fn = path.node;
    if (fn.type !== "FunctionExpression" && fn.type !== "ArrowFunctionExpression") return false;
    if (fn.async || (fn.type === "FunctionExpression" && fn.generator)) return false;
    const parent = path.parent;
    const invoked =
        ((parent?.type === "CallExpression" || parent?.type === "NewExpression") && path.key === "callee") ||
        (parent?.type === "MemberExpression" &&
            path.key === "object" &&
            (propertyKey(parent) === "call" || propertyKey(parent) === "apply") &&
            path.parentPath?.parent?.type === "CallExpression" &&
            path.parentPath.key === "callee");
    if (!invoked) return false;
    const name = fn.type === "FunctionExpression" ? fn.id?.name : undefined;
    if (name === undefined) return true;
    let named = false;
    traverse(fn.body as Node, {
        enter(inner) {
            if (named) inner.skip();
        },
        Identifier(inner) {
            if (inner.node.name === name) named = true;
        },
    });
    return !named;
};

/** Whether a function's own body (not nested non-arrow functions) uses `this`. */
const usesThis = (fn: Node): boolean => {
    let found = false;
    traverse(fn, {
        enter(path) {
            if (found || (path.node !== fn && isFunctionNode(path.node) && path.node.type !== "ArrowFunctionExpression")) path.skip();
        },
        ThisExpression() {
            found = true;
        },
    });
    return found;
};

/** The function a scope belongs to (`undefined` for code at the root's top level), or `null` when it can't be told. */
const enclosingFunction = (scope: Scope | null, root: Node): Node | undefined | null => {
    for (let s = scope; s !== null; s = s.upper) {
        if (s.type === "function") return (s.block as unknown as Node) === root ? undefined : (s.block as unknown as Node);
        if (s.type === "global" || s.type === "module") return undefined;
        if (s.type === "class-field-initializer" || s.type === "class-static-block") return null;
    }
    return undefined;
};

/** A path on the storage object as code reaches it: `undefined` stands for a key computed at run time. */
type KeyPattern = readonly (string | undefined)[];

/**
 * Something the program does to the storage object that the prelude's snapshot may not show:
 * - `write`: assigns (or deletes, increments...) the value at `keys`;
 * - `escape`: hands the object at `keys` to code this analysis doesn't follow (an argument, a stored value, the
 *   `this` of a call), which may then write any property below it.
 */
interface StorageEffect {
    readonly kind: "write" | "escape";
    readonly keys: KeyPattern;
    readonly node: Node;
    /** How it happens, for the log: the parent slot the value goes into, the call it is `this` of... */
    readonly via: string;
    /** For a write by `=`, the value put down. */
    readonly value?: Node | undefined;
    /** For code directly in a root statement the guest didn't finish: the statement's index. */
    readonly statement?: number | undefined;
}

/**
 * What calling a value could do with its `this`: `inert` (not callable: a primitive, an object or array literal),
 * `this-free` (a function whose own body has no `this`), `unknown`.
 */
type ValueKind = "inert" | "this-free" | "unknown";

const worst = (kinds: readonly ValueKind[]): ValueKind => (kinds.includes("unknown") ? "unknown" : kinds.includes("this-free") ? "this-free" : "inert");

/** The kind of a value expression. An immediately invoked function's is that of what it returns (`undefined` at its end). */
const valueKind = (value: Node, depth = 0): ValueKind => {
    switch (value.type) {
        case "Literal":
        case "TemplateLiteral":
        case "ObjectExpression":
        case "ArrayExpression":
        case "UnaryExpression":
        case "BinaryExpression":
        case "UpdateExpression":
            return "inert";
        case "FunctionExpression":
        case "ArrowFunctionExpression":
            return usesThis(value) ? "unknown" : "this-free";
        case "Identifier":
            return value.name === "undefined" ? "inert" : "unknown";
        case "ConditionalExpression":
            return worst([valueKind(value.consequent, depth), valueKind(value.alternate, depth)]);
        case "LogicalExpression":
            return worst([valueKind(value.left, depth), valueKind(value.right, depth)]);
        case "SequenceExpression":
            return valueKind(value.expressions.at(-1) as Node, depth);
        case "CallExpression": {
            const fn = value.callee;
            if (depth > 2 || (fn.type !== "FunctionExpression" && fn.type !== "ArrowFunctionExpression") || fn.async || (fn.type === "FunctionExpression" && fn.generator)) return "unknown";
            if (fn.body === null) return "unknown";
            if (fn.body.type !== "BlockStatement") return valueKind(fn.body, depth + 1);
            const kinds: ("inert" | "this-free" | "unknown")[] = [];
            traverse(fn.body, {
                enter(path) {
                    if (isFunctionNode(path.node)) path.skip();
                },
                ReturnStatement(path) {
                    kinds.push(path.node.argument === null ? "inert" : valueKind(path.node.argument, depth + 1));
                },
            });
            return worst(kinds);
        }
        default:
            return "unknown";
    }
};

/**
 * An object the expression creates right there and no binding holds: an object literal of data properties, or what an
 * immediately invoked function returns as one. Code can then only get hold of it through where it is put.
 */
const isFreshObject = (value: Node): boolean => {
    if (value.type === "ObjectExpression") return value.properties.every((property) => property.type === "Property" && property.kind === "init");
    if (value.type !== "CallExpression" || value.callee.type !== "FunctionExpression" || value.arguments.length > 0 || value.callee.async || value.callee.generator) return false;
    const returns = returnsOf(value.callee);
    const [only] = returns;
    return returns.length === 1 && only?.type === "ReturnStatement" && only.argument !== null && isFreshObject(only.argument);
};

/** Why a read may not see the snapshot's value, and the node to blame. */
export interface Staleness {
    readonly reason: string;
    readonly node: Node;
}

export interface StorageEffects {
    /**
     * Why the value at `path`, read through `site` (the reference to `G` the read starts from), may differ from what
     * the prelude's snapshot holds; `undefined` when it can't. `writesOnly` leaves out objects handed to calls as
     * `this` (for a wrapper's target: the runtime's own calls, like the decoder swapping its accessor when it
     * freezes, are what the guest runs too). `built`, a root statement storing the value at `path`: the value is the
     * one it stores, whether or not the guest finished it, so its own writes (those directly in it, done before the
     * read) don't count and the read must start after it.
     */
    readonly staleAt: (site: Node, path: PropertyPath, writesOnly?: boolean, built?: Node) => Staleness | undefined;
    /** Whether the code `site` (a reference to `G`) sits in runs only after the prelude (or never), not as part of it. */
    readonly runsAfterPrelude: (site: Node) => boolean;
    /** Whether the code `site` (a reference to `G`) sits in runs only in the prelude and is done before root statement `statement` starts (or never runs). */
    readonly runsBefore: (site: Node, statement: Node) => boolean;
    /** The last root statement the code `site` (a reference to `G`) may run in while the prelude runs; undefined if it runs only later, never, or wasn't analysed. */
    readonly lastPreludeStatement: (site: Node) => Node | undefined;
    /** Whether the code `site` (a reference to `G`) sits in runs only once root statement `statement` is done: in a later root statement, after the prelude, or never. */
    readonly runsAfter: (site: Node, statement: Node) => boolean;
    /**
     * Whether `node`, a use of `G` as a value, only stores it as a global property (`G[g].P = G`) that the program never
     * names again: no code of this script reaches `G` through it, and other scripts don't read it (model 2).
     */
    readonly keptAsGlobal: (node: Node) => boolean;
    /**
     * Whether code can reach the object the snapshot holds at `path` only through `G`'s paths, so that model 3 covers
     * every change to it: `G` itself, or an object the prelude put there with its one write to the path (or a prefix)
     * and created right there, unheld by any binding (no closure of the runtime keeps it, as the decoder keeps the
     * holder it swaps its accessor on).
     */
    readonly reachedOnlyThroughStorage: (path: PropertyPath) => boolean;
    /** How many writes by prelude code the snapshot holds that set the value at `path`: writes to it or to a prefix. */
    readonly preludeWritesTo: (path: PropertyPath) => number;
    /**
     * Whether the code directly inside `fn` (a function of the root; `undefined` for the root's top level) runs only
     * while the prelude runs, or never: never after it.
     */
    readonly runsOnlyInPrelude: (fn: Node | undefined) => boolean;
}

const matches = (pattern: KeyPattern, path: PropertyPath): boolean => {
    for (const [i, key] of pattern.entries()) if (key !== undefined && key !== path[i]) return false;
    return true;
};

/** Whether `effect` can change the value at `path`: a write to it or a prefix, an escape of a proper prefix. */
const affects = (effect: StorageEffect, path: PropertyPath): boolean => (effect.kind === "write" ? effect.keys.length <= path.length : effect.keys.length < path.length) && matches(effect.keys, path);

const describe = (storage: string, keys: KeyPattern): string => storage + keys.map((k) => (k === undefined ? "[?]" : `[${JSON.stringify(k)}]`)).join("");

/**
 * When each function of the root runs. Code runs during the prelude when it is a root statement's top-level code, the
 * body of a function invoked in place there, or the body of a prelude-only function: one whose every use is a direct
 * call from prelude code (or from itself). The last is a least fixpoint over the call graph. A function nothing refers
 * to never runs. The script is taken to be closed: other scripts don't call its functions (top-level ones included).
 * A program that mentions `.callee` or `.caller` can reach functions without naming them: then nothing is taken to
 * run only during the prelude.
 */
const timeline = (runtime: RuntimeModel, scopes: ScopeInfo, log: PassLog): ((fn: Node) => Timing) => {
    const statements = rootStatements(runtime.root);
    const parentOf = new Map<Node, { fn: Node | undefined; index: number; inPlace: boolean }>();
    const topLevelIndex = new Map<Node, number>();
    const directCallees = new Set<Node>();
    const candidates: { fn: Node; references: readonly Reference[] }[] = [];
    let reflective = false;
    /**
     * A function bound once, by its definition alone (a declaration has no write reference, `var f = function` the
     * one of its initializer), with the references to its binding.
     */
    const candidate = (fn: Node, id: Node): void => {
        const variable = scopes.staticVariableOf(id);
        if (variable === undefined || variable.defs.length !== 1) return;
        const references = scopes.staticReferences(variable);
        const definitionWrites = fn.type === "FunctionDeclaration" ? 0 : 1;
        if (references.filter((reference) => reference.isWrite()).length === definitionWrites) candidates.push({ fn, references });
    };

    for (const [index, statement] of statements.entries()) {
        const stack: Node[] = [];
        traverse(statement, {
            enter(path) {
                const node = path.node;
                if (!isFunctionNode(node)) return;
                parentOf.set(node, { fn: stack.at(-1), index, inPlace: invokedInPlace(path) });
                stack.push(node);
                if (node.type === "FunctionDeclaration" && node.id !== null) candidate(node, node.id);
            },
            exit(path) {
                if (stack.at(-1) === path.node) stack.pop();
            },
            VariableDeclarator(path) {
                const { id, init } = path.node;
                if (id.type === "Identifier" && (init?.type === "FunctionExpression" || init?.type === "ArrowFunctionExpression")) candidate(init, id);
            },
            Identifier(path) {
                const node = path.node;
                if (stack.length === 0) topLevelIndex.set(node, index);
                if (path.parent?.type === "CallExpression" && path.key === "callee") directCallees.add(node);
                if ((node.name === "callee" || node.name === "caller") && path.parent?.type === "MemberExpression" && path.key === "property") reflective = true;
            },
            Literal(path) {
                if (path.node.value === "callee" || path.node.value === "caller") reflective = true;
            },
        });
    }

    const preludeOnly = new Map<Node, Timing>();
    const memo = new Map<Node, Timing>();

    /** When code directly inside `fn` (or at the top level of root statement `index`, for `undefined`) runs. */
    const contextTiming = (fn: Node | undefined, index: number): Timing => {
        if (fn === undefined) {
            const statement = statements[index];
            return { kind: "prelude", reflected: statement !== undefined && runtime.executed.has(statement), first: index, last: index };
        }
        return timingOf(fn);
    };
    const timingOf = (fn: Node): Timing => {
        const known = memo.get(fn) ?? preludeOnly.get(fn);
        if (known !== undefined) return known;
        const info = parentOf.get(fn);
        if (info === undefined || reflective) return LATER;
        return info.inPlace ? contextTiming(info.fn, info.index) : LATER;
    };
    /** Whether `inner` is `fn` or nested in it. */
    const within = (inner: Node | undefined, fn: Node): boolean => {
        for (let current = inner; current !== undefined; current = parentOf.get(current)?.fn) if (current === fn) return true;
        return false;
    };

    if (!reflective) {
        for (const { fn, references } of candidates) {
            if (references.some((reference) => !reference.isWrite())) continue;
            memo.set(fn, NEVER);
            log.debug("never runs: nothing refers to it", fn);
        }
        // Least fixpoint: a function joins once every call to it comes from code already known to run in the prelude.
        for (let changed = true; changed;) {
            changed = false;
            for (const { fn, references } of candidates) {
                if (memo.has(fn) || preludeOnly.has(fn)) continue;
                let first = Number.POSITIVE_INFINITY;
                let last = -1;
                let only = true;
                for (const reference of references) {
                    if (reference.isWrite()) continue;
                    const identifier = reference.identifier as unknown as Node;
                    const caller = enclosingFunction(reference.from, runtime.root);
                    if (!directCallees.has(identifier) || caller === null) {
                        only = false;
                        break;
                    }
                    if (within(caller, fn)) continue; // a call from inside itself: only while it runs anyway
                    const index = caller === undefined ? topLevelIndex.get(identifier) : parentOf.get(caller)?.index;
                    const timing = index === undefined ? LATER : contextTiming(caller, index);
                    if (timing.kind !== "prelude" || !timing.reflected) {
                        only = false;
                        break;
                    }
                    first = Math.min(first, timing.first);
                    last = Math.max(last, timing.last);
                }
                if (only && last >= 0) {
                    preludeOnly.set(fn, { kind: "prelude", reflected: true, first, last });
                    log.debug(`runs only during the prelude: every call comes from it (root statements ${first} to ${last})`, fn);
                    changed = true;
                }
            }
        }
    }
    return (fn) => {
        let timing = memo.get(fn);
        if (timing === undefined) {
            timing = timingOf(fn);
            memo.set(fn, timing);
        }
        return timing;
    };
};

/**
 * Everything the program does to the storage object `G` that the prelude's snapshot may not show, found in one walk
 * over the root's statements. `G` changes only through code that names its paths: `G` itself, other names for it
 * (aliases, IIFE parameters), locals bound to a static part of it (`var t = G.a`), `this` inside functions called as
 * methods of `G` paths, and the global name the prelude may keep it under (`G[g].P = G`; counted as soon as the
 * program names `P` again). Each such reference is followed up its member chain (`G.a[k].b`) to what the code does:
 * write it, call it (the object it was read from becomes the callee's `this`), or read and hand on the value.
 *
 * What prelude code does is in the snapshot when the guest finished the statements it runs in; anything else may
 * happen later. Model assumptions, beyond the snapshot's own (app code runs after the prelude):
 * - a reference to a part of `G` obtained otherwise (a call's result, an argument, a computed read held in a local)
 *   isn't used to change `G` after the prelude;
 * - operators only read: the runtime's objects don't override `valueOf`/`toString`.
 *
 * A call `G.a.m()` is harmless when `G.a.m` is known not to use `this`: a call alias or another getter the setup
 * installed, a wrapper (whose target is then applied to the wrapper's receiver: that object gets used as `this`
 * instead), a function whose body has no `this`, or no function at all in the snapshot.
 *
 * `keyOf` gives computed keys a value where the caller knows it (`G[G.w(147)]` with the decoder call resolved).
 */
export const storageEffects = (runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, log: PassLog, keyOf?: (property: Node) => string | undefined): StorageEffects => {
    const statements = rootStatements(runtime.root);
    const timingOf = timeline(runtime, scopes, log);
    const later: StorageEffect[] = [];
    const preludeWrites: { keys: KeyPattern; last: number }[] = [];
    /** When each reference to `G` runs. */
    const sites = new Map<Node, Timing>();
    /** Functions prelude code assigned to storage paths, and how many prelude writes each path has, by path. */
    const assignedFunctions = new Map<string, Node>();
    const preludeWriteCount = new Map<string, number>();
    /** Paths a prelude write put a fresh object at (see `isFreshObject`). */
    const freshObjects = new Set<string>();
    const calls: { callee: KeyPattern; node: Node; timing: Timing }[] = [];
    /** `G[g].P = G`, with `G[g]` the global object: `G` kept as global `P`. */
    const globalStores: { name: string; key: Node; node: Node }[] = [];

    /** `G[g].P` (or `globalThis.P`, as global-proxy rewrites it) as a store target: the global property `P`, and the node naming it. */
    const globalProperty = (target: Node): { name: string; key: Node } | undefined => {
        if (target.type !== "MemberExpression") return undefined;
        const owner = target.object;
        const slot = owner.type === "MemberExpression" && matcher.isStorage(owner.object) ? propertyKey(owner) : undefined;
        const isGlobalObject = (slot !== undefined && runtime.globalKeys.has(slot)) || (owner.type === "Identifier" && owner.name === "globalThis" && scopes.isGlobalReference(owner));
        const name = propertyKey(target);
        return isGlobalObject && name !== undefined ? { name, key: target.property } : undefined;
    };
    const keyOfMember = (member: MemberExpression): string | undefined => propertyKey(member) ?? (member.computed && keyOf !== undefined ? keyOf(member.property) : undefined);
    /** `target = G`: kept as a global property, which the program may reach again by that name. */
    const storeInto = (target: Node, keys: KeyPattern, value: Node): void => {
        const store = keys.length === 0 ? globalProperty(target) : undefined;
        if (store !== undefined) globalStores.push({ ...store, node: value });
    };

    // Locals bound to a static part of G, once and only by their initializer (`var t = G.a[1]`): writes through them
    // are writes to that path.
    const parts = new Map<Variable, KeyPattern>();
    /** The storage path an expression reads, when it is `G`, an alias of it or a part local, plus static keys. */
    const pathOf = (node: Node): KeyPattern | undefined => {
        if (node.type === "MemberExpression") {
            const base = pathOf(node.object);
            const key = keyOfMember(node);
            return base === undefined || key === undefined ? undefined : [...base, key];
        }
        if (node.type !== "Identifier") return undefined;
        if (matcher.isStorage(node)) return [];
        const variable = scopes.staticVariableOf(node);
        return variable === undefined ? undefined : parts.get(variable);
    };
    for (const statement of statements) {
        traverse(statement, {
            VariableDeclarator(path) {
                const { id, init } = path.node;
                if (id.type !== "Identifier" || init?.type !== "MemberExpression") return;
                const keys = pathOf(init);
                const variable = keys === undefined ? undefined : scopes.staticVariableOf(id);
                if (keys === undefined || variable === undefined || variable.defs.length !== 1) return;
                if (scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length === 1) parts.set(variable, keys);
            },
        });
    }
    const partOf = (node: Node): KeyPattern | undefined => {
        const variable = node.type === "Identifier" ? scopes.staticVariableOf(node) : undefined;
        return variable === undefined ? undefined : parts.get(variable);
    };

    for (const [index, statement] of statements.entries()) {
        const top: Timing = { kind: "prelude", reflected: runtime.executed.has(statement), first: index, last: index };
        const timings: Timing[] = [top];
        const record = (kind: StorageEffect["kind"], keys: KeyPattern, node: Node, via: string, value?: Node): void => {
            const timing = timings.at(-1) as Timing;
            if (timing.kind === "never") return;
            if (timing.kind === "prelude" && timing.reflected) {
                // Prelude code: a write is in the snapshot; a reference it hands out is taken not to be used later.
                if (kind !== "write") return;
                preludeWrites.push({ keys, last: timing.last });
                const id = keys.every((k) => k !== undefined) ? JSON.stringify(keys) : undefined;
                if (id !== undefined) preludeWriteCount.set(id, (preludeWriteCount.get(id) ?? 0) + 1);
                return;
            }
            const when = timing.kind === "later" ? "in code that may run later" : `in prelude code the guest didn't finish (root statements ${timing.first} to ${timing.last})`;
            later.push({ kind, keys, node, via: `${via}, ${when}`, value, statement: timing.kind === "prelude" ? timing.first : undefined });
        };
        traverse(statement, {
            enter(path) {
                if (isFunctionNode(path.node)) {
                    const outer = timings.at(-1) as Timing;
                    timings.push(outer.kind !== "prelude" ? outer : timingOf(path.node));
                }
            },
            exit(path) {
                if (isFunctionNode(path.node)) timings.pop();
            },
            Identifier(path) {
                const node = path.node;
                const base = matcher.isStorage(node) ? [] : partOf(node);
                if (base === undefined) return;
                // Declarations of G itself (hoisted `function G() {}`), of another name for it or of a part local.
                if (matcher.isAliasBinding(node) || (path.parent?.type === "FunctionDeclaration" && path.key === "id")) return;
                const declared = scopes.staticVariableOf(node);
                if (declared !== undefined && parts.has(declared) && declared.identifiers.includes(node as never)) return;
                const timing = timings.at(-1) as Timing;
                if (base.length === 0) sites.set(node, timing);
                // Follow the member chain outwards: `G` -> `G.a` -> `G.a[k]`, also through what passes a value on: an
                // assignment's value (`(X = G).k`), `||`/`&&`/`??` operands, `?:` branches and a sequence's last element
                // (`(G || x).k`: taken as G's, the careful reading).
                let outer: Path = path;
                const keys: (string | undefined)[] = [...base];
                for (;;) {
                    while (outer.parent?.type === "MemberExpression" && outer.key === "object" && outer.parentPath !== null) {
                        keys.push(keyOfMember(outer.parent as MemberExpression));
                        outer = outer.parentPath;
                    }
                    const through = outer.parentPath;
                    if (through === null) break;
                    const passing = through.node;
                    if (passing.type === "AssignmentExpression" && passing.operator === "=" && outer.key === "right" && through.parent?.type === "MemberExpression" && through.key === "object") {
                        storeInto(passing.left, keys, outer.node);
                    } else if (!(
                        passing.type === "LogicalExpression" ||
                        (passing.type === "ConditionalExpression" && outer.key !== "test") ||
                        (passing.type === "SequenceExpression" && passing.expressions.at(-1) === outer.node)
                    )) {
                        break;
                    }
                    outer = through;
                }
                const parent = outer.parent;
                if (outer.isWriteTarget()) {
                    const value = parent?.type === "AssignmentExpression" && parent.operator === "=" ? parent.right : undefined;
                    record("write", keys, outer.node, `as the target of ${parent?.type ?? "a write"}`, value);
                    const preludeKeys = timing.kind === "prelude" && timing.reflected && keys.every((k) => k !== undefined) ? (keys as string[]) : undefined;
                    if (value !== undefined && preludeKeys !== undefined && isFunctionNode(value)) assignedFunctions.set(JSON.stringify(preludeKeys), value);
                    if (value !== undefined && preludeKeys !== undefined && isFreshObject(value)) freshObjects.add(JSON.stringify(preludeKeys));
                    // `G.k = (function () { ...; return holder; })()`: the holder's methods are functions the prelude put at `G.k.m`.
                    if (value?.type === "CallExpression" && value.callee.type === "FunctionExpression" && value.arguments.length === 0 && preludeKeys !== undefined) {
                        const builder = builderOf(value.callee, scopes);
                        if (typeof builder !== "string") {
                            const built = [...builder.methods, ...[...builder.closures].map(([name, { fn }]) => [name, fn] as const)];
                            for (const [name, method] of built) {
                                const id = JSON.stringify([...preludeKeys, name]);
                                assignedFunctions.set(id, method);
                                preludeWriteCount.set(id, (preludeWriteCount.get(id) ?? 0) + 1);
                            }
                        }
                    }
                } else if (parent?.type === "VariableDeclarator" && outer.key === "id") {
                    record("write", keys, outer.node, "declared");
                } else if (parent?.type === "CallExpression" && outer.key === "callee" && keys.length > 0) {
                    calls.push({ callee: keys, node: outer.node, timing });
                } else if (parent?.type === "AssignmentExpression" && outer.key === "right") {
                    storeInto(parent.left, keys, outer.node);
                }
                // Anything else reads the value or hands it on; what is done with it elsewhere is taken not to change G.
            },
        });
    }

    // Calls: the callee gets the object it was read from as `this`, unless it is known not to use it.
    const writes = later.filter((effect) => effect.kind === "write");
    type Verdict = { readonly thisFree: true; readonly passes: readonly KeyPattern[] } | { readonly thisFree: false };
    const verdicts = new Map<string, Verdict>();
    /** Whether a call through the static path `callee` (nothing writes it later) may use `this`. */
    const verdictOf = (callee: PropertyPath): Verdict => {
        const id = JSON.stringify(callee);
        const known = verdicts.get(id);
        if (known !== undefined) return known;
        const key = callee.length === 1 ? callee[0] : undefined;
        const wrapper = key === undefined ? undefined : runtime.wrappers.get(key);
        const assigned = preludeWriteCount.get(id) === 1 ? assignedFunctions.get(id) : undefined;
        let verdict: Verdict = { thisFree: false };
        // Later writes: those to a prefix only build an object whose method at the path doesn't use `this`
        // (`G.k = (function () {...})()` the guest didn't finish), and those to the path itself only put down values
        // calls can't use `this` through.
        const builtThisFree = (write: StorageEffect): boolean => {
            const value = write.value;
            if (write.keys.length !== callee.length - 1 || value?.type !== "CallExpression" || value.callee.type !== "FunctionExpression" || value.arguments.length > 0) return false;
            const builder = builderOf(value.callee, scopes);
            const name = callee.at(-1) as string;
            const method = typeof builder === "string" ? undefined : (builder.methods.get(name) ?? builder.closures.get(name)?.fn);
            return method !== undefined && !usesThis(method);
        };
        const prefixWrite = writes.some((write) => write.keys.length < callee.length && matches(write.keys, callee) && !builtThisFree(write));
        const ownWrites = writes.filter((write) => write.keys.length === callee.length && matches(write.keys, callee));
        if (prefixWrite || !ownWrites.every((write) => write.value !== undefined && valueKind(write.value) !== "unknown")) verdict = { thisFree: false };
        // A call alias stands for a builtin called with the arguments (what the aliases pass rewrites it to), not G;
        // so do the other getters the setup calls installed (call aliases whose style couldn't be probed).
        else if (key !== undefined && (runtime.callAliases.has(key) || runtime.setupKeys.has(key))) verdict = { thisFree: true, passes: [] };
        // A wrapper applies a function target to its own receiver: the receiver is handed on, unless the target is
        // known not to use `this` (then it is the target's own verdict). A value target is returned as is (unless
        // something may write a function there later).
        else if (wrapper !== undefined) {
            const appliesTarget = runtime.guest.inspect(wrapper.target)?.type === "function" || writes.some((write) => affects(write, wrapper.target));
            const target = appliesTarget ? verdictOf(wrapper.target) : undefined;
            if (target === undefined) verdict = { thisFree: true, passes: [] };
            else if (target.thisFree) verdict = target;
            else verdict = { thisFree: true, passes: wrapper.receiver === undefined ? [] : [wrapper.receiver] };
        } else if (assigned !== undefined) verdict = usesThis(assigned) ? { thisFree: false } : { thisFree: true, passes: [] };
        else {
            // Not a function in the snapshot, reached through data properties only: the call throws before running anything.
            const info = runtime.guest.inspect(callee);
            if (info !== undefined && info.data && info.type !== "function") verdict = { thisFree: true, passes: [] };
        }
        verdicts.set(id, verdict);
        return verdict;
    };
    /**
     * `G[k]()` with `k` computed: whatever own property it reaches must not use `this`, including properties written
     * later. (Inherited methods only call or bind `G`; Object.prototype's legacy `__defineGetter__`/`__defineSetter__`,
     * the two that would change it, are taken not to be what such keys select.)
     */
    let computedVerdict: Verdict | undefined;
    const computedKeyVerdict = (): Verdict => {
        if (computedVerdict !== undefined) return computedVerdict;
        computedVerdict = { thisFree: false };
        const rewritten = writes.find((write) => write.keys.length === 0 || (write.keys.length === 1 && (write.value === undefined || valueKind(write.value) === "unknown")));
        if (rewritten !== undefined) {
            log.debug(`calls through computed ${runtime.storage} keys may use this: a write puts down a value they could call`, rewritten.node);
            return computedVerdict;
        }
        const passes: KeyPattern[] = [];
        for (const key of runtime.guest.ownCallables() ?? []) {
            const verdict = verdictOf([key]);
            if (!verdict.thisFree) {
                log.debug(`calls through computed ${runtime.storage} keys may use this: they can reach ${runtime.storage}.${key}`);
                return computedVerdict;
            }
            passes.push(...verdict.passes);
        }
        computedVerdict = { thisFree: true, passes };
        return computedVerdict;
    };
    let thisFree = 0;
    for (const call of calls) {
        if (call.timing.kind === "never" || (call.timing.kind === "prelude" && call.timing.reflected)) continue;
        const { callee } = call;
        const verdict = callee.every((k) => k !== undefined) ? verdictOf(callee as PropertyPath) : callee.length === 1 ? computedKeyVerdict() : { thisFree: false as const };
        if (verdict.thisFree) {
            thisFree++;
            for (const keys of verdict.passes) later.push({ kind: "escape", keys, node: call.node, via: "as this of a wrapper's target" });
            continue;
        }
        later.push({ kind: "escape", keys: callee.slice(0, -1), node: call.node, via: `as this of ${describe(runtime.storage, callee)}()` });
    }

    // `G` kept as a global property only matters if the program reaches it again under that name, written out: a
    // global reference, `.P`, or `["P"]` (a name it computes is taken not to be one of these).
    /** Global names G is kept under that the program names again. */
    const mentioned = new Set<string>();
    if (globalStores.length > 0) {
        const names = new Set(globalStores.map((store) => store.name));
        const own = new Set(globalStores.map((store) => store.key));
        const mention = (node: Node, name: string): void => {
            if (!names.has(name) || own.has(node)) return;
            mentioned.add(name);
            later.push({ kind: "escape", keys: [], node, via: `by the global name ${name}` });
        };
        traverse(runtime.root, {
            Identifier(path) {
                const node = path.node;
                if (!names.has(node.name) || matcher.isStorage(node)) return; // `G` itself is followed already
                if (path.parent?.type === "MemberExpression" && path.key === "property" && !path.parent.computed) return mention(node, node.name);
                // A reference to a global of that name (a local isn't the global property; top-level declarations are).
                if (scopes.referenceOf(node) === undefined) return;
                const variable = scopes.staticVariableOf(node);
                if (variable === undefined || variable.scope.type === "global") mention(node, node.name);
            },
            MemberExpression(path) {
                const property = path.node.property;
                if (path.node.computed && property.type === "Literal" && typeof property.value === "string") mention(property, property.value);
            },
        });
        for (const store of globalStores) log.debug(`${runtime.storage} kept as global ${store.name}`, store.node);
    }

    // One effect per kind and path answers for all of them (the first one found is the one reported); writes directly
    // in a root statement the guest didn't finish are kept per statement, for `staleAt`'s `built`.
    const unique = new Map<string, StorageEffect>();
    for (const effect of later) {
        const id = `${effect.kind}:${JSON.stringify(effect.keys)}${effect.kind === "write" && effect.statement !== undefined ? `@${effect.statement}` : ""}`;
        if (!unique.has(id)) unique.set(id, effect);
    }
    const effects = [...unique.values()];
    log.debug(`storage: ${preludeWrites.length} write(s) by prelude code, ${effects.length} other effect(s) on distinct paths; ${thisFree} later call(s) on ${runtime.storage} paths don't use this`);
    if (log.debugging) for (const effect of effects) log.debug(`storage ${effect.kind} of ${describe(runtime.storage, effect.keys)} (${effect.via}) the snapshot doesn't hold`, effect.node);

    return {
        staleAt(site, path, writesOnly = false, built) {
            const timing = sites.get(site);
            if (timing === undefined) return { reason: `this reference to ${runtime.storage} wasn't analysed`, node: site };
            if (timing.kind === "never") return undefined;
            const builtAt = built === undefined ? -1 : (statements as readonly Node[]).indexOf(built);
            const effect = effects.find((candidate) => (!writesOnly || candidate.kind === "write") && !(candidate.kind === "write" && candidate.statement === builtAt) && affects(candidate, path));
            if (effect !== undefined)
                return { reason: `${describe(runtime.storage, path)} may change after the prelude: ${effect.kind} of ${describe(runtime.storage, effect.keys)}`, node: effect.node };
            if (timing.kind === "prelude") {
                const lastWrite = preludeWrites.reduce((last, write) => (write.keys.length <= path.length && matches(write.keys, path) ? Math.max(last, write.last) : last), builtAt);
                if (timing.first <= lastWrite) return { reason: `read while the prelude is still setting ${describe(runtime.storage, path)} up`, node: site };
            }
            return undefined;
        },
        runsAfterPrelude(site) {
            const timing = sites.get(site);
            return timing !== undefined && timing.kind !== "prelude";
        },
        keptAsGlobal(node) {
            return globalStores.some((store) => store.node === node && !mentioned.has(store.name));
        },
        runsBefore(site, statement) {
            const timing = sites.get(site);
            if (timing === undefined || timing.kind === "later") return false;
            return timing.kind === "never" || timing.last < (statements as readonly Node[]).indexOf(statement);
        },
        lastPreludeStatement(site) {
            const timing = sites.get(site);
            return timing?.kind === "prelude" ? statements[timing.last] : undefined;
        },
        runsAfter(site, statement) {
            const timing = sites.get(site);
            if (timing === undefined) return false;
            if (timing.kind !== "prelude") return true;
            const index = (statements as readonly Node[]).indexOf(statement);
            return index >= 0 && timing.first > index;
        },
        reachedOnlyThroughStorage(path) {
            if (path.length === 0) return true;
            const count = preludeWrites.filter((write) => write.keys.length <= path.length && matches(write.keys, path)).length;
            return count === 1 && freshObjects.has(JSON.stringify(path));
        },
        preludeWritesTo(path) {
            return preludeWrites.filter((write) => write.keys.length <= path.length && matches(write.keys, path)).length;
        },
        runsOnlyInPrelude(fn) {
            return fn === undefined || timingOf(fn).kind !== "later";
        },
    };
};

/** The storage object's recognizer and what the program does to it. */
export interface StorageAnalysis {
    readonly matcher: StorageMatcher;
    readonly effects: StorageEffects;
}

/** One analysis per scope analysis (which passes share until bindings change). */
const analyses = new WeakMap<ScopeInfo, StorageAnalysis>();

/**
 * The storage analysis for the program as `scopes` describes it, computed once and shared while that scope analysis
 * is reused. The passes in between only replace expressions (resolving calls, inlining wrappers, folding): that
 * removes effects, or swaps one for an equal one (a wrapper call for its target's call on the same receiver), so the
 * shared result stays an over-approximation. A binding change brings a new scope analysis and a new run.
 */
export const storageAnalysis = (program: Node, runtime: RuntimeModel, scopes: ScopeInfo, log: PassLog): StorageAnalysis => {
    let analysis = analyses.get(scopes);
    if (analysis === undefined) {
        const matcher = storageMatcher(program, runtime, scopes);
        analysis = { matcher, effects: storageEffects(runtime, matcher, scopes, log) };
        analyses.set(scopes, analysis);
    }
    return analysis;
};

/** Share an analysis made for the program as it now is (resolve-calls', with its computed keys resolved). */
export const shareStorageAnalysis = (scopes: ScopeInfo, analysis: StorageAnalysis): void => {
    analyses.set(scopes, analysis);
};
