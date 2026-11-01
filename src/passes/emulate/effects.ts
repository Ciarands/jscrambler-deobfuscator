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
 * Relative to the prelude: `prelude` runs only during root statements `first`..`last` (`reflected` when the guest
 * finished them all, so the snapshot holds its effects); `later` may run after it; `never` nothing refers to it.
 */
type Timing = { readonly kind: "prelude"; readonly reflected: boolean; readonly first: number; readonly last: number } | { readonly kind: "later" } | { readonly kind: "never" };

const LATER: Timing = { kind: "later" };
const NEVER: Timing = { kind: "never" };

/**
 * Invoked right where written (also via `.call`/`.apply`/`new`), plain (async/generator bodies run later), and unable
 * to run again (doesn't use its own name).
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

/** Not counting nested non-arrow functions. */
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

/** `undefined` for the root's top level, `null` when it can't be told. */
const enclosingFunction = (scope: Scope | null, root: Node): Node | undefined | null => {
    for (let s = scope; s !== null; s = s.upper) {
        if (s.type === "function") return (s.block as unknown as Node) === root ? undefined : (s.block as unknown as Node);
        if (s.type === "global" || s.type === "module") return undefined;
        if (s.type === "class-field-initializer" || s.type === "class-static-block") return null;
    }
    return undefined;
};

/** `undefined` stands for a key computed at run time. */
type KeyPattern = readonly (string | undefined)[];

/**
 * Something the snapshot may not show: a `write` to `keys`, or an `escape` of the object at `keys` to code this
 * analysis doesn't follow (argument, stored value, `this` of a call), which may then write anything below it.
 */
interface StorageEffect {
    readonly kind: "write" | "escape";
    readonly keys: KeyPattern;
    readonly node: Node;
    /** For the log. */
    readonly via: string;
    readonly value?: Node | undefined;
    /** Set for code directly in a root statement the guest didn't finish. */
    readonly statement?: number | undefined;
}

/** What calling a value could do with its `this`: `inert` (not callable), `this-free` (body has no `this`), `unknown`. */
type ValueKind = "inert" | "this-free" | "unknown";

const worst = (kinds: readonly ValueKind[]): ValueKind => (kinds.includes("unknown") ? "unknown" : kinds.includes("this-free") ? "this-free" : "inert");

/** An immediately invoked function's kind is that of what it returns. */
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

/** Created right there and held by no binding: code can only get hold of it through where it is put. */
const isFreshObject = (value: Node): boolean => {
    if (value.type === "ObjectExpression") return value.properties.every((property) => property.type === "Property" && property.kind === "init");
    if (value.type !== "CallExpression" || value.callee.type !== "FunctionExpression" || value.arguments.length > 0 || value.callee.async || value.callee.generator) return false;
    const returns = returnsOf(value.callee);
    const [only] = returns;
    return returns.length === 1 && only?.type === "ReturnStatement" && only.argument !== null && isFreshObject(only.argument);
};

export interface Staleness {
    readonly reason: string;
    readonly node: Node;
}

export interface StorageEffects {
    /**
     * Why the value at `path`, read through `site`, may differ from the snapshot; `undefined` when it can't.
     * `writesOnly` ignores objects handed to calls as `this` (for a wrapper's target: the runtime's own calls run in the
     * guest too). `built`: a root statement storing the value at `path`, so its own writes don't count and the read
     * must start after it.
     */
    readonly staleAt: (site: Node, path: PropertyPath, writesOnly?: boolean, built?: Node) => Staleness | undefined;
    /** `site` is a reference to `G`, here and below. */
    readonly runsAfterPrelude: (site: Node) => boolean;
    readonly runsBefore: (site: Node, statement: Node) => boolean;
    /** Undefined if `site` runs only later, never, or wasn't analysed. */
    readonly lastPreludeStatement: (site: Node) => Node | undefined;
    /** In a later root statement, after the prelude, or never. */
    readonly runsAfter: (site: Node, statement: Node) => boolean;
    /** `node` only stores `G` as a global property (`G[g].P = G`) the program never names again (model 2). */
    readonly keptAsGlobal: (node: Node) => boolean;
    /**
     * Code reaches the object at `path` only through `G`'s paths, so model 3 covers every change: `G` itself, or a fresh
     * object the prelude's one write to the path (or a prefix) put there, held by no closure.
     */
    readonly reachedOnlyThroughStorage: (path: PropertyPath) => boolean;
    /** Prelude writes in the snapshot to `path` or a prefix. */
    readonly preludeWritesTo: (path: PropertyPath) => number;
    /** `fn` is a root function, or `undefined` for the root's top level. */
    readonly runsOnlyInPrelude: (fn: Node | undefined) => boolean;
}

const matches = (pattern: KeyPattern, path: PropertyPath): boolean => {
    for (const [i, key] of pattern.entries()) if (key !== undefined && key !== path[i]) return false;
    return true;
};

const affects = (effect: StorageEffect, path: PropertyPath): boolean => (effect.kind === "write" ? effect.keys.length <= path.length : effect.keys.length < path.length) && matches(effect.keys, path);

const describe = (storage: string, keys: KeyPattern): string => storage + keys.map((k) => (k === undefined ? "[?]" : `[${JSON.stringify(k)}]`)).join("");

/**
 * Prelude code: a root statement's top-level code, a function invoked in place there, or a prelude-only function (every
 * use a direct call from prelude code; least fixpoint). Unreferenced functions never run. The script is taken to be
 * closed: other scripts don't call its functions. A mention of `.callee`/`.caller` disables prelude-only functions.
 */
const timeline = (runtime: RuntimeModel, scopes: ScopeInfo, log: PassLog): ((fn: Node) => Timing) => {
    const statements = rootStatements(runtime.root);
    const parentOf = new Map<Node, { fn: Node | undefined; index: number; inPlace: boolean }>();
    const topLevelIndex = new Map<Node, number>();
    const directCallees = new Set<Node>();
    const candidates: { fn: Node; references: readonly Reference[] }[] = [];
    let reflective = false;
    /** Bound once, by its definition alone (no write reference, or `var f = function`'s initializer only). */
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

    /** For `undefined`: the top level of root statement `index`. */
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
 * Everything the program does to `G` that the snapshot may not show. `G` changes only through code naming its paths:
 * `G`, other names for it, locals bound to a static part (`var t = G.a`), `this` in methods called on `G` paths, and a
 * global the prelude keeps it under (`G[g].P = G`, once the program names `P` again). Each reference is followed up
 * its member chain to a write, a call (the object read from becomes `this`), or a read handing the value on.
 *
 * What prelude code does is in the snapshot when the guest finished the statements it runs in; anything else may
 * happen later. Model assumptions, beyond the snapshot's own (app code runs after the prelude):
 * - a reference to a part of `G` obtained otherwise (a call's result, an argument, a computed read held in a local)
 *   isn't used to change `G` after the prelude;
 * - operators only read: the runtime's objects don't override `valueOf`/`toString`.
 *
 * `keyOf` resolves computed keys the caller knows (`G[G.w(147)]`).
 */
export const storageEffects = (runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, log: PassLog, keyOf?: (property: Node) => string | undefined): StorageEffects => {
    const statements = rootStatements(runtime.root);
    const timingOf = timeline(runtime, scopes, log);
    const later: StorageEffect[] = [];
    const preludeWrites: { keys: KeyPattern; last: number }[] = [];
    const sites = new Map<Node, Timing>();
    /** By path. */
    const assignedFunctions = new Map<string, Node>();
    const preludeWriteCount = new Map<string, number>();
    const freshObjects = new Set<string>();
    const calls: { callee: KeyPattern; node: Node; timing: Timing }[] = [];
    /** `G[g].P = G`, with `G[g]` the global object. */
    const globalStores: { name: string; key: Node; node: Node }[] = [];

    /** `G[g].P` or `globalThis.P` (as global-proxy rewrites it). */
    const globalProperty = (target: Node): { name: string; key: Node } | undefined => {
        if (target.type !== "MemberExpression") return undefined;
        const owner = target.object;
        const slot = owner.type === "MemberExpression" && matcher.isStorage(owner.object) ? propertyKey(owner) : undefined;
        const isGlobalObject = (slot !== undefined && runtime.globalKeys.has(slot)) || (owner.type === "Identifier" && owner.name === "globalThis" && scopes.isGlobalReference(owner));
        const name = propertyKey(target);
        return isGlobalObject && name !== undefined ? { name, key: target.property } : undefined;
    };
    const keyOfMember = (member: MemberExpression): string | undefined => propertyKey(member) ?? (member.computed && keyOf !== undefined ? keyOf(member.property) : undefined);
    const storeInto = (target: Node, keys: KeyPattern, value: Node): void => {
        const store = keys.length === 0 ? globalProperty(target) : undefined;
        if (store !== undefined) globalStores.push({ ...store, node: value });
    };

    // Locals bound once, by their initializer, to a static part of G (`var t = G.a[1]`).
    const parts = new Map<Variable, KeyPattern>();
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
                // A reference prelude code hands out is taken not to be used later.
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
                if (matcher.isAliasBinding(node) || (path.parent?.type === "FunctionDeclaration" && path.key === "id")) return;
                const declared = scopes.staticVariableOf(node);
                if (declared !== undefined && parts.has(declared) && declared.identifiers.includes(node as never)) return;
                const timing = timings.at(-1) as Timing;
                if (base.length === 0) sites.set(node, timing);
                // Values passed on (`(X = G).k`, `||`/`&&`/`??`, `?:`, sequences) count as G's: the careful reading.
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
                // Anything else reads or hands on the value; that is taken not to change G (see model assumptions above).
            },
        });
    }

    const writes = later.filter((effect) => effect.kind === "write");
    type Verdict = { readonly thisFree: true; readonly passes: readonly KeyPattern[] } | { readonly thisFree: false };
    const verdicts = new Map<string, Verdict>();
    const verdictOf = (callee: PropertyPath): Verdict => {
        const id = JSON.stringify(callee);
        const known = verdicts.get(id);
        if (known !== undefined) return known;
        const key = callee.length === 1 ? callee[0] : undefined;
        const wrapper = key === undefined ? undefined : runtime.wrappers.get(key);
        const assigned = preludeWriteCount.get(id) === 1 ? assignedFunctions.get(id) : undefined;
        let verdict: Verdict = { thisFree: false };
        // Later prefix writes must build an object whose method here doesn't use `this` (an unfinished
        // `G.k = (function () {...})()`); later writes to the path must put down values without `this`.
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
        // A call alias (or other setup getter) stands for a builtin called with the arguments, not on G.
        else if (key !== undefined && (runtime.callAliases.has(key) || runtime.setupKeys.has(key))) verdict = { thisFree: true, passes: [] };
        // A wrapper hands its receiver on to a function target, unless the target doesn't use `this`.
        else if (wrapper !== undefined) {
            const appliesTarget = runtime.guest.inspect(wrapper.target)?.type === "function" || writes.some((write) => affects(write, wrapper.target));
            const target = appliesTarget ? verdictOf(wrapper.target) : undefined;
            if (target === undefined) verdict = { thisFree: true, passes: [] };
            else if (target.thisFree) verdict = target;
            else verdict = { thisFree: true, passes: wrapper.receiver === undefined ? [] : [wrapper.receiver] };
        } else if (assigned !== undefined) verdict = usesThis(assigned) ? { thisFree: false } : { thisFree: true, passes: [] };
        else {
            // Not a function, reached through data properties only: the call throws before running anything.
            const info = runtime.guest.inspect(callee);
            if (info !== undefined && info.data && info.type !== "function") verdict = { thisFree: true, passes: [] };
        }
        verdicts.set(id, verdict);
        return verdict;
    };
    /**
     * `G[k]()`, `k` computed: every own property, including later ones, must not use `this`. Inherited methods only
     * call or bind; `__defineGetter__`/`__defineSetter__` are taken not to be what such keys select.
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

    // Only names the program writes out count (global reference, `.P`, `["P"]`); computed names are taken not to be these.
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
                // Locals aren't the global property; top-level declarations are.
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

    // One effect per kind and path answers for all; writes in unfinished root statements are kept per statement for `built`.
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

export interface StorageAnalysis {
    readonly matcher: StorageMatcher;
    readonly effects: StorageEffects;
}

/** Passes share one scope analysis until bindings change. */
const analyses = new WeakMap<ScopeInfo, StorageAnalysis>();

/**
 * The passes sharing a scope analysis only replace expressions, which removes effects or swaps one for an equal one, so
 * the shared result stays an over-approximation.
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

/** For an analysis of the program as it now is (resolve-calls', with computed keys resolved). */
export const shareStorageAnalysis = (scopes: ScopeInfo, analysis: StorageAnalysis): void => {
    analyses.set(scopes, analysis);
};
