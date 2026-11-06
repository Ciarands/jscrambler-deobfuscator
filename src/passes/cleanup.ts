import type { CallExpression, Expression, MemberExpression, Node, Program, Statement, VariableDeclaration, VariableDeclarator } from "../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../core/ast.js";
import { at } from "../core/build.js";
import { constantEnv } from "../core/constants.js";
import type { ConstantEnv } from "../core/constants.js";
import { evaluate } from "../core/evaluate.js";
import { pushAll, spliceList } from "../core/list.js";
import { parse, ParseError } from "../core/parse.js";
import { isPlainPrimitive, isPure, isPureTest } from "../core/purity.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Facts } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { PropertyPath, RuntimeModel } from "./runtime/model.js";
import { RUNTIME } from "./runtime/model.js";
import { definitionOf, parentsWithin } from "./runtime/builders.js";
import type { DecoderProof } from "./runtime/decoder.js";
import { DECODER_PROOF } from "./runtime/decoder.js";
import { FUNCTION_NAMES } from "./runtime/decoder-host.js";
import type { StorageEffects } from "./runtime/effects.js";
import { storageAnalysis } from "./runtime/effects.js";
import type { StorageMatcher } from "./runtime/storage.js";
import { rootStatements, storageMatcher } from "./runtime/storage.js";
import { isAliasDeclarator, isGlobalRead, onlyTested } from "./storage-usage.js";
import { DETECTOR_BUILDERS } from "./detectors.js";
import { keySets, mayName } from "./key-sets.js";
import { inlineStorageAliases } from "./storage-aliases.js";
import type { Effect, RuntimeCall } from "./locality.js";
import { callLocalityOf, exposedLocalityOf } from "./locality.js";

const isLocalScope = (scopeType: string): boolean => scopeType !== "global" && scopeType !== "module";

/**
 * - `def`: `G.k = ...`; removable when its right side has no effect outside the storage object;
 * - `stage`: a runtime call with constant arguments, or a bare read (decoder stages, code locks), affecting `key`;
 * - `setup`: the call that defined the aliases; goes once no alias name or call-alias key is used;
 * - `fn`: a root function; goes once only removed statements name it;
 * - `store`: `globalThis.P = G`; other scripts don't read it (model 2).
 */
type Role =
    | { kind: "def"; key: string; removable: boolean; effect?: string | undefined }
    | { kind: "stage"; key: string; probe: { call: PropertyPath } | { read: PropertyPath } }
    | { kind: "setup" }
    | { kind: "fn"; name: string }
    | { kind: "store" }
    | { kind: "other" };

const isRemovable = (role: Role): boolean => (role.kind === "def" && role.removable) || role.kind === "stage" || role.kind === "setup" || role.kind === "fn" || role.kind === "store";

/**
 * Why evaluating `right` (of a root `G.k = right`) may change something outside the storage object, its own state and
 * objects it creates; `undefined` when it can't. It completes (model 1). Proofs: `isPure`; the setup evaluator's
 * (`getters.ts`, `RuntimeModel.local`); a templated decoder's build on the host (`DecoderProof.hostBuilt`); a read of
 * a storage property no setup call defined (a data property, model 9); an immediately invoked function `locality.ts`
 * shows local, with call aliases as the builtins they stand for (model 7) and calls of templated string decoders,
 * which write only the state `G` holds for them (`DecoderProof`).
 */
const definitionEffect = (
    statement: Statement,
    right: Node,
    runtime: RuntimeModel,
    matcher: StorageMatcher,
    effects: StorageEffects,
    scopes: ScopeInfo,
    decoders: DecoderProof | undefined
): string | undefined => {
    if (isPure(right, scopes) || runtime.local.has(statement) || decoders?.hostBuilt.has(statement) === true) return undefined;
    const path = memberPath(right);
    if (path !== undefined && matcher.isStorage(path.root)) {
        const [key] = path.keys;
        return path.keys.length === 1 && key !== undefined && !runtime.setupKeys.has(key) && !runtime.callAliases.has(key) && !FUNCTION_NAMES.includes(key)
            ? undefined
            : "it reads a storage property a getter may hold";
    }
    if (right.type !== "CallExpression" || (right.callee.type !== "FunctionExpression" && right.callee.type !== "ArrowFunctionExpression")) return "its right side isn't a builder";
    if (!right.arguments.every((arg) => arg.type !== "SpreadElement" && isPure(arg, scopes))) return "its builder's arguments may have effects";
    const runtimeCall = (call: Node): RuntimeCall | undefined => {
        if (call.type !== "CallExpression" || call.callee.type !== "MemberExpression") return undefined;
        const callee = memberPath(call.callee);
        if (callee === undefined || !matcher.isStorage(callee.root)) return undefined;
        const [first] = callee.keys;
        const alias = callee.keys.length === 1 && first !== undefined ? runtime.callAliases.get(first) : undefined;
        if (alias !== undefined) return { kind: "alias", owner: alias.owner, original: alias.original, style: alias.style, nullishCalls: alias.nullishCalls };
        return decoders?.templated.has(targetId(runtime, callee.keys)) === true ? { kind: "own-state" } : undefined;
    };
    const effect = callLocalityOf(right.callee, scopes, parentsWithin(right.callee), (call) => isGlobalRead(call, runtime, matcher, effects), runtimeCall);
    return effect?.reason;
};

const roleOf = (statement: Statement, runtime: RuntimeModel, matcher: StorageMatcher, effects: StorageEffects, scopes: ScopeInfo, inputs: RemovalInputs): Role => {
    const { isStorage } = matcher;
    const keptAsGlobal = (node: Node): boolean => effects.keptAsGlobal(node);
    if (runtime.setup.has(statement)) return { kind: "setup" };
    if (statement.type !== "ExpressionStatement") return { kind: "other" };
    const e = statement.expression;
    if (e.type === "AssignmentExpression" && e.operator === "=" && isStorage(e.right) && keptAsGlobal(e.right)) return { kind: "store" };
    if (e.type === "AssignmentExpression" && e.operator === "=" && e.left.type === "MemberExpression") {
        // `(globalThis.P = G).k = v` (model 2).
        const object = e.left.object;
        const holder = object.type === "AssignmentExpression" && object.operator === "=" && isStorage(object.right) && keptAsGlobal(object.right) ? object.right : object;
        if (isStorage(holder)) {
            const key = propertyKey(e.left);
            if (key === undefined) return { kind: "other" };
            const effect = inputs.detectorBuilders?.has(statement) === true ? undefined : definitionEffect(statement, e.right, runtime, matcher, effects, scopes, inputs.decoders);
            return { kind: "def", key, removable: effect === undefined, effect };
        }
    }
    const target = e.type === "CallExpression" ? e.callee : e;
    const path = memberPath(target);
    if (path === undefined || !isStorage(path.root)) return { kind: "other" };
    // A call through a wrapper affects its target's state, not the wrapper's.
    const [first] = path.keys;
    const affected = (first === undefined ? undefined : runtime.wrappers.get(first)?.target[0]) ?? first;
    if (affected === undefined) return { kind: "other" };
    if (e.type !== "CallExpression") return { kind: "stage", key: affected, probe: { read: path.keys } };
    if (e.arguments.some((arg) => arg.type === "SpreadElement" || !evaluate(arg).ok)) return { kind: "other" };
    return { kind: "stage", key: affected, probe: { call: path.keys } };
};

const MAX_CLEANUP_ROUNDS = 16;

/**
 * Removes the runtime once nothing needs it, unused locals, dead stores, and initial values overwritten at once.
 *
 * A definition goes when its key is dead and its right side had no effect outside the storage object, or it only
 * builds anti-debug detectors (model 5). A stage call goes when its state is dead and it is shown effect-free. Nothing
 * goes when the storage object escapes or is read with a computed key in code that may run after the prelude; a
 * computed read in prelude-only code keeps only what it may select (`selectable`).
 *
 * Storage aliases are inlined after the removals, which need the scope analysis that doesn't know the new names;
 * declarations are merged after both (`mergeOverwrittenDeclarations`).
 */
export const cleanup: Pass = {
    name: "cleanup",
    description: "Remove the dead runtime (decoder, wrappers, setup, prelude calls) and unused locals",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const scopes = scope();
        const model = facts.get(RUNTIME);
        if (model !== undefined && log.debugging) logLostFacts(model, log);
        const inputs: RemovalInputs = { decoders: facts.get(DECODER_PROOF), detectorBuilders: facts.get(DETECTOR_BUILDERS), evalUses: new WeakMap() };
        let runtime = 0;
        let locals = 0;
        let stoppedEarly = 0;
        // Removals can expose more unused code; `forget` updates the analysis in between.
        let runtimeDirty = true;
        let last = { runtime: 0, stores: 0, locals: 0 };
        for (let round = 0; ; round++) {
            if (round === MAX_CLEANUP_ROUNDS) {
                stoppedEarly = 1;
                log.warn(
                    `stopped after ${MAX_CLEANUP_ROUNDS} rounds, the last still removing ${last.runtime} runtime statement(s), ${last.stores} dead store(s) and ${last.locals} unused local(s); more may be removable`
                );
                break;
            }
            const removed: Node[] = [];
            last = {
                runtime: runtimeDirty ? removeRuntime(program, model, scopes, log, inputs, removed) : 0,
                stores: removeDeadStores(program, scopes, log, removed),
                locals: removeUnusedLocals(program, scopes, log, removed),
            };
            runtime += last.runtime;
            locals += last.stores + last.locals;
            if (last.runtime + last.stores + last.locals === 0) break;
            runtimeDirty = last.runtime > 0 || (model !== undefined && namesRuntime(removed, model, storageMatcher(program, model, scopes)));
            scopes.forget(removed);
        }
        const aliases = model === undefined ? 0 : inlineStorageAliases(model, storageAnalysis(program, model, scopes, log).matcher, scopes, log);
        const merged = mergeOverwrittenDeclarations(program, log, facts);
        // The inlined storage name is a reference the analysis doesn't know; a merge drops a declarator it lists.
        // Settled: the last round found nothing to remove (where it skipped `removeRuntime`, `namesRuntime` showed it
        // would find nothing) in the program as it is left, with the analysis `forget` kept in step (what a refresh
        // gives: removals are all that changed), and neither step after it changed anything.
        return {
            changed: runtime + locals + aliases + merged,
            bindingsChanged: aliases > 0 || merged > 0,
            settled: stoppedEarly === 0 && aliases === 0 && merged === 0,
            stats: { runtime, locals, aliases, merged, stoppedEarly },
        };
    },
};

/** Removing code that doesn't name the runtime leaves every runtime statement's liveness unchanged. */
const namesRuntime = (removed: readonly Node[], runtime: RuntimeModel, matcher: StorageMatcher): boolean => {
    const names = new Set<string>([
        runtime.storage,
        ...[...matcher.aliases].map((variable) => variable.name),
        ...runtime.aliases.map((alias) => alias.alias),
        ...runtime.unprovenAliases,
        ...runtime.setupGlobals,
    ]);
    for (const statement of rootStatements(runtime.root)) if (statement.type === "FunctionDeclaration" && statement.id !== null) names.add(statement.id.name);
    let found = false;
    for (const node of removed) {
        traverse(node, {
            Identifier(path) {
                if (names.has(path.node.name)) found = true;
            },
        });
        if (found) return true;
    }
    return false;
};

/** `local` and `setup` are keyed by root statement; an earlier pass splitting or removing one loses its fact. */
const logLostFacts = (runtime: RuntimeModel, log: PassContext["log"]): void => {
    const body = new Set<Node>(rootStatements(runtime.root));
    for (const [name, recorded] of [
        ["local", runtime.local],
        ["setup", runtime.setup],
    ] as const) {
        const lost = [...recorded].filter((statement) => !body.has(statement));
        if (lost.length > 0) log.debug(`${lost.length} of ${recorded.size} recorded ${name} statement(s) are no longer root statements (split or removed by an earlier pass)`, lost[0]);
    }
};

/** What one root statement does with the storage object, its aliases and other names. */
interface RootUses {
    readonly statement: Statement;
    role: Role;
    /** Storage keys it reads: statically, in literal `eval` code, or by a computed read `selectable` resolves. */
    readonly reads: Set<string>;
    /** Static writes to storage keys, for stage calls' proofs. */
    readonly writes: Set<string>;
    readonly names: Set<string>;
    /** A use of the storage object as a value or with a computed key. */
    escape: Node | undefined;
    /** A write of the storage binding. */
    rebind: Node | undefined;
    /** A use of an alias, a call alias or a setup global: the setup call stays with it. */
    aliasUse: Node | undefined;
    /** Computed reads of the storage object in prelude-only code, for `selectable`. */
    readonly computed: MemberExpression[];
}

/** The storage analysis `removeRuntime`'s steps share. */
interface RuntimeAnalysis {
    readonly runtime: RuntimeModel;
    readonly matcher: StorageMatcher;
    readonly effects: StorageEffects;
    readonly scopes: ScopeInfo;
}

/** What `removeRuntime` takes from the run beyond the analysis. */
interface RemovalInputs {
    readonly decoders: DecoderProof | undefined;
    readonly detectorBuilders: ReadonlySet<Node> | undefined;
    /** Per `eval` literal: cleanup asks every round. */
    readonly evalUses: WeakMap<Node, EvalUses | undefined>;
}

/**
 * A computed read `G[k]` in prelude-only code sees only what ran before it, and only keys `keySets` says it can name.
 * Adds what it may select to its root's `reads`/`aliasUse`; returns why each other statement is unreachable (for the log).
 */
const selectable = (roots: readonly RootUses[], { runtime, scopes, effects }: RuntimeAnalysis): Map<number, string> => {
    const unreachable = new Map<number, string>();
    const reachable = new Set<number>();
    for (const root of roots) {
        if (root.computed.length === 0) continue;
        const keysOf = keySets(scopes, parentsWithin(root.statement));
        for (const read of root.computed) {
            const keys = keysOf(read.property as Expression);
            for (const [other, { role, statement }] of roots.entries()) {
                if (role.kind !== "def" && role.kind !== "stage" && role.kind !== "setup") continue;
                if (effects.runsBefore(read.object, statement)) {
                    if (!unreachable.has(other)) unreachable.set(other, "a computed read of the runtime is done before it runs");
                    continue;
                }
                const names = role.kind === "setup" ? [...runtime.setupKeys] : [role.key];
                if (keys !== undefined && !names.some((name) => mayName(keys, name))) {
                    if (!unreachable.has(other)) unreachable.set(other, "a computed read of the runtime can't select its key");
                    continue;
                }
                reachable.add(other);
                if (role.kind === "setup") root.aliasUse ??= read;
                else root.reads.add(role.key);
            }
        }
    }
    for (const other of reachable) unreachable.delete(other);
    return unreachable;
};

const targetId = (runtime: RuntimeModel, path: readonly string[]): string => {
    const [first] = path;
    const wrapper = path.length === 1 && first !== undefined ? runtime.wrappers.get(first) : undefined;
    return JSON.stringify(wrapper?.target ?? path);
};

/**
 * Why the stage call `G.path(...)` at `index`, on key `k`, may change more than the state of the builder `G.k` holds;
 * `undefined` when it can't.
 *
 * `G.k` is built once, by `G.k = (function () {...})()` before the call. No other root statement names `G.k` or a
 * wrapper of something under it (one with a storage path for its receiver), but those wrappers' definitions and
 * stage calls on `k` (static paths, primitive arguments), and none rebinds `G` or uses it as a value or with a
 * computed key. So, if the builder leaks nothing, what it made is reachable only through `G.k`, and only those calls
 * run its functions afterwards. `exposedLocalityOf` proves that the builder, and any of its functions called that way
 * (this call's target among them), change nothing but the builder's variables and objects it and they create: no
 * builtin, global or storage key. (Model 7: builtins intact; the wrapper's `apply` is the builtin.)
 */
const stageRefusal = (
    index: number,
    key: string,
    path: PropertyPath,
    roots: readonly RootUses[],
    { runtime, matcher, effects, scopes }: RuntimeAnalysis,
    proofs: Map<string, Effect | undefined>
): string | undefined => {
    const name = `${runtime.storage}.${key}`;
    const definition = definitionOf(runtime, matcher.isStorage, [key]);
    if (typeof definition === "string") return `${name}: ${definition}`;
    if (roots.findIndex((root) => root.statement === definition.statement) > index) return `it runs before ${name} is built`;
    const wrappers = [...runtime.wrappers.values()].filter((wrapper) => wrapper.target[0] === key && wrapper.receiver !== undefined);
    const [first] = path;
    const wrapper = first === undefined ? undefined : runtime.wrappers.get(first);
    if (wrapper !== undefined && path.length > 1) return "it calls a property of a wrapper";
    const named = new Set([key, ...wrappers.map((w) => w.key)]);
    const allowed = new Set<Node>([definition.statement, ...wrappers.map((w) => w.definition)]);
    for (const [other, root] of roots.entries()) {
        if (allowed.has(root.statement) || (root.role.kind === "stage" && root.role.key === key)) continue;
        if ((root.escape ?? root.rebind) !== undefined) return `root statement ${other} rebinds ${runtime.storage} or uses it as a value or with a computed key`;
        if ([...named].some((k) => root.reads.has(k) || root.writes.has(k))) return `root statement ${other} names ${name} or a wrapper of it`;
    }
    const called = (wrapper?.target ?? path).slice(1);
    const id = JSON.stringify([key, called]);
    if (!proofs.has(id))
        proofs.set(
            id,
            exposedLocalityOf(definition.iife, called, scopes, parentsWithin(definition.iife), (call) => isGlobalRead(call, runtime, matcher, effects))
        );
    const effect = proofs.get(id);
    return effect === undefined ? undefined : `its builder, or a call of what it built, may change more than the builder's own state: ${effect.reason}`;
};

interface EvalUses {
    readonly keys: Set<string>;
    escape: boolean;
    readonly names: Set<string>;
}

/**
 * `eval("...")` code runs in the caller's scope and jscrambler hides storage reads there, so its uses count at the
 * call. Unparsable code throws before running: it uses nothing.
 */
const literalEvalUses = (call: CallExpression, storage: string, cache: RemovalInputs["evalUses"]): EvalUses | undefined => {
    const [code] = call.arguments;
    if (code?.type !== "Literal" || typeof code.value !== "string") return undefined;
    if (cache.has(code)) return cache.get(code);
    let parsed: Program;
    try {
        parsed = parse(code.value);
    } catch (error) {
        if (!(error instanceof ParseError)) throw error;
        cache.set(code, undefined);
        return undefined;
    }
    const uses: EvalUses = { keys: new Set<string>(), escape: false, names: new Set<string>() };
    traverse(parsed, {
        MemberExpression(path) {
            const node = path.node;
            if (node.object.type !== "Identifier" || node.object.name !== storage) return;
            const key = propertyKey(node);
            if (key === undefined || path.isWriteTarget()) uses.escape = true;
            else uses.keys.add(key);
        },
        Identifier(path) {
            const node = path.node;
            uses.names.add(node.name);
            if (node.name === storage && !(path.parent?.type === "MemberExpression" && path.key === "object")) uses.escape = true;
        },
    });
    cache.set(code, uses);
    return uses;
};

/** Each root statement's uses (`RootUses`), in `body` order. */
const collectUses = (body: readonly Statement[], roles: readonly Role[], { runtime, matcher, effects, scopes }: RuntimeAnalysis, evalUses: RemovalInputs["evalUses"]): RootUses[] => {
    const { isStorage } = matcher;
    const aliasNames = new Set([...runtime.aliases.map((a) => a.alias), ...runtime.unprovenAliases]);
    // A setup global stays reachable only where code names it (model 9).
    const { setupGlobals } = runtime;
    return body.map((statement, index): RootUses => {
        const role = roles[index] as Role;
        const uses: RootUses = { statement, role, reads: new Set(), writes: new Set(), names: new Set(), escape: undefined, rebind: undefined, aliasUse: undefined, computed: [] };
        const functions: Node[] = [];
        traverse(statement, {
            enter(path) {
                if (isFunctionNode(path.node)) functions.push(path.node);
            },
            exit(path) {
                if (functions.at(-1) === path.node) functions.pop();
            },
            MemberExpression(path) {
                const node = path.node;
                const key = propertyKey(node);
                if (key !== undefined && !node.computed && aliasNames.has(key)) uses.aliasUse ??= node;
                if (key !== undefined && setupGlobals.has(key)) uses.aliasUse ??= node;
                if (!isStorage(node.object)) return;
                if (key === undefined) {
                    // A call would hand `G` on as `this`.
                    const called = (path.parent?.type === "CallExpression" && path.key === "callee") || (path.parent?.type === "TaggedTemplateExpression" && path.key === "tag");
                    if (!called && !path.isWriteTarget() && effects.runsOnlyInPrelude(functions.at(-1))) uses.computed.push(node);
                    else uses.escape ??= node;
                    return;
                }
                const isDefTarget = role.kind === "def" && path.parent === (statement as { expression?: Node }).expression && path.key === "left";
                if (path.isWriteTarget()) uses.writes.add(key);
                else if (!isDefTarget) uses.reads.add(key);
                // A key the setup installed is read through its getter: rewritten or not, the setup call stays with it.
                if (runtime.callAliases.has(key) || runtime.setupKeys.has(key)) uses.aliasUse ??= node;
            },
            CallExpression(path) {
                const call = path.node;
                if (call.callee.type !== "Identifier" || call.callee.name !== "eval" || scopes.nameBoundAt(call.callee, "eval") !== false) return;
                const found = literalEvalUses(call, runtime.storage, evalUses);
                if (found === undefined) return;
                for (const key of found.keys) uses.reads.add(key);
                for (const name of found.names) {
                    uses.names.add(name);
                    if (aliasNames.has(name) || setupGlobals.has(name)) uses.aliasUse ??= call;
                }
                if (found.escape) uses.escape ??= call;
            },
            Identifier(path) {
                const node = path.node;
                if (scopes.referenceOf(node) !== undefined) uses.names.add(node.name);
                if ((aliasNames.has(node.name) || setupGlobals.has(node.name)) && scopes.isGlobalReference(node)) uses.aliasUse ??= node;
                if (!isStorage(node)) return;
                const asObject = path.parent?.type === "MemberExpression" && path.key === "object";
                const asDeclaration = path.parent?.type === "FunctionDeclaration" && path.key === "id";
                // Keeping G as a global isn't an escape (model 2).
                if (path.isWriteTarget()) uses.rebind ??= node;
                else if (!asObject && !asDeclaration && !isAliasDeclarator(path.parent, matcher, scopes) && !onlyTested(path) && !effects.keptAsGlobal(node)) uses.escape ??= node;
            },
        });
        return uses;
    });
};

/** Other top-level functions of a script are globals other code may call: they stay. */
const classifyFunctions = (roots: readonly RootUses[], runtime: RuntimeModel): void => {
    const runtimeNames = new Set<string>();
    for (const { role, names } of roots) if (role.kind !== "other") for (const name of names) runtimeNames.add(name);
    for (const root of roots) {
        const statement = root.statement;
        if (statement.type !== "FunctionDeclaration" || statement.id === null) continue;
        const name = statement.id.name;
        if (runtime.root.type !== "Program" || name === runtime.storage || runtimeNames.has(name)) root.role = { kind: "fn", name };
    }
};

interface Liveness {
    readonly kept: ReadonlySet<number>;
    /** A kept root statement reading each live key (for the log). */
    readonly liveBy: ReadonlyMap<string, number>;
}

/**
 * Root statements that stay: those not removable, what their reads and names reach (definitions and stage calls by
 * key, functions by name), and the setup call with what it reaches once one that stays uses an alias.
 */
const computeLiveness = (roots: readonly RootUses[], log: PassContext["log"]): Liveness => {
    const byKey = new Map<string, number[]>();
    const byName = new Map<string, number[]>();
    for (const [index, { role }] of roots.entries()) {
        if ((role.kind === "def" && role.removable) || role.kind === "stage") byKey.set(role.key, [...(byKey.get(role.key) ?? []), index]);
        if (role.kind === "fn") byName.set(role.name, [...(byName.get(role.name) ?? []), index]);
    }
    const kept = new Set<number>();
    const liveBy = new Map<string, number>();
    const used = new Set<string>();
    const work: number[] = [];
    const keep = (index: number) => {
        if (kept.has(index)) return;
        kept.add(index);
        work.push(index);
    };
    const drain = () => {
        for (let index = work.pop(); index !== undefined; index = work.pop()) {
            const root = roots[index] as RootUses;
            for (const key of root.reads) {
                if (liveBy.has(key)) continue;
                liveBy.set(key, index);
                for (const other of byKey.get(key) ?? []) keep(other);
            }
            for (const name of root.names) {
                if (used.has(name)) continue;
                used.add(name);
                for (const other of byName.get(name) ?? []) keep(other);
            }
        }
    };
    for (const [index, { role }] of roots.entries()) if (!isRemovable(role)) keep(index);
    drain();
    const aliasUse = [...kept].map((index) => roots[index]?.aliasUse).find((node) => node !== undefined);
    if (aliasUse !== undefined) {
        log.debug("setup call stays: an alias is still used", aliasUse);
        for (const [index, { role }] of roots.entries()) if (role.kind === "setup") keep(index);
        drain();
    }
    return { kept, liveBy };
};

/**
 * Why the stage call at `index`, which nothing that stays needs, must stay anyway; `undefined` when it can go. Its own
 * run completes (model 1: the top level runs to completion). A templated decoder writes only its own, dead, state
 * (model 7: builtins intact).
 */
const stageObjection = (
    index: number,
    role: Extract<Role, { kind: "stage" }>,
    roots: readonly RootUses[],
    analysis: RuntimeAnalysis,
    decoders: DecoderProof | undefined,
    proofs: Map<string, Effect | undefined>
): string | undefined => {
    const { runtime, effects } = analysis;
    // A bare read through data properties runs no code (`Snapshot` answers only those).
    if ("read" in role.probe) return typeof effects.snapshot.typeAt(role.probe.read) === "string" ? "runtime call has effects outside its own state" : undefined;
    if (decoders?.templated.has(targetId(runtime, role.probe.call)) === true) return undefined;
    return stageRefusal(index, role.key, role.probe.call, roots, analysis, proofs);
};

/**
 * Demotes the stage calls about to go that `stageObjection` keeps to ordinary statements, in order: a demoted one
 * counts against the next one's `stageRefusal`. Whether any was demoted (liveness must then be redone).
 */
const demoteStages = (
    roots: readonly RootUses[],
    kept: ReadonlySet<number>,
    analysis: RuntimeAnalysis,
    decoders: DecoderProof | undefined,
    proofs: Map<string, Effect | undefined>,
    log: PassContext["log"]
): boolean => {
    let demoted = false;
    for (const [index, root] of roots.entries()) {
        if (root.role.kind !== "stage" || kept.has(index)) continue;
        const why = stageObjection(index, root.role, roots, analysis, decoders, proofs);
        if (why === undefined) continue;
        root.role = { kind: "other" };
        demoted = true;
        log.debug(`kept: ${why}`, root.statement);
    }
    return demoted;
};

const removeRuntime = (program: Node, runtime: RuntimeModel | undefined, scopes: ScopeInfo, log: PassContext["log"], inputs: RemovalInputs, removed: Node[]): number => {
    if (runtime === undefined) return 0;
    const body = rootStatements(runtime.root);
    if (body.length === 0) return 0;
    const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
    const analysis: RuntimeAnalysis = { runtime, matcher, effects, scopes };
    const roles = body.map((statement) => roleOf(statement, runtime, matcher, effects, scopes, inputs));
    // Escapes and alias uses only matter in statements that stay; prelude-only computed reads go to `selectable`.
    const roots = collectUses(body, roles, analysis, inputs.evalUses);
    const unreachable = selectable(roots, analysis);
    classifyFunctions(roots, runtime);

    const proofs = new Map<string, Effect | undefined>();
    let liveness: Liveness;
    do {
        liveness = computeLiveness(roots, log);
        const escape = [...liveness.kept].map((index) => roots[index]?.escape).find((node) => node !== undefined);
        if (escape !== undefined) {
            log.info(`the storage object ${runtime.storage} escapes or is read with a computed key in code that stays; the runtime stays`, escape);
            return 0;
        }
    } while (demoteStages(roots, liveness.kept, analysis, inputs.decoders, proofs, log));

    const dropped = [...roots.keys()].filter((index) => !liveness.kept.has(index));
    if (log.debugging) logDefinitions(roots, liveness, unreachable, runtime.storage, log);
    for (const index of dropped.toReversed()) {
        log.debug(`removed runtime statement (${roots[index]?.role.kind})`, body[index]);
        removed.push(...body.splice(index, 1));
    }
    if (dropped.length > 0) log.info(`removed ${dropped.length} runtime statement(s)`);
    return dropped.length;
};

const logDefinitions = (roots: readonly RootUses[], { kept, liveBy }: Liveness, unreachable: ReadonlyMap<number, string>, storage: string, log: PassContext["log"]): void => {
    for (const [index, { role, statement }] of roots.entries()) {
        if (role.kind !== "def") continue;
        const name = `${storage}[${JSON.stringify(role.key)}]`;
        const reader = liveBy.get(role.key);
        const because = !kept.has(index)
            ? `goes: nothing that stays reads ${name}${unreachable.has(index) ? ` (${unreachable.get(index)})` : ""}`
            : role.effect !== undefined
              ? `stays: its right side may have effects outside the storage object (${role.effect})`
              : `stays: ${name} is read by root statement ${reader ?? "?"}, which stays`;
        log.debug(`definition ${because}`, statement);
    }
};

/**
 * The refreshed (not rebuilt) analysis still lists these; skipping them avoids a useless next round. Outlives the run:
 * the next run may get the same refreshed analysis.
 */
const removedDeclarations = new WeakSet<Node>();

/** `x = <pure>`, or a bare `x` that isn't a for-in/of head (the loop writes that one: an init reference at its id). */
const removableDeclarator = (node: Node, variable: Variable, scopes: ScopeInfo): node is VariableDeclarator => {
    if (node.type !== "VariableDeclarator" || node.id.type !== "Identifier" || !isPure(node.init, scopes)) return false;
    const references = scopes.references(variable);
    return references !== undefined && (node.init !== null || !references.some((reference) => reference.init === true && (reference.identifier as unknown as Node) === node.id));
};

const removeUnusedLocals = (program: Node, scopes: ScopeInfo, log: PassContext["log"], out: Node[]): number => {
    const within = scopes.manager.scopes.find((s) => s.type === "with");
    if (within !== undefined) {
        log.info("the program uses with; unused locals stay", within.block as unknown as Node);
        return 0;
    }
    // Fixpoint over candidates so whole chains go in one round. Block functions are skipped: sloppy-mode ones are
    // visible outside their block (Annex B), which the analysis doesn't model.
    const env = constantEnv(scopes, log);
    const candidates: { node: Node; variable: Variable; body: Node | null }[] = [];
    const bodies = new Map<Node, ReadonlySet<Node>>();
    const directlyIn = (block: Node, node: Node): boolean => {
        let body = bodies.get(block);
        if (body === undefined) {
            body = new Set<Node>(
                block.type === "Program" ? block.body : isFunctionNode(block) && (block as { body: Node }).body.type === "BlockStatement" ? (block as { body: { body: Node[] } }).body.body : []
            );
            bodies.set(block, body);
        }
        return body.has(node);
    };
    for (const scope of scopes.manager.scopes) {
        for (const variable of scope.variables) {
            const [def] = variable.defs;
            if (def === undefined || removedDeclarations.has(def.node as unknown as Node) || !mayBeOwn(variable)) continue;
            const node = def.node as unknown as Node;
            if (variable.defs.length > 1) {
                // `var x = a; ...; var x = b;`: one binding, which each declarator only writes (a parameter, catch
                // parameter or function of the name isn't a declarator, and `let`/`const` can't be redeclared).
                const declarators = variable.defs.map((d) => d.node as unknown as Node);
                if (declarators.every((d) => removableDeclarator(d, variable, scopes))) for (const d of declarators) candidates.push({ node: d, variable, body: d.init });
            } else if (def.type === "Variable" && removableDeclarator(node, variable, scopes)) {
                candidates.push({ node, variable, body: node.init });
            } else if (def.type === "FunctionName" && node.type === "FunctionDeclaration" && directlyIn(scope.block as unknown as Node, node)) {
                candidates.push({ node, variable, body: node });
            }
        }
    }
    const dead = new Set<Node>();
    const gone = new Set<Node>();
    for (let changed = true; changed;) {
        changed = false;
        for (const candidate of candidates) {
            const references = scopes.references(candidate.variable);
            if (dead.has(candidate.node) || references === undefined || !references.every((reference) => reference.init || gone.has(reference.identifier as unknown as Node))) continue;
            if (!ownBinding(candidate.variable, env)) continue;
            dead.add(candidate.node);
            changed = true;
            if (candidate.body !== null) traverse(candidate.body, { Identifier: (path) => void gone.add(path.node) });
        }
    }
    if (dead.size === 0) return 0;
    let removed = 0;
    traverse(program, {
        VariableDeclaration: {
            exit(path) {
                const declaration = path.node;
                const parent = path.parent;
                const unused = declaration.declarations.filter((declarator) => dead.has(declarator));
                if (unused.length === 0) return;
                for (const declarator of unused) log.debug(`removed unused ${declaration.kind} ${declarator.id.type === "Identifier" ? declarator.id.name : ""}`, declarator);
                declaration.declarations = declaration.declarations.filter((declarator) => !dead.has(declarator));
                for (const declarator of unused) removedDeclarations.add(declarator);
                pushAll(out, unused);
                removed += unused.length;
                if (declaration.declarations.length > 0) return;
                if (parent?.type === "ForStatement" && path.key === "init") parent.init = null;
                else if (path.isInStatementList()) path.remove();
                else path.replace(at<Statement>({ type: "EmptyStatement" }, declaration));
            },
        },
        FunctionDeclaration: {
            exit(path) {
                const node = path.node as Node;
                if (!dead.has(node) || node.type !== "FunctionDeclaration") return;
                log.debug(`removed unused function ${node.id?.name ?? ""}`, node);
                path.remove();
                removedDeclarations.add(node);
                out.push(node);
                removed++;
            },
        },
    });
    if (removed > 0) log.info(`removed ${removed} unused local declaration(s)`);
    return removed;
};

/** `x = <primitive>;`, `x += <primitive>;`, `x++;` or `x = <pure>;`. */
const storeOf = (statement: Node, scopes: ScopeInfo): { target: Node; update: boolean; primitive: boolean } | undefined => {
    if (statement.type !== "ExpressionStatement") return undefined;
    const e = statement.expression;
    if (e.type === "UpdateExpression") return e.argument.type === "Identifier" ? { target: e.argument, update: true, primitive: true } : undefined;
    if (e.type !== "AssignmentExpression" || e.left.type !== "Identifier") return undefined;
    if (isPlainPrimitive(e.right)) return { target: e.left, update: e.operator !== "=", primitive: true };
    return e.operator === "=" && isPure(e.right, scopes) ? { target: e.left, update: false, primitive: false } : undefined;
};

/** Reachable only by name from the program's own code (model 2 for script globals). */
const ownBinding = (variable: Variable, env: ConstantEnv): boolean => mayBeOwn(variable) && (variable.scope.type !== "global" || env.onlyByName(variable));

/** `with` is checked once per program; a direct eval marks the scopes around it `dynamic`. */
const mayBeOwn = (variable: Variable): boolean => (isLocalScope(variable.scope.type) ? !variable.scope.dynamic : variable.scope.type === "global");

/** A read inside the test of an `if` (through operators only): a candidate guard of `guardedStoresOf`. */
const readInTest = (identifier: Node, scopes: ScopeInfo): boolean => {
    let node = identifier;
    for (let parent = scopes.parentOf(node); parent !== undefined; node = parent, parent = scopes.parentOf(node)) {
        if (parent.type === "IfStatement") return parent.test === node;
        if (parent.type !== "BinaryExpression" && parent.type !== "LogicalExpression" && parent.type !== "UnaryExpression") return false;
    }
    return false;
};

interface Store {
    readonly statement: Node;
    readonly targets: readonly Node[];
    /** The guard's identifiers (`guardedStoresOf`): reads of the target that go with the statement. */
    readonly reads: readonly Node[];
    readonly update: boolean;
    readonly primitive: boolean;
}

/**
 * `if (test) { x = a; } else { x = b; }` (a branch may be empty or missing) with a test that can't throw or run code
 * (`isPureTest`): stores to `x`, plus whatever the test reads. With `x` read nowhere else, its value decides only
 * which of these stores runs, and nothing observes either. The walk records the branches' stores on their own too,
 * with their update and primitive flags, so this one claims neither.
 */
const guardedStoresOf = (statement: Node, scopes: ScopeInfo): Store | undefined => {
    if (statement.type !== "IfStatement" || !isPureTest(statement.test, scopes)) return undefined;
    const branches = [statement.consequent, statement.alternate].flatMap((branch) => (branch === null ? [] : branch.type === "BlockStatement" ? branch.body : [branch]));
    const targets: Node[] = [];
    for (const branch of branches) {
        const store = storeOf(branch, scopes);
        if (store === undefined) return undefined;
        targets.push(store.target);
    }
    const reads: Node[] = [];
    traverse(statement.test, { Identifier: (path) => void reads.push(path.node) });
    return { statement, targets, reads, update: false, primitive: true };
};

/**
 * Stores to locals nothing reads (leftover flattening state, dead tables), also when the only reads are the tests of
 * `if`s that store to them (`guardedStoresOf`). Updates are allowed only when the local only ever holds primitives,
 * so their reads run no code. The declaration is then left to `removeUnusedLocals`.
 */
const removeDeadStores = (program: Node, scopes: ScopeInfo, log: PassContext["log"], out: Node[]): number => {
    if (scopes.manager.scopes.some((s) => s.type === "with")) return 0;
    // Fast exit: without a binding that is only ever written (or read in `if` tests), no walk.
    const candidate = scopes.manager.scopes.some((scope) =>
        scope.variables.some((v) => {
            const references = v.defs.length > 0 ? scopes.references(v) : undefined;
            return (
                references !== undefined &&
                references.some((reference) => reference.init !== true && reference.isWrite()) &&
                references.every((reference) => reference.init === true || reference.isWrite() || readInTest(reference.identifier as unknown as Node, scopes))
            );
        })
    );
    if (!candidate) return 0;
    const stores = new Map<Variable, Store[]>();
    const record = (store: Store): void => {
        const variables = new Set(store.targets.map((target) => scopes.variableOf(target)));
        const [variable] = variables;
        if (variables.size !== 1 || variable === undefined) return;
        const list = stores.get(variable);
        if (list === undefined) stores.set(variable, [store]);
        else list.push(store);
    };
    traverse(program, {
        ExpressionStatement(path) {
            const store = storeOf(path.node, scopes);
            if (store !== undefined) record({ statement: path.node, targets: [store.target], reads: [], update: store.update, primitive: store.primitive });
        },
        IfStatement(path) {
            const store = guardedStoresOf(path.node, scopes);
            if (store !== undefined) record(store);
        },
    });
    const env = constantEnv(scopes, log);
    const dead = new Set<Node>();
    for (const [v, list] of stores) {
        // A `var` only (each declaration of it): a store to a `let`/`const` before its declaration throws.
        if (v.defs.length === 0 || !v.defs.every((def) => def.type === "Variable" && (def.parent as { kind?: string } | null)?.kind === "var")) continue;
        const declarators = v.defs.map((def) => def.node as unknown as VariableDeclarator);
        if (!declarators.every((declarator) => declarator.init === null || isPlainPrimitive(declarator.init))) continue;
        // An update of an object would convert it (`valueOf`): updates only of primitives.
        if (list.some((store) => store.update) && !list.every((store) => store.primitive)) continue;
        const covered = new Set(list.flatMap((store) => [...store.targets, ...store.reads]));
        const references = scopes.references(v);
        if (references === undefined || !references.every((reference) => reference.init === true || covered.has(reference.identifier as unknown as Node))) continue;
        if (!ownBinding(v, env)) continue;
        for (const { statement } of list) dead.add(statement);
        log.debug(`removed ${list.length} store(s) to ${v.name}, which nothing reads`, list[0]?.statement);
    }
    if (dead.size === 0) return 0;
    let removed = 0;
    traverse(program, {
        enter(path) {
            if (!dead.has(path.node)) return;
            out.push(path.node);
            if (path.isInStatementList()) path.remove();
            else path.replace(at<Statement>({ type: "EmptyStatement" }, path.node));
            removed++;
            // A store inside a guarded one goes with it.
            path.skip();
        },
    });
    return removed;
};

/**
 * `var x = <literal>` followed by another literal write of `x`: the first is never seen. Only a literal: any other
 * value may run code that reads `x`.
 */
const overwritten = (declarator: VariableDeclarator | undefined, name: string | undefined, value: Node | null): boolean =>
    value?.type === "Literal" && declarator?.id.type === "Identifier" && declarator.id.name === name && (declarator.init === null || declarator.init.type === "Literal");

const declarationOf = (node: VariableDeclaration, declarations: VariableDeclarator[]): VariableDeclaration =>
    at<VariableDeclaration>({ type: "VariableDeclaration", kind: node.kind, declarations }, node);

/**
 * Declarations whose literal value is replaced right away (`var a = "", a = "keyCode";`), when the second value
 * doesn't read `x`. Both are in one statement list, so they name one binding. What `first` (and `second`, when
 * `consumed` is 2) become, or `undefined`.
 */
const mergeDeclaration = (first: Statement, second: Statement | undefined): { replacement: Statement[]; consumed: 1 | 2 } | undefined => {
    if (first.type !== "VariableDeclaration" || first.kind !== "var") return undefined;
    const kept = first.declarations.filter((declarator, i) => {
        const next = first.declarations[i + 1];
        return next === undefined || !overwritten(declarator, next.id.type === "Identifier" ? next.id.name : undefined, next.init);
    });
    if (kept.length < first.declarations.length) return { replacement: [declarationOf(first, kept)], consumed: 1 };
    const last = first.declarations.at(-1);
    if (second?.type === "VariableDeclaration" && second.kind === "var") {
        const [next] = second.declarations;
        if (next === undefined || !overwritten(last, next.id.type === "Identifier" ? next.id.name : undefined, next.init)) return undefined;
        const rest = first.declarations.slice(0, -1);
        return { replacement: rest.length === 0 ? [] : [declarationOf(first, rest)], consumed: 1 };
    }
    if (second?.type !== "ExpressionStatement" || second.expression.type !== "AssignmentExpression" || last === undefined) return undefined;
    const assignment = second.expression;
    if (assignment.operator !== "=" || assignment.left.type !== "Identifier" || !overwritten(last, assignment.left.name, assignment.right)) return undefined;
    const merged = at<VariableDeclarator>({ ...last, init: assignment.right }, last);
    return { replacement: [declarationOf(first, [...first.declarations.slice(0, -1), merged])], consumed: 2 };
};

/**
 * The dead initial values `mergeDeclaration` finds, in every statement list. Runs after the removals and alias
 * inlining: dropping a declarator of a name declared again changes what the scope analysis lists.
 */
const mergeOverwrittenDeclarations = (program: Node, log: PassContext["log"], facts: Facts): number => {
    let merged = 0;
    const mergeList = (list: Statement[]): void => {
        for (let i = 0; i < list.length; i++) {
            const merge = mergeDeclaration(list[i] as Statement, list[i + 1]);
            if (merge === undefined) continue;
            const originals = list.slice(i, i + merge.consumed);
            if (log.debugging) log.debug("merged a declaration whose value is overwritten at once", list[i] as Statement);
            facts.replaced(originals, merge.replacement);
            spliceList(list, i, merge.consumed, merge.replacement);
            i = Math.max(-1, i - 2);
            merged++;
        }
    };
    traverse(program, {
        enter(path) {
            const node = path.node;
            if (node.type === "Program" || node.type === "BlockStatement" || node.type === "StaticBlock") mergeList(node.body as Statement[]);
            else if (node.type === "SwitchCase") mergeList(node.consequent);
        },
    });
    if (merged > 0) log.info(`merged ${merged} declaration(s) whose initial value is overwritten at once`);
    return merged;
};
