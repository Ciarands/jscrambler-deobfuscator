import type { CallExpression, Expression, MemberExpression, Node, Program, Statement, VariableDeclarator } from "../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../core/ast.js";
import { at } from "../core/build.js";
import { constantEnv } from "../core/constants.js";
import type { ConstantEnv } from "../core/constants.js";
import type { Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import { parse, ParseError } from "../core/parse.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { ResolveRequest } from "./emulate/guest.js";
import type { RuntimeModel } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import { parentsWithin } from "./emulate/builders.js";
import type { DecoderProof } from "./emulate/decoder.js";
import { DECODER_PROOF } from "./emulate/decoder.js";
import type { StorageEffects } from "./emulate/effects.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { StorageMatcher } from "./emulate/storage.js";
import { onlyTested, rootStatements, storageMatcher } from "./emulate/storage.js";
import { DETECTOR_BUILDERS } from "./detectors.js";
import { keySets, mayName } from "./key-sets.js";
import { inlineStorageAliases } from "./storage-aliases.js";

/** Evaluation can't throw or have effects. */
const isPure = (node: Node | null | undefined, scopes: ScopeInfo): boolean => {
    if (node === null || node === undefined) return true;
    switch (node.type) {
        case "Literal":
        case "FunctionExpression":
        case "ArrowFunctionExpression":
            return true;
        case "Identifier": {
            // Only bindings with no dead zone: an undeclared name, or `let`/`const`/class read early, throws.
            const variable = scopes.variableOf(node) ?? scopes.staticVariableOf(node);
            if (variable === undefined) return false;
            if (variable.name === "arguments" && variable.defs.length === 0) return variable.scope.type === "function";
            return (
                variable.defs.length > 0 &&
                variable.defs.every(
                    (def) =>
                        def.type === "FunctionName" || def.type === "Parameter" || def.type === "CatchClause" || (def.type === "Variable" && (def.parent as { kind?: string } | null)?.kind === "var")
                )
            );
        }
        case "ArrayExpression":
            return node.elements.every((e) => e === null || (e.type !== "SpreadElement" && isPure(e, scopes)));
        case "ObjectExpression":
            return node.properties.every((p) => p.type === "Property" && !p.computed && p.kind === "init" && isPure(p.value, scopes));
        case "CallExpression":
            return isPureBuilderCall(node, scopes);
        default:
            return evaluate(node).ok;
    }
};

/**
 * `(() => { var t; t = {}; t.a = x; return t; })()` (how jscrambler builds object literals): a call with no arguments
 * of a function literal without parameters whose body only declares `var`s, gives one of them a plain literal, sets
 * static keys of it (not `__proto__`) to pure values and returns something pure. It changes nothing but its fresh
 * object (model 7: no setter on Object.prototype but `__proto__`'s) and can't throw: the holder is the body's own
 * `var`, holding the literal by then. (An async or generator body runs at most this, and throws into its result.)
 */
const isPureBuilderCall = (node: CallExpression, scopes: ScopeInfo): boolean => {
    const fn = node.callee;
    if (node.arguments.length > 0 || (fn.type !== "ArrowFunctionExpression" && fn.type !== "FunctionExpression")) return false;
    if (fn.params.length > 0 || fn.body?.type !== "BlockStatement") return false;
    const body = fn.body.body;
    const last = body.at(-1);
    if (last?.type !== "ReturnStatement") return false;
    // Every top-level `var` of the body is its own (hoisted); a `let`/`const` holds nothing a store may use below.
    const own = new Set(
        body.flatMap((statement) => (statement.type === "VariableDeclaration" && statement.kind === "var" ? statement.declarations.map((d) => (d.id.type === "Identifier" ? d.id.name : "")) : []))
    );
    let holder: string | undefined;
    const assigns = (target: Node, value: Node | null): boolean => {
        if (value !== null && !isPure(value, scopes)) return false;
        if (target.type === "Identifier" && own.has(target.name)) {
            // A `__proto__` property sets a prototype, whose setters a later store could run.
            const plain =
                value?.type === "ObjectExpression" &&
                value.properties.every((p) => p.type === "Property" && !(p.key.type === "Identifier" ? p.key.name === "__proto__" : p.key.type === "Literal" && p.key.value === "__proto__"));
            holder = plain ? target.name : holder === target.name ? undefined : holder;
            return true;
        }
        if (target.type !== "MemberExpression" || target.object.type !== "Identifier" || target.object.name !== holder) return false;
        const key = propertyKey(target);
        return key !== undefined && key !== "__proto__";
    };
    for (const statement of body.slice(0, -1)) {
        if (statement.type === "VariableDeclaration") {
            if (!statement.declarations.every((d) => d.id.type === "Identifier" && (d.init === null || assigns(d.id, d.init)))) return false;
            continue;
        }
        const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
        if (e?.type !== "AssignmentExpression" || e.operator !== "=" || !assigns(e.left, e.right)) return false;
    }
    return isPure(last.argument, scopes);
};

const isLocalScope = (scopeType: string): boolean => scopeType !== "global" && scopeType !== "module";

/**
 * - `def`: `G.k = ...`; removable when its right side has no effect outside the storage object;
 * - `stage`: a runtime call with constant arguments, or a bare read (decoder stages, code locks), affecting `key`;
 * - `setup`: the call that defined the aliases; goes once no alias name or call-alias key is used;
 * - `fn`: a root function; goes once only removed statements name it;
 * - `store`: `globalThis.P = G`; other scripts don't read it (model 2).
 */
type Role =
    | { kind: "def"; key: string; removable: boolean }
    | { kind: "stage"; key: string; probe: { call: ResolveRequest } | { read: readonly string[] } }
    | { kind: "setup" }
    | { kind: "fn"; name: string }
    | { kind: "store" }
    | { kind: "other" };

const isRemovable = (role: Role): boolean => (role.kind === "def" && role.removable) || role.kind === "stage" || role.kind === "setup" || role.kind === "fn" || role.kind === "store";

const roleOf = (
    statement: Statement,
    runtime: RuntimeModel,
    isStorage: (n: Node) => boolean,
    keptAsGlobal: (n: Node) => boolean,
    scopes: ScopeInfo,
    detectorBuilders: ReadonlySet<Node> | undefined
): Role => {
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
            return { kind: "def", key, removable: isPure(e.right, scopes) || runtime.pure.has(statement) || detectorBuilders?.has(statement) === true };
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
    const args: Value[] = [];
    for (const arg of e.arguments) {
        const value = arg.type === "SpreadElement" ? undefined : evaluate(arg);
        if (value === undefined || !value.ok) return { kind: "other" };
        args.push(value.value);
    }
    return { kind: "stage", key: affected, probe: { call: { path: path.keys, args } } };
};

const MAX_CLEANUP_ROUNDS = 16;

/**
 * Removes the runtime once nothing needs it, and unused locals.
 *
 * A definition goes when its key is dead and its right side had no effect outside the storage object, or it only
 * builds anti-debug detectors (model 5). A stage call goes when its state is dead and it is shown effect-free. Nothing
 * goes when the storage object escapes or is read with a computed key in code that may run after the prelude; a
 * computed read in prelude-only code keeps only what it may select (`selectable`).
 *
 * Storage aliases are inlined last: the removals need the scope analysis, which doesn't know the new names.
 */
export const cleanup: Pass = {
    name: "cleanup",
    description: "Remove the dead runtime (decoder, wrappers, setup, prelude calls) and unused locals",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const scopes = scope();
        const model = facts.get(RUNTIME);
        if (model !== undefined && log.debugging) logLostFacts(model, log);
        let runtime = 0;
        let locals = 0;
        // Removals can expose more unused code; `forget` updates the analysis in between.
        let runtimeDirty = true;
        for (let round = 0; ; round++) {
            if (round === MAX_CLEANUP_ROUNDS) {
                log.warn(`stopped after ${MAX_CLEANUP_ROUNDS} rounds; more may be removable`);
                break;
            }
            const removed: Node[] = [];
            const removedRuntime: number = runtimeDirty ? removeRuntime(program, model, facts.get(DECODER_PROOF), facts.get(DETECTOR_BUILDERS), scopes, log, removed) : 0;
            const removedStores = removeDeadStores(program, scopes, log, removed);
            const removedLocals = removeUnusedLocals(program, scopes, log, removed);
            runtime += removedRuntime;
            locals += removedStores + removedLocals;
            if (removedRuntime + removedStores + removedLocals === 0) break;
            runtimeDirty = removedRuntime > 0 || (model !== undefined && namesRuntime(removed, model, storageMatcher(program, model, scopes)));
            scopes.forget(removed);
        }
        const aliases = model === undefined ? 0 : inlineStorageAliases(model, storageAnalysis(program, model, scopes, log).matcher, scopes, log);
        // Only the inlined storage name is a reference the analysis doesn't know.
        return { changed: runtime + locals + aliases, bindingsChanged: aliases > 0, stats: { runtime, locals, aliases } };
    },
};

/** Removing code that doesn't name the runtime leaves every runtime statement's liveness unchanged. */
const namesRuntime = (removed: readonly Node[], runtime: RuntimeModel, matcher: StorageMatcher): boolean => {
    const names = new Set<string>([runtime.storage, ...[...matcher.aliases].map((variable) => variable.name), ...runtime.aliases.map((alias) => alias.alias), ...runtime.setupGlobals]);
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

/** `pure` and `setup` are keyed by root statement; an earlier pass splitting or removing one loses its fact. */
const logLostFacts = (runtime: RuntimeModel, log: PassContext["log"]): void => {
    const body = new Set<Node>(rootStatements(runtime.root));
    for (const [name, recorded] of [
        ["pure", runtime.pure],
        ["setup", runtime.setup],
    ] as const) {
        const lost = [...recorded].filter((statement) => !body.has(statement));
        if (lost.length > 0) log.debug(`${lost.length} of ${recorded.size} recorded ${name} statement(s) are no longer root statements (split or removed by an earlier pass)`, lost[0]);
    }
};

/**
 * A computed read `G[k]` in prelude-only code sees only what ran before it, and only keys `keySets` says it can name.
 * Adds what it may select to `reads`/`aliasUses`; returns why each other statement is unreachable (for the log).
 */
const selectable = (
    body: readonly Statement[],
    roles: readonly Role[],
    computed: readonly (readonly MemberExpression[])[],
    reads: readonly Set<string>[],
    aliasUses: (Node | undefined)[],
    runtime: RuntimeModel,
    scopes: ScopeInfo,
    effects: StorageEffects
): Map<number, string> => {
    const unreachable = new Map<number, string>();
    const reachable = new Set<number>();
    for (const [index, list] of computed.entries()) {
        if (list.length === 0) continue;
        const statement = body[index] as Statement;
        const keysOf = keySets(scopes, parentsWithin(statement));
        for (const read of list) {
            const keys = keysOf(read.property as Expression);
            for (const [other, role] of roles.entries()) {
                if (role.kind !== "def" && role.kind !== "stage" && role.kind !== "setup") continue;
                if (effects.runsBefore(read.object, body[other] as Node)) {
                    if (!unreachable.has(other)) unreachable.set(other, "a computed read of the runtime is done before it runs");
                    continue;
                }
                const names = role.kind === "setup" ? [...runtime.setupKeys] : [role.key];
                if (keys !== undefined && !names.some((name) => mayName(keys, name))) {
                    if (!unreachable.has(other)) unreachable.set(other, "a computed read of the runtime can't select its key");
                    continue;
                }
                reachable.add(other);
                if (role.kind === "setup") aliasUses[index] ??= read;
                else reads[index]?.add(role.key);
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

interface EvalUses {
    readonly keys: Set<string>;
    escape: boolean;
    readonly names: Set<string>;
}

/** Cached per literal: cleanup asks every round. */
const evalUsesCache = new WeakMap<Node, { storage: string; uses: EvalUses | undefined }>();

/**
 * `eval("...")` code runs in the caller's scope and jscrambler hides storage reads there, so its uses count at the
 * call. Unparsable code throws before running: it uses nothing.
 */
const literalEvalUses = (call: CallExpression, storage: string): EvalUses | undefined => {
    const [code] = call.arguments;
    if (code?.type !== "Literal" || typeof code.value !== "string") return undefined;
    const cached = evalUsesCache.get(code);
    if (cached?.storage === storage) return cached.uses;
    let parsed: Program;
    try {
        parsed = parse(code.value);
    } catch (error) {
        if (!(error instanceof ParseError)) throw error;
        evalUsesCache.set(code, { storage, uses: undefined });
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
    evalUsesCache.set(code, { storage, uses });
    return uses;
};

const removeRuntime = (
    program: Node,
    runtime: RuntimeModel | undefined,
    decoders: DecoderProof | undefined,
    detectorBuilders: ReadonlySet<Node> | undefined,
    scopes: ScopeInfo,
    log: PassContext["log"],
    removed: Node[]
): number => {
    if (runtime === undefined) return 0;
    const body = rootStatements(runtime.root);
    if (body.length === 0) return 0;
    const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
    const { isStorage, aliases } = matcher;

    /** Only a real alias (written once) is harmless: otherwise `s` can hold G under another name. */
    const isAliasDeclarator = (node: Node | null): boolean => {
        if (node?.type !== "VariableDeclarator" || node.id.type !== "Identifier") return false;
        const variable = scopes.variableOf(node.id);
        return variable !== undefined && aliases.has(variable);
    };

    // Escapes and alias uses only matter in statements that stay; prelude-only computed reads go to `selectable`.
    const roles = body.map((statement) => roleOf(statement, runtime, isStorage, (node) => effects.keptAsGlobal(node), scopes, detectorBuilders));
    const reads = body.map(() => new Set<string>());
    const names = body.map(() => new Set<string>());
    const escapes: (Node | undefined)[] = body.map(() => undefined);
    const aliasUses: (Node | undefined)[] = body.map(() => undefined);
    const computed = body.map((): MemberExpression[] => []);
    const aliasNames = new Set(runtime.aliases.map((a) => a.alias));
    // A setup global stays reachable only where code names it (model 9).
    const { setupGlobals } = runtime;
    for (const [index, statement] of body.entries()) {
        const role = roles[index] as Role;
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
                if (key !== undefined && !node.computed && aliasNames.has(key)) aliasUses[index] ??= node;
                if (key !== undefined && setupGlobals.has(key)) aliasUses[index] ??= node;
                if (!isStorage(node.object)) return;
                if (key === undefined) {
                    // A call would hand `G` on as `this`.
                    const called = (path.parent?.type === "CallExpression" && path.key === "callee") || (path.parent?.type === "TaggedTemplateExpression" && path.key === "tag");
                    if (!called && !path.isWriteTarget() && effects.runsOnlyInPrelude(functions.at(-1))) computed[index]?.push(node);
                    else escapes[index] ??= node;
                    return;
                }
                const isDefTarget = role.kind === "def" && path.parent === (statement as { expression?: Node }).expression && path.key === "left";
                if (!isDefTarget && !path.isWriteTarget()) reads[index]?.add(key);
                if (runtime.callAliases.has(key)) aliasUses[index] ??= node;
            },
            CallExpression(path) {
                const call = path.node;
                if (call.callee.type !== "Identifier" || call.callee.name !== "eval" || scopes.nameBoundAt(call.callee, "eval") !== false) return;
                const uses = literalEvalUses(call, runtime.storage);
                if (uses === undefined) return;
                for (const key of uses.keys) reads[index]?.add(key);
                for (const name of uses.names) {
                    names[index]?.add(name);
                    if (aliasNames.has(name) || setupGlobals.has(name)) aliasUses[index] ??= call;
                }
                if (uses.escape) escapes[index] ??= call;
            },
            Identifier(path) {
                const node = path.node;
                if (scopes.referenceOf(node) !== undefined) names[index]?.add(node.name);
                if ((aliasNames.has(node.name) || setupGlobals.has(node.name)) && scopes.isGlobalReference(node)) aliasUses[index] ??= node;
                if (!isStorage(node)) return;
                const asObject = path.parent?.type === "MemberExpression" && path.key === "object";
                const asDeclaration = path.parent?.type === "FunctionDeclaration" && path.key === "id";
                // Keeping G as a global isn't an escape (model 2).
                if (!asObject && !asDeclaration && !isAliasDeclarator(path.parent) && !path.isWriteTarget() && !onlyTested(path) && !effects.keptAsGlobal(node)) escapes[index] ??= node;
            },
        });
    }
    const unreachable = selectable(body, roles, computed, reads, aliasUses, runtime, scopes, effects);

    // Other top-level functions of a script are globals other code may call: they stay.
    const runtimeNames = new Set<string>();
    for (const [index, role] of roles.entries()) if (role.kind !== "other") for (const name of names[index] ?? []) runtimeNames.add(name);
    for (const [index, statement] of body.entries()) {
        if (statement.type !== "FunctionDeclaration" || statement.id === null) continue;
        const name = statement.id.name;
        if (runtime.root.type !== "Program" || name === runtime.storage || runtimeNames.has(name)) roles[index] = { kind: "fn", name };
    }

    let kept = new Set<number>();
    const liveBy = new Map<string, number>();
    for (let settled = false; !settled;) {
        settled = true;
        const byKey = new Map<string, number[]>();
        const byName = new Map<string, number[]>();
        for (const [index, role] of roles.entries()) {
            if ((role.kind === "def" && role.removable) || role.kind === "stage") byKey.set(role.key, [...(byKey.get(role.key) ?? []), index]);
            if (role.kind === "fn") byName.set(role.name, [...(byName.get(role.name) ?? []), index]);
        }
        kept = new Set<number>();
        liveBy.clear();
        const live = new Set<string>();
        const used = new Set<string>();
        const work: number[] = [];
        const keep = (index: number) => {
            if (kept.has(index)) return;
            kept.add(index);
            work.push(index);
        };
        const drain = () => {
            for (let index = work.pop(); index !== undefined; index = work.pop()) {
                for (const key of reads[index] ?? []) {
                    if (live.has(key)) continue;
                    live.add(key);
                    liveBy.set(key, index);
                    for (const other of byKey.get(key) ?? []) keep(other);
                }
                for (const name of names[index] ?? []) {
                    if (used.has(name)) continue;
                    used.add(name);
                    for (const other of byName.get(name) ?? []) keep(other);
                }
            }
        };
        for (const [index, role] of roles.entries()) if (!isRemovable(role)) keep(index);
        drain();
        const aliasUse = [...kept].map((index) => aliasUses[index]).find((node) => node !== undefined);
        if (aliasUse !== undefined) {
            log.debug("setup call stays: an alias is still used", aliasUse);
            for (const [index, role] of roles.entries()) if (role.kind === "setup") keep(index);
            drain();
        }

        const escape = [...kept].map((index) => escapes[index]).find((node) => node !== undefined);
        if (escape !== undefined) {
            log.info(`the storage object ${runtime.storage} escapes or is read with a computed key in code that stays; the runtime stays`, escape);
            return 0;
        }
        // Stage calls about to go must be effect-free; ones that aren't become ordinary statements.
        for (const [index, role] of roles.entries()) {
            if (role.kind !== "stage" || kept.has(index)) continue;
            // A re-run shows nothing for code that acts once (a lock's checks), so its own run must be pure too. A
            // templated decoder writes only its own, dead, state (model 7: builtins intact).
            const harmless =
                "read" in role.probe
                    ? runtime.guest.inspect(role.probe.read)?.data === true
                    : decoders?.templated.has(targetId(runtime, role.probe.call.path)) === true || (runtime.pure.has(body[index] as Node) && runtime.guest.effectFree(role.probe.call));
            if (harmless) continue;
            roles[index] = { kind: "other" };
            settled = false;
            log.debug("kept: runtime call has effects outside its own state", body[index]);
        }
    }

    const dropped = [...roles.keys()].filter((index) => !kept.has(index));
    if (log.debugging) logDefinitions(roles, kept, liveBy, unreachable, body, runtime.storage, log);
    for (const index of dropped.toReversed()) {
        log.debug(`removed runtime statement (${roles[index]?.kind})`, body[index]);
        removed.push(...body.splice(index, 1));
    }
    if (dropped.length > 0) log.info(`removed ${dropped.length} runtime statement(s)`);
    return dropped.length;
};

const logDefinitions = (
    roles: readonly Role[],
    kept: ReadonlySet<number>,
    liveBy: ReadonlyMap<string, number>,
    unreachable: ReadonlyMap<number, string>,
    body: readonly Statement[],
    storage: string,
    log: PassContext["log"]
): void => {
    for (const [index, role] of roles.entries()) {
        if (role.kind !== "def") continue;
        const name = `${storage}[${JSON.stringify(role.key)}]`;
        const reader = liveBy.get(role.key);
        const because = !kept.has(index)
            ? `goes: nothing that stays reads ${name}${unreachable.has(index) ? ` (${unreachable.get(index)})` : ""}`
            : !role.removable
              ? "stays: its right side may have effects outside the storage object"
              : `stays: ${name} is read by root statement ${reader ?? "?"}, which stays`;
        log.debug(`definition ${because}`, body[index]);
    }
};

/** `with` is checked once per program; a direct eval marks the scopes around it `dynamic`. */
const hiddenUses = (variable: Variable): boolean => variable.scope.dynamic;

/** The refreshed (not rebuilt) analysis still lists these; skipping them avoids a useless next round. */
const removedDeclarations = new WeakSet<Node>();

/** `x = <pure>`, or a bare `x` that isn't a for-in/of head (the loop writes that one: an init reference at its id). */
const removableDeclarator = (node: Node, variable: Variable, scopes: ScopeInfo): node is VariableDeclarator =>
    node.type === "VariableDeclarator" &&
    node.id.type === "Identifier" &&
    isPure(node.init, scopes) &&
    (node.init !== null || !variable.references.some((reference) => reference.init === true && (reference.identifier as unknown as Node) === node.id));

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
            if (dead.has(candidate.node) || !candidate.variable.references.every((reference) => reference.init || gone.has(reference.identifier as unknown as Node))) continue;
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
                out.push(...unused);
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

/** No update can throw on it or run code: not a regex, not a BigInt (`1n + 1` throws). */
const isPlainPrimitive = (node: Node | null): boolean => {
    const literal = node?.type === "UnaryExpression" && node.operator === "-" ? node.argument : node;
    return literal?.type === "Literal" && !(literal.value instanceof RegExp) && typeof literal.value !== "bigint" && !("bigint" in literal && literal.bigint !== undefined && literal.bigint !== null);
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

const mayBeOwn = (variable: Variable): boolean => (isLocalScope(variable.scope.type) ? !hiddenUses(variable) : variable.scope.type === "global");

const isStoredTo = (variable: Variable): boolean => variable.references.some((reference) => reference.init !== true && reference.isWrite());

/** Can't throw or run code: strict comparisons (no conversion), `!`, `&&`/`||`/`??` of pure operands. */
const isPureTest = (node: Node, scopes: ScopeInfo): boolean => {
    switch (node.type) {
        case "BinaryExpression":
            return (node.operator === "===" || node.operator === "!==") && isPureTest(node.left as Node, scopes) && isPureTest(node.right, scopes);
        case "LogicalExpression":
            return isPureTest(node.left, scopes) && isPureTest(node.right, scopes);
        case "UnaryExpression":
            return node.operator === "!" && isPureTest(node.argument, scopes);
        default:
            return isPure(node, scopes);
    }
};

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
        scope.variables.some(
            (v) =>
                v.defs.length > 0 && isStoredTo(v) && v.references.every((reference) => reference.init === true || reference.isWrite() || readInTest(reference.identifier as unknown as Node, scopes))
        )
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
        if (!v.references.every((reference) => reference.init === true || covered.has(reference.identifier as unknown as Node))) continue;
        if (!ownBinding(v, env)) continue;
        for (const { statement } of list) dead.add(statement);
        log.debug(`removed ${list.length} store(s) to ${v.name}, which nothing reads`, list[0]?.statement);
    }
    if (dead.size === 0) return 0;
    traverse(program, {
        enter(path) {
            if (!dead.has(path.node)) return;
            out.push(path.node);
            if (path.isInStatementList()) path.remove();
            else path.replace(at<Statement>({ type: "EmptyStatement" }, path.node));
            // A store inside a guarded one goes with it (and counts, as in the log).
            path.skip();
        },
    });
    return dead.size;
};
