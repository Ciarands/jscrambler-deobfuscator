import type { CallExpression, Expression, MemberExpression, Node, Program, Statement } from "../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../core/ast.js";
import { at } from "../core/build.js";
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
import { onlyTested, rootStatements } from "./emulate/storage.js";
import { DETECTOR_BUILDERS } from "./detectors.js";
import { keySets, mayName } from "./key-sets.js";
import { inlineStorageAliases } from "./storage-aliases.js";

/** An expression whose evaluation can't throw or have effects: literals, known bindings, functions, plain literals of those. */
const isPure = (node: Node | null | undefined, scopes: ScopeInfo): boolean => {
    if (node === null || node === undefined) return true;
    switch (node.type) {
        case "Literal":
        case "FunctionExpression":
        case "ArrowFunctionExpression":
            return true;
        case "Identifier": {
            // A binding that exists from its scope's start (no dead zone): a parameter, `var`, function declaration or
            // a function's `arguments`, resolved locally or (a script's own) globally. An undeclared name throws, as do
            // `let`/`const`/class bindings read before their declaration and `arguments` outside functions.
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
        default:
            return evaluate(node).ok;
    }
};

/** Script globals and module bindings (exports, or used by importers) are visible outside the program. */
const isLocalScope = (scopeType: string): boolean => scopeType !== "global" && scopeType !== "module";

/**
 * What a root statement is to the runtime:
 * - `def`: `G.k = ...`, removable when its right side has no effect outside the storage object;
 * - `stage`: a call into the runtime with constant arguments, or a bare read of it (decoder stages, code locks),
 *   affecting the state kept under `key`;
 * - `setup`: the call that defined the aliases;
 * - `fn`: a root function that may go when nothing that stays uses it.
 */
type Role =
    | { kind: "def"; key: string; removable: boolean }
    | { kind: "stage"; key: string; probe: { call: ResolveRequest } | { read: readonly string[] } }
    | { kind: "setup" }
    | { kind: "fn"; name: string }
    | { kind: "other" };

const isRemovable = (role: Role): boolean => (role.kind === "def" && role.removable) || role.kind === "stage" || role.kind === "setup" || role.kind === "fn";

const roleOf = (statement: Statement, runtime: RuntimeModel, isStorage: (n: Node) => boolean, scopes: ScopeInfo, detectorBuilders: ReadonlySet<Node> | undefined): Role => {
    if (runtime.setup.has(statement)) return { kind: "setup" };
    if (statement.type !== "ExpressionStatement") return { kind: "other" };
    const e = statement.expression;
    if (e.type === "AssignmentExpression" && e.operator === "=" && e.left.type === "MemberExpression" && isStorage(e.left.object)) {
        const key = propertyKey(e.left);
        if (key === undefined) return { kind: "other" };
        return { kind: "def", key, removable: isPure(e.right, scopes) || runtime.pure.has(statement) || detectorBuilders?.has(statement) === true };
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

/** A safety cap on cleanup's own repeats (each removal round can expose more unused code). */
const MAX_CLEANUP_ROUNDS = 16;

/**
 * Cleanup: remove the obfuscator's runtime once nothing needs it, and unused locals.
 *
 * Runtime (root statements of the prelude, decided per storage key):
 * - a definition `G.k = ...` goes when `k` is read nowhere that stays, and evaluating its right side had no effect
 *   outside the storage object (a function, a literal, or a statement the emulator saw run without touching
 *   builtins or globals), or it builds only anti-debug detectors (`DETECTOR_BUILDERS`: they go, semantic model 5);
 * - a stage call or code-lock read `G.k.m(1);` goes when the state it affects is dead, after the runtime shows it has
 *   no effect outside its own state (a re-run call changes no builtin, global or storage key; a read is of data
 *   properties only);
 * - the setup call goes when no alias name and no call-alias key is used any more; root functions only the removed
 *   statements referenced go with them, and the storage function when nothing references it.
 * Nothing of the runtime is removed when the storage object escapes (used as a value: passed, stored, exported), or
 * is read with a computed key, in code that stays and may run after the prelude: then any key could be read. A plain
 * computed read in code that runs only during the prelude (the decoder's name probe) keeps only what it may select:
 * definitions that ran before it with a key it can name (`selectable`).
 *
 * Locals (function scopes only; script and module bindings are visible outside): declarators nothing reads whose
 * initializer is pure, and function declarations nothing references.
 *
 * Last, other names for the storage object become its own name (`inlineStorageAliases`), so the output names the
 * runtime one way. That comes after the removals, which still need the scope analysis the new names are unknown to.
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
        // Removed code takes its references along, which can leave more unused: repeat until nothing more goes, with the
        // analysis refreshed in between (removed references dropped; no binding is added, so nothing else changes).
        for (let round = 0; ; round++) {
            if (round === MAX_CLEANUP_ROUNDS) {
                log.warn(`stopped after ${MAX_CLEANUP_ROUNDS} rounds; more may be removable`);
                break;
            }
            const removedRuntime = removeRuntime(program, model, facts.get(DECODER_PROOF), facts.get(DETECTOR_BUILDERS), scopes, log);
            const removedStores = removeDeadStores(program, scopes, log);
            const removedLocals = removeUnusedLocals(program, scopes, log);
            runtime += removedRuntime;
            locals += removedStores + removedLocals;
            if (removedRuntime + removedStores + removedLocals === 0) break;
            scopes.refresh(program);
        }
        const aliases = model === undefined ? 0 : inlineStorageAliases(model, storageAnalysis(program, model, scopes, log).matcher, scopes, log);
        // Removals only take declarations and references away (what a refresh of the analysis drops); the storage
        // name put in for aliases is a new reference the analysis doesn't know, so only that needs a new analysis.
        return { changed: runtime + locals + aliases, bindingsChanged: aliases > 0, stats: { runtime, locals, aliases } };
    },
};

/** `pure` and `setup` are keyed by the root statement and follow it through one-for-one replacements: one an earlier pass split or removed lost its fact. */
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
 * What the plain computed reads `G[k]` in prelude-only code (`computed`, by root statement) may select: added to
 * `reads` (and `aliasUses`, for the setup's call aliases) of their statements. Such a read runs only while the
 * prelude does, so it sees only what ran before it: a definition (or stage call) whose statement starts after the
 * read's code is done can't be what it selects. One that ran before it can, unless the read's key can't name it
 * (`keySets`: the decoder's probe tries permutations of a few characters). Returns, per statement no such read can
 * reach, why (for the log).
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

/** The target `[k, m]` a stage call reaches: through its wrapper, or directly. */
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

/** `literalEvalUses` by the code's literal and storage name: the code never changes, and cleanup asks every round. */
const evalUsesCache = new WeakMap<Node, { storage: string; uses: EvalUses | undefined }>();

/**
 * What the code of `eval("...")` (a string literal) uses. That code runs in the caller's scope and is this script's
 * own: jscrambler hides payloads there (reads of storage keys like `G[123]`), so its uses count where the eval call is. The
 * storage keys it reads, whether it uses the storage object otherwise (a computed key, a write, as a value), and every
 * name it mentions. Code that doesn't parse throws before running: it uses nothing.
 */
const literalEvalUses = (call: CallExpression, storage: string): EvalUses | undefined => {
    const [code] = call.arguments;
    // The first argument is the code; others are evaluated (like any argument, elsewhere) and ignored.
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
    log: PassContext["log"]
): number => {
    if (runtime === undefined) return 0;
    const body = rootStatements(runtime.root);
    if (body.length === 0) return 0;
    const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
    const { isStorage, aliases } = matcher;

    /** `var s = G` is harmless only when `s` is a real alias (written once): otherwise `s` can hold G under another name. */
    const isAliasDeclarator = (node: Node | null): boolean => {
        if (node?.type !== "VariableDeclarator" || node.id.type !== "Identifier") return false;
        const variable = scopes.variableOf(node.id);
        return variable !== undefined && aliases.has(variable);
    };

    // Per root statement: its role, the storage keys it reads, where the storage escapes in it (used as a value, or
    // read with a computed key) and where it still uses an alias or a global the setup added. Those only matter in
    // statements that stay: the decoder's own `G[name]` lookup goes with the decoder. Plain computed reads in code that
    // runs only during the prelude are kept apart (`computed`): see `selectable`.
    const roles = body.map((statement) => roleOf(statement, runtime, isStorage, scopes, detectorBuilders));
    const reads = body.map(() => new Set<string>());
    const names = body.map(() => new Set<string>());
    const escapes: (Node | undefined)[] = body.map(() => undefined);
    const aliasUses: (Node | undefined)[] = body.map(() => undefined);
    const computed = body.map((): MemberExpression[] => []);
    const aliasNames = new Set(runtime.aliases.map((a) => a.alias));
    // A setup global stays reachable only where code names it (model 9): by identifier, `.name` or a literal key.
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
                // Keeping G as a global isn't an escape: other scripts don't read it (model 2), and the program's own
                // uses of that name are effects the analysis reports.
                if (!asObject && !asDeclaration && !isAliasDeclarator(path.parent) && !path.isWriteTarget() && !onlyTested(path) && !effects.keptAsGlobal(node)) escapes[index] ??= node;
            },
        });
    }
    const unreachable = selectable(body, roles, computed, reads, aliasUses, runtime, scopes, effects);

    // Root functions: removable when they're locals (root is an IIFE), the storage function, or referenced by runtime
    // statements. Other top-level functions of a script are globals other code may call: they stay.
    const runtimeNames = new Set<string>();
    for (const [index, role] of roles.entries()) if (role.kind !== "other") for (const name of names[index] ?? []) runtimeNames.add(name);
    for (const [index, statement] of body.entries()) {
        if (statement.type !== "FunctionDeclaration" || statement.id === null) continue;
        const name = statement.id.name;
        if (runtime.root.type !== "Program" || name === runtime.storage || runtimeNames.has(name)) roles[index] = { kind: "fn", name };
    }

    // Liveness: what ordinary statements need, transitively. Definitions and stage calls stay when their key is live,
    // functions when their name is used, the setup call when an alias still is.
    let kept = new Set<number>();
    /** The statement that made each key live, for the log. */
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
            // A call's own run must have been pure too: a re-run shows nothing for code that acts only once (a lock's
            // checks). A templated decoder's stage call needs neither: its template shows it writes only the decoder's
            // own state, reachable only through the key that is dead here (relies on model 7: builtins intact).
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
        body.splice(index, 1);
    }
    if (dropped.length > 0) log.info(`removed ${dropped.length} runtime statement(s)`);
    return dropped.length;
};

/** Why each definition `G.k = ...` stays or goes. */
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

/**
 * Whether `variable` may be used where the reference lists can't show it. `with` makes every name lookup inside it
 * dynamic (checked once for the program); a direct eval can see the variables of the scopes around it, and
 * eslint-scope marks each of those `dynamic` (its own references there stay unresolved too).
 */
const hiddenUses = (variable: Variable): boolean => variable.scope.dynamic;

const removeUnusedLocals = (program: Node, scopes: ScopeInfo, log: PassContext["log"]): number => {
    const within = scopes.manager.scopes.find((s) => s.type === "with");
    if (within !== undefined) {
        log.info("the program uses with; unused locals stay", within.block as unknown as Node);
        return 0;
    }
    // Candidates first, then which go: a candidate goes when every use but its own initialization is inside code that
    // goes too, so whole chains (`var a = b; var b = 1;`) go in one pass instead of one per analysis refresh.
    const candidates: { node: Node; variable: Variable; body: Node | null }[] = [];
    traverse(program, {
        VariableDeclaration(path) {
            const parent = path.parent;
            // A for-in/of head's binding is the loop's assignment target: it stays even when nothing reads it.
            if ((parent?.type === "ForInStatement" || parent?.type === "ForOfStatement") && path.key === "left") return;
            for (const declarator of path.node.declarations) {
                if (declarator.id.type !== "Identifier") continue;
                const variable = scopes.variableOf(declarator.id);
                if (variable === undefined || !isLocalScope(variable.scope.type) || variable.defs.length !== 1 || hiddenUses(variable) || !isPure(declarator.init, scopes)) continue;
                candidates.push({ node: declarator, variable, body: declarator.init });
            }
        },
        FunctionDeclaration(path) {
            const node = path.node as Node;
            if (node.type !== "FunctionDeclaration" || node.id === null) return;
            // Only directly in a function body: sloppy-mode block functions are also visible outside their block
            // (Annex B), which the scope analysis doesn't model.
            const inFunctionBody = path.parent?.type === "BlockStatement" && isFunctionNode(path.parentPath?.parent);
            if (!path.isInStatementList() || !inFunctionBody) return;
            const variable = scopes.variableOf(node.id);
            if (variable === undefined || !isLocalScope(variable.scope.type) || variable.defs.length !== 1 || hiddenUses(variable)) return;
            candidates.push({ node, variable, body: node });
        },
    });
    const dead = new Set<Node>();
    /** Identifiers inside code that goes: their references no longer count. */
    const gone = new Set<Node>();
    for (let changed = true; changed;) {
        changed = false;
        for (const candidate of candidates) {
            if (dead.has(candidate.node) || !candidate.variable.references.every((reference) => reference.init || gone.has(reference.identifier as unknown as Node))) continue;
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
                removed++;
            },
        },
    });
    if (removed > 0) log.info(`removed ${removed} unused local declaration(s)`);
    return removed;
};

/**
 * A literal, or a minus on one (`-5`: negating a primitive runs no code), whose value no update can throw on: not a
 * regex (an object), not a BigInt (`1n + 1` throws).
 */
const isPlainPrimitive = (node: Node | null): boolean => {
    const literal = node?.type === "UnaryExpression" && node.operator === "-" ? node.argument : node;
    return literal?.type === "Literal" && !(literal.value instanceof RegExp) && typeof literal.value !== "bigint" && !("bigint" in literal && literal.bigint !== undefined && literal.bigint !== null);
};

/** `x = <primitive>;`, `x += <primitive>;`, `x++;` as a statement: what it does to its local. */
const storeOf = (statement: Node): { target: Node; update: boolean } | undefined => {
    if (statement.type !== "ExpressionStatement") return undefined;
    const e = statement.expression;
    if (e.type === "UpdateExpression") return e.argument.type === "Identifier" ? { target: e.argument, update: true } : undefined;
    if (e.type !== "AssignmentExpression" || e.left.type !== "Identifier" || !isPlainPrimitive(e.right)) return undefined;
    return { target: e.left, update: e.operator !== "=" };
};

/**
 * Stores to locals nothing reads: jscrambler's leftover flattening state (`a = 576049076; S = 2; Z0 += 2; u4++;`).
 * A local qualifies when it has one declaration with a primitive (or no) initializer and every other reference is a
 * statement of its own that stores a primitive (`x = 1;`) or updates it with one (`x += 2;`, `x++`). Its value is
 * then always a primitive, so the reads the updates make run no code, and nothing else ever sees it: the statements
 * go, and the declaration is left with no use for `removeUnusedLocals`.
 */
const removeDeadStores = (program: Node, scopes: ScopeInfo, log: PassContext["log"]): number => {
    if (scopes.manager.scopes.some((s) => s.type === "with")) return 0;
    /** Store statements by the variable they store to. */
    const stores = new Map<Variable, Node[]>();
    traverse(program, {
        ExpressionStatement(path) {
            const store = storeOf(path.node);
            const variable = store === undefined ? undefined : scopes.variableOf(store.target);
            if (variable === undefined) return;
            const list = stores.get(variable);
            if (list === undefined) stores.set(variable, [path.node]);
            else list.push(path.node);
        },
    });
    const dead = new Set<Node>();
    for (const [v, statements] of stores) {
        const [def] = v.defs;
        // A `var` only: a store to a `let`/`const` before its declaration throws.
        if (!isLocalScope(v.scope.type) || v.defs.length !== 1 || def?.type !== "Variable" || (def.parent as { kind?: string } | null)?.kind !== "var" || hiddenUses(v)) continue;
        const declarator = def.node as unknown as { init: Node | null };
        if (declarator.init !== null && !isPlainPrimitive(declarator.init)) continue;
        const targets = new Set(statements.map((statement) => (storeOf(statement) as { target: Node }).target));
        if (!v.references.every((reference) => reference.init === true || targets.has(reference.identifier as unknown as Node))) continue;
        for (const statement of statements) dead.add(statement);
        log.debug(`removed ${statements.length} store(s) to ${v.name}, which nothing reads`, statements[0]);
    }
    if (dead.size === 0) return 0;
    traverse(program, {
        ExpressionStatement(path) {
            if (!dead.has(path.node)) return;
            if (path.isInStatementList()) path.remove();
            else path.replace(at<Statement>({ type: "EmptyStatement" }, path.node));
        },
    });
    return dead.size;
};
