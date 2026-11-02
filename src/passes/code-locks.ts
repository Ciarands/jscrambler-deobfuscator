import type { Function as FunctionNode, MemberExpression, Node, Statement } from "../core/ast.js";
import { valueToNode } from "../core/build.js";
import type { Primitive } from "../core/build.js";
import type { ScopeInfo } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { factKey } from "../pipeline/facts.js";
import type { ResolveResult } from "./emulate/guest.js";
import type { Builder, Slot } from "./emulate/builders.js";
import { bodyOf, builderOf, definitionOf, returnsOf, sameSlot, slotOf, slotsOnly } from "./emulate/builders.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { Staleness, StorageEffects } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import type { RuntimeModel } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import type { StorageMatcher } from "./emulate/storage.js";
import { assignedPaths, storageMatcher } from "./emulate/storage.js";
import { localityOf } from "./locality.js";
import type { CallSite } from "./storage-usage.js";
import { HolderReach, isGlobalRead, rewriteCalls, survey } from "./storage-usage.js";

type FastPath =
    | {
          readonly ok: true;
          readonly answer: Primitive;
          readonly method: FunctionNode;
          readonly cache: Slot;
          readonly parents: ReadonlyMap<Node, Node>;
          /** Every return gives the answer: a call answers it whether the cache is set or not (when it returns). */
          readonly constant: boolean;
      }
    | { readonly ok: false; readonly reason: string; readonly node: Node };

const refused = (reason: string, node: Node): FastPath => ({ ok: false, reason, node });

const isPrimitiveLiteral = (node: Node | null | undefined): node is Node & { type: "Literal"; value: Primitive } =>
    node?.type === "Literal" && (node.value === null || typeof node.value === "string" || typeof node.value === "number" || typeof node.value === "boolean");

/**
 * The cached answer of the code lock `method` that `iife` builds, proven from its code:
 *
 *     G.k = function () { var S = [arguments]; S[j] = undefined; S[i] = {}; S[i].method = function () {
 *         var X = [arguments];
 *         if (S[j]) return L;                  // the answer, once the cache is set
 *         ...checks...; S[j] = 15; return 91;  // the first call: checks, sets the cache
 *     }; return S[i]; }();
 *
 * (or the methods in a returned object literal). The cache is a slot of an array the builder declares and keeps to
 * itself. Once set, nothing clears it (its only writes are the builder's own top-level statements, which ran once,
 * and truthy literals the method stores at its own top level), so every later call returns `L` and does nothing else.
 * The method's other returns are literals other than `L`: a call that answers `L` took the cached path.
 */
const fastPathOf = (iife: FunctionNode, builder: Builder | string, method: string, scopes: ScopeInfo): FastPath => {
    if (typeof builder === "string") return refused(builder, iife);
    const fn = builder.methods.get(method);
    if (fn === undefined) return refused(`its builder gives it no plain function ${method}`, iife);
    if (fn.async || fn.generator) return refused(`${method} is async or a generator`, fn);

    const statements = bodyOf(fn);
    let first = 0;
    while (
        statements[first]?.type === "VariableDeclaration" &&
        (statements[first] as Statement & { type: "VariableDeclaration" }).declarations.every((d) => d.init === null || d.init.type === "ArrayExpression")
    )
        first++;
    const check = statements[first];
    if (check?.type !== "IfStatement" || check.alternate !== null) return refused(`${method} doesn't start with a cache check`, fn);
    const taken = check.consequent.type === "BlockStatement" && check.consequent.body.length === 1 ? check.consequent.body[0] : check.consequent;
    if (taken?.type !== "ReturnStatement" || !isPrimitiveLiteral(taken.argument)) return refused(`${method}'s cache check doesn't return a literal`, check);
    const answer = taken.argument.value;
    const cache = slotOf(check.test, scopes);
    if (cache === undefined || (cache.variable.scope.block as unknown as Node) !== iife || !slotsOnly(cache.variable, scopes, builder.parents)) {
        return refused(`${method}'s cache isn't a slot of an array its builder keeps to itself`, check.test);
    }

    // Writes to the cache: the builder's own statements, and truthy literals the method stores at its own top level.
    let clearable: Node | undefined;
    traverse(iife, {
        AssignmentExpression(path) {
            if (clearable !== undefined || !sameSlot(cache, slotOf(path.node.left, scopes))) return;
            const statement = path.parent;
            const inBuilder = statement?.type === "ExpressionStatement" && builder.statements.includes(statement);
            const setsAnswer =
                statement?.type === "ExpressionStatement" && statements.includes(statement) && path.node.operator === "=" && isPrimitiveLiteral(path.node.right) && Boolean(path.node.right.value);
            if (!inBuilder && !setsAnswer) clearable = path.node;
        },
        UpdateExpression(path) {
            if (clearable === undefined && sameSlot(cache, slotOf(path.node.argument, scopes))) clearable = path.node;
        },
    });
    if (clearable !== undefined) return refused(`${method}'s cache may be cleared`, clearable);
    // The other returns: literals other than the answer (answering it then means the cache was read), or all the
    // answer itself (a self-defending check: it answers that or never returns).
    const others = returnsOf(fn).filter((r) => r !== taken);
    const isAnswer = (r: Node): boolean => r.type === "ReturnStatement" && isPrimitiveLiteral(r.argument) && Object.is(r.argument.value, answer);
    if (others.length > 0 && others.every(isAnswer)) return { ok: true, answer, method: fn, cache, parents: builder.parents, constant: true };
    const other = others.find((r) => r.type !== "ReturnStatement" || !isPrimitiveLiteral(r.argument) || isAnswer(r));
    if (other !== undefined) return refused(`${method} may answer ${String(answer)} without its cache`, other);
    return { ok: true, answer, method: fn, cache, parents: builder.parents, constant: false };
};

type Disposition = "remove" | "answer" | "keep";

interface Lock {
    readonly path: PropertyPath;
    readonly sites: readonly CallSite[];
    readonly full: readonly Disposition[];
    readonly staleness: readonly (Staleness | undefined)[];
    readonly fast: FastPath & { ok: true };
    readonly builder: Statement;
}

type LockContext = { runtime: RuntimeModel; scopes: ScopeInfo; matcher: StorageMatcher; effects: StorageEffects; reach: HolderReach };

/** Why the lock's checks (its first call) may change more than objects they create and its cache, if they may. */
const localityRefusal = (fast: FastPath & { ok: true }, context: LockContext): { reason: string; node: Node } | undefined => {
    const { runtime, scopes, matcher, effects } = context;
    const effect = localityOf(fast.method, fast.cache, scopes, fast.parents, (call) => isGlobalRead(call, runtime, matcher, effects));
    return effect === undefined ? undefined : { reason: `its checks may change more than their own objects: ${effect.reason}`, node: effect.node };
};

const fullModeRefusal = (lock: Lock, context: LockContext): { reason: string; node: Node } | undefined => {
    const { path, sites, full, staleness, fast, builder } = lock;
    const { runtime, reach } = context;
    if (path.length !== 2) return { reason: "its holder isn't a key of the storage object itself", node: builder };
    const local = localityRefusal(fast, context);
    if (local !== undefined) return local;
    const used = sites.findIndex(({ discarded }, i) => !discarded && full[i] !== "answer");
    if (used !== -1) return { reason: staleness[used]?.reason ?? "a call whose value is used runs in the prelude, where it may be the first call", node: (sites[used] as CallSite).call };
    const dynamic = reach.reachingDynamicUse(path[0] as string, builder);
    if (dynamic !== undefined) return { reason: `${runtime.storage} is used as a value or read with a computed key once the lock is built, which may reach it`, node: dynamic };
    const callees = new Set(sites.map(({ call }) => (call.callee as MemberExpression).object as Node));
    const stray = reach.strayReference(path, callees, builder);
    if (stray !== undefined) return { reason: `${runtime.storage}.${path[0]} is used other than by its calls, its builder and unused wrappers`, node: stray };
    return undefined;
};

/** Each lock's first probe in the guest, by path: later runs (the cleanup group's) reuse it. */
const LOCK_PROBES = factKey<Map<string, ResolveResult | undefined>>("code-lock probes");

/**
 * Code locks: jscrambler's environment checks (`G.k.m()`) run once, then answer from a cache.
 *
 * Proof per lock: the builder's code shows the cached path and that the cache, once set, stays set (`fastPathOf`);
 * one guest call after the prelude answers the cached value; and each call site reaches the lock the snapshot holds.
 *
 * Full mode (the whole lock goes): the first call changes only objects it creates and its cache (`localityOf`), and
 * the environment passes its checks (model 5). A used call becomes the answer only after the prelude. Every static
 * reference to the holder key is one of those calls, in the builder, in an unused wrapper, or before the builder
 * runs; and `G` escapes only before the builder, in a condition, or into a global nothing names (model 2). Otherwise
 * partial mode: only post-prelude calls go, so the checks run when the original's did.
 *
 * Constant locks (self-defending): every return gives the answer and the other outcome is a trap the environment
 * never meets (model 5), so only full mode applies and the guest isn't asked (it may fall into the trap).
 */
export const codeLocks: Pass = {
    name: "code-locks",
    description: "Remove cached environment checks: all their calls when their checks touch only their own objects, else the calls made after the prelude",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.guest.broken !== undefined) {
            log.info("no usable runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const matcher = storageMatcher(program, runtime, scopes);
        const builders = new Map<FunctionNode, Builder | string>();
        const counts = { locks: 0, full: 0, removed: 0, answered: 0, kept: 0 };
        // A call below is a lock's only when a root statement builds its holder with a method of that name that has a
        // fast path: with no such method, no call is, and the survey (a walk of the whole program) is skipped.
        const shaped = assignedPaths(runtime, matcher.isStorage).some((prefix) => {
            const definition = definitionOf(runtime, matcher.isStorage, prefix);
            if (typeof definition === "string") return false;
            const builder = builders.get(definition.iife) ?? builderOf(definition.iife, scopes);
            builders.set(definition.iife, builder);
            return typeof builder !== "string" && [...builder.methods.keys()].some((method) => fastPathOf(definition.iife, builder, method, scopes).ok);
        });
        if (!shaped) {
            log.info("no builder method has a code lock's shape");
            return { changed: 0, stats: counts };
        }
        const programSurvey = survey(program, runtime, matcher, scopes);
        // Full mode asks only about locks under a key of `G` itself.
        const holders = new Set([...programSurvey.calls.values()].flatMap(({ path }) => (path.length === 2 ? [path[0] as string] : [])));
        // The storage effects (a walk of every function) only once a builder has a lock's shape.
        let context: LockContext | undefined;
        const probes = facts.get(LOCK_PROBES) ?? new Map<string, ResolveResult | undefined>();
        facts.set(LOCK_PROBES, probes);

        const replacements = new Map<Node, Node>();
        const removals = new Set<Node>();
        for (const { path, sites } of programSurvey.calls.values()) {
            if (path.length < 2) continue; // a wrapper: inlined by now when its target is a function
            const name = `${runtime.storage}.${path.join(".")}`;
            const definition = definitionOf(runtime, matcher.isStorage, path.slice(0, -1));
            if (typeof definition === "string") continue; // not a code lock's shape at all: say nothing
            const builder = builders.get(definition.iife) ?? builderOf(definition.iife, scopes);
            builders.set(definition.iife, builder);
            const fast = fastPathOf(definition.iife, builder, path.at(-1) as string, scopes);
            if (!fast.ok) {
                log.debug(`${name} is no code lock: ${fast.reason}`, fast.node);
                continue;
            }
            if (!fast.constant) {
                // The probe runs the lock in the guest, setting its cache there if the prelude hadn't: a later run
                // must see what the first probe saw, not the state that probe left.
                const id = path.join("\u0000");
                const probe = probes.get(id) ?? runtime.guest.resolve([{ path, args: [] }])[0];
                probes.set(id, probe);
                if (probe === undefined || !probe.ok || "nonPrimitive" in probe || !probe.repeatable || !Object.is(probe.value, fast.answer)) {
                    log.debug(`${name} looks like a code lock, but in the guest it doesn't answer ${String(fast.answer)} from its cache`, fast.method);
                    continue;
                }
            }
            counts.locks++;
            log.debug(
                fast.constant
                    ? `${name} is a constant lock: every call that returns answers ${String(fast.answer)}`
                    : `${name} is a code lock: after its first call it answers ${String(fast.answer)} and does nothing else`,
                fast.method
            );

            if (context === undefined) {
                const { effects } = storageAnalysis(program, runtime, scopes, log);
                context = { runtime, scopes, matcher, effects, reach: new HolderReach(program, runtime, matcher, scopes, effects, programSurvey.dynamic, holders) };
            }
            const known = context.effects;
            const staleness = sites.map(({ site }) => known.staleAt(site, path));
            // A discarded call's answer is as good as no call; a used one may answer the cached value only after the prelude.
            const full = sites.map(({ statement, discarded, site }, i): Disposition =>
                staleness[i] !== undefined ? "keep" : statement !== undefined ? "remove" : discarded || fast.constant || known.runsAfterPrelude(site) ? "answer" : "keep"
            );
            // A constant lock's later calls may still be its first: no partial mode.
            const partial = sites.map(({ statement, site }, i): Disposition =>
                fast.constant || staleness[i] !== undefined || !known.runsAfterPrelude(site) ? "keep" : statement === undefined ? "answer" : "remove"
            );
            // A constant lock's calls answer whoever else may call it: callers the analysis can't see run the checks
            // themselves, which touch only their own objects.
            const refusal = fast.constant ? localityRefusal(fast, context) : fullModeRefusal({ path, sites, full, staleness, fast, builder: definition.statement }, context);
            if (refusal === undefined) counts.full++;
            else log.debug(`${name}: ${fast.constant ? "kept" : "partial mode, the prelude's calls stay"}: ${refusal.reason}`, refusal.node);

            const dispositions = refusal === undefined ? full : partial;
            const lock = { removed: 0, answered: 0, kept: 0 };
            for (const [i, { call, statement }] of sites.entries()) {
                const disposition = dispositions[i];
                if (disposition === "keep") {
                    lock.kept++;
                    const stale = staleness[i];
                    log.debug(`kept: ${stale?.reason ?? "the call runs in the prelude, which makes the first call"}`, stale?.node ?? call);
                } else if (disposition === "answer") {
                    replacements.set(call, valueToNode(fast.answer, call, scopes));
                    lock.answered++;
                } else {
                    removals.add(statement as Statement);
                    lock.removed++;
                }
            }
            const mode = refusal === undefined ? "full" : `partial: ${refusal.reason}`;
            log.info(`${name} (${mode}): removed ${lock.removed} call(s), answered ${lock.answered}, kept ${lock.kept}`, definition.statement);
            counts.removed += lock.removed;
            counts.answered += lock.answered;
            counts.kept += lock.kept;
        }

        rewriteCalls(program, replacements, removals);
        log.info(`${counts.locks} code lock(s), ${counts.full} removed in full: removed ${counts.removed} call(s), answered ${counts.answered}, kept ${counts.kept}`);
        return { changed: counts.removed + counts.answered, bindingsChanged: false, stats: counts };
    },
};
