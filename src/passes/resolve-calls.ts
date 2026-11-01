import type { CallExpression, Expression, Node, SequenceExpression } from "../core/ast.js";
import { memberPath, propertyKey } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import { constantEnv } from "../core/constants.js";
import { pushAll } from "../core/list.js";
import type { EvaluateEnv, Evaluation, Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import type { Path } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { factKey } from "../pipeline/facts.js";
import type { DecoderProof } from "./emulate/decoder.js";
import { DECODER_PROOF, decoderLookups } from "./emulate/decoder.js";
import { shareStorageAnalysis, storageEffects } from "./emulate/effects.js";
import type { LoggedCall, ResolveRequest } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import { storageMatcher } from "./emulate/storage.js";

/** Identity of a call by key and argument values, matching how `emulate` reports calls it couldn't place. */
const sameCall = (key: string, args: readonly unknown[], other: { key: string; args: readonly unknown[] }): boolean =>
    key === other.key && args.length === other.args.length && args.every((arg, i) => Object.is(arg, other.args[i]));

/** A call site to resolve: where the result goes (`node`: the call, or the outermost member of a lookup on it). */
interface Candidate {
    readonly node: Node;
    readonly request: ResolveRequest;
    /** Lookups resolve to any primitive (they index a generated table); plain calls only to strings. */
    readonly isLookup: boolean;
    /** The reference to `G` the call goes through, and the wrapper key: what must still be the snapshot's there. */
    readonly site: Node;
    readonly key: string;
    /** What the arguments run before their constant values (`e` of `G.w((e, 32))`): kept ahead of the answer. */
    readonly prefix: readonly Expression[];
    /** A direct call of the wrapper's target (`G.D.m(5)`), not one through the wrapper. */
    readonly direct: boolean;
}

/** What resolve-calls keeps between its runs: the first right after emulate, the others in the simplify group. */
interface Resolution {
    /** Wrapper call sites decided for good: resolved, kept with their results, or left for a reason that stays. */
    readonly decided: WeakSet<Node>;
    /** Sites of settled decoders whose arguments weren't constant yet, as the last run found them. */
    waiting: Set<Node>;
    readonly logged: WeakSet<Node>;
    readonly proof: DecoderProof;
    /**
     * Per settled decoder (its target path, `\0`-joined), the reference to `G` its settling call goes through: a
     * direct call of it that runs only after that call's root statement can't drive a stage. Found by the first run.
     */
    readonly settlingSites: Map<string, Node>;
    /** How many runs walked the whole program; after wrappers, no later pass makes new decoder calls. */
    walks: number;
}

/** A value in a request's identity: strings quoted, numbers keeping `-0` apart, other primitives by type. */
const requestPart = (value: unknown): string =>
    typeof value === "string" ? JSON.stringify(value) : typeof value === "number" ? (Object.is(value, -0) ? "-0" : String(value)) : `${typeof value}:${String(value)}`;

const requestId = (request: ResolveRequest): string => `${request.path.map(requestPart).join(".")}(${request.args.map(requestPart).join(",")})${(request.lookup ?? []).map(requestPart).join(".")}`;

const RESOLUTION = factKey<Resolution>("resolve-calls");

const argumentValue = (arg: Node, env: EvaluateEnv): Evaluation | undefined => {
    const last = arg.type === "SequenceExpression" ? arg.expressions.at(-1) : arg;
    return last === undefined || last.type === "SpreadElement" ? undefined : evaluate(last, env);
};

/**
 * Resolve calls to the runtime's wrapper functions (`G.w(...)`, mostly the string decoder).
 *
 * The decoder is stateful until its stages are done (`decoderLookups` proves when). So:
 * - Calls the prelude made keep running: `G.P1(50)` becomes `(G.P1(50), 1)`, so the decoder still gets its stages;
 *   one proven a pure lookup on its settled decoder becomes just its value.
 * - Later constant-argument calls of a settled decoder's wrappers are pure lookups: batched in the sandbox on the
 *   post-prelude state, replaced when the result is a repeatable string. Other targets stay: a call can change state
 *   and still give the same result twice.
 * - Sites matching an unplaced prelude call are left alone (they may be that call, made before the decoder froze),
 *   unless every such call was a pure lookup on a settled decoder.
 */
export const resolveCalls: Pass = {
    name: "resolve-calls",
    description: "Replace wrapper (decoder) calls with their results from the emulated runtime",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.wrappers.size === 0) {
            log.info("no wrappers known, nothing to do");
            return { changed: 0 };
        }
        const { guest, callResults, wrappers } = runtime;
        const earlier = facts.get(RESOLUTION);
        // Later runs only look for settled decoders' calls whose arguments were waiting to become constant. Once a walk
        // after wrappers found them (`walks`), until one of them has constant arguments, there is nothing to do.
        if (earlier !== undefined && earlier.waiting.size === 0) {
            log.info("no wrapper calls wait for constant arguments");
            return { changed: 0 };
        }
        if (earlier !== undefined && earlier.walks >= 2) {
            const env = constantEnv(scope(), log);
            const ready = [...earlier.waiting].some((call) => call.type === "CallExpression" && call.arguments.every((arg) => argumentValue(arg, env)?.ok === true));
            if (!ready) {
                log.info(`none of the ${earlier.waiting.size} waiting call(s) has constant arguments yet`);
                return { changed: 0 };
            }
        }
        const scopes = scope();
        const matcher = storageMatcher(program, runtime, scopes);
        const { isStorage } = matcher;
        const resolution: Resolution = earlier ?? {
            decided: new WeakSet(),
            waiting: new Set(),
            logged: new WeakSet(),
            proof: decoderLookups(runtime, matcher, scopes, log),
            settlingSites: new Map(),
            walks: 0,
        };
        resolution.walks++;
        if (earlier === undefined) {
            facts.set(RESOLUTION, resolution);
            facts.set(DECODER_PROOF, resolution.proof);
        }
        const { decided, logged: loggedWaiting, proof } = resolution;
        const waiting = new Set<Node>();
        const unmappedByKey = new Map<string, LoggedCall[]>();
        for (const logged of runtime.unmappedCalls) unmappedByKey.set(logged.key, [...(unmappedByKey.get(logged.key) ?? []), logged]);
        // Built on first use: later runs often find no call left to look at.
        let env: EvaluateEnv | undefined;
        const constants = (): EvaluateEnv => (env ??= constantEnv(scopes, log));
        let recordedSeen = 0;
        const counts = { prelude: 0, dropped: 0, resolved: 0, lookups: 0, kept: 0 };
        const keep = (reason: string, node: Node) => {
            counts.kept++;
            log.debug(`kept: ${reason}`, node);
        };
        /**
         * Constant-key reads on top of a call (`call[41][49]`). A method called on the result leaves its key out:
         * the receiver is what gets resolved.
         */
        const lookupOn = (path: Path): { outer: Path; keys: string[] } => {
            let outer: Path = path;
            let receiver: Path = path;
            const keys: string[] = [];
            while (outer.parent?.type === "MemberExpression" && outer.key === "object" && outer.parentPath !== null && !outer.parentPath.isWriteTarget()) {
                const member = outer.parent;
                const key = member.computed ? evaluate(member.property, constants()) : { ok: true as const, value: propertyKey(member) };
                if (!key.ok || key.value === undefined) break;
                keys.push(String(key.value));
                receiver = outer;
                outer = outer.parentPath;
            }
            return outer.parent?.type === "CallExpression" && outer.key === "callee" && keys.length > 0 ? { outer: receiver, keys: keys.slice(0, -1) } : { outer, keys };
        };

        const candidates: Candidate[] = [];
        /** Wrapper keys by their target's path: a direct call of the target (what wrappers makes of a wrapper call) asks the same. */
        const wrapperOfTarget = new Map<string, string>();
        for (const [key, wrapper] of wrappers) if (wrapper.target !== undefined) wrapperOfTarget.set(wrapper.target.join("\u0000"), key);
        const targetOf = (key: string): string | undefined => wrappers.get(key)?.target.join("\u0000");
        traverse(program, {
            CallExpression(path) {
                const call: CallExpression = path.node;
                if (decided.has(call)) return;
                const callee = call.callee;
                if (callee.type !== "MemberExpression") return;
                let key = isStorage(callee.object) ? propertyKey(callee) : undefined;
                let site: Node = callee.object;
                let direct = false;
                if (key === undefined || !wrappers.has(key)) {
                    const target = memberPath(callee);
                    key = target !== undefined && isStorage(target.root) ? wrapperOfTarget.get(target.keys.join("\u0000")) : undefined;
                    if (key === undefined || target === undefined) return;
                    site = target.root;
                    direct = true;
                }

                if (callResults.has(call)) {
                    decided.add(call);
                    recordedSeen++;
                    const recorded = callResults.get(call);
                    const logged = runtime.siteCalls.get(call);
                    const target = logged !== undefined && proof.settlingCalls.has(logged) ? targetOf(key) : undefined;
                    if (target !== undefined) resolution.settlingSites.set(target, site);
                    if (logged !== undefined && proof.lookups.has(logged)) {
                        path.replace(valueToNode(recorded, call, scopes));
                        counts.dropped++;
                        log.debug(`a pure lookup on its settled decoder: replaced by its result ${JSON.stringify(recorded)}`, call);
                        return;
                    }
                    // The original call stays first in the sequence: its side effect drives the decoder's stages.
                    path.replace(at<SequenceExpression>({ type: "SequenceExpression", expressions: [call, valueToNode(recorded, call, scopes)] }, call));
                    counts.prelude++;
                    return;
                }
                // Only a settled decoder's calls are proven free of effects; later runs also find the guest moved on
                // by earlier batches, which a settled decoder's lookups can't notice.
                if (!proof.settled.has(key)) {
                    decided.add(call);
                    return keep("its target isn't a settled string decoder: the call may have effects", call);
                }

                // `(e, 32)` passes 32 once `e` ran: `e` stays, in order, ahead of the answer.
                const args: Value[] = [];
                const prefix: Expression[] = [];
                for (const arg of call.arguments) {
                    const value = argumentValue(arg, constants());
                    if (value?.ok === true) {
                        if (arg.type === "SequenceExpression") pushAll(prefix, arg.expressions.slice(0, -1));
                        args.push(value.value);
                        continue;
                    }
                    // Constant propagation in the simplify group may still make it one: looked at again then.
                    if (!loggedWaiting.has(call)) log.debug(`left for now: ${arg.type === "SpreadElement" ? "spread argument" : "argument is not a constant"}`, arg);
                    loggedWaiting.add(call);
                    waiting.add(call);
                    return;
                }
                decided.add(call);
                const unplaced = (unmappedByKey.get(key) ?? []).filter((logged) => sameCall(key, args, logged));
                if (unplaced.some((logged) => !proof.lookups.has(logged))) return keep("the prelude made this call but its site is unknown", call);
                if (unplaced.length > 0)
                    log.debug(`the prelude made ${unplaced.length} call(s) like this one at unknown sites, each a pure lookup on its settled decoder: resolved like a later call`, call);

                const lookup = lookupOn(path);
                const isLookup = lookup.keys.length > 0;
                candidates.push({ node: isLookup ? lookup.outer.node : call, request: { path: [key], args, ...(isLookup ? { lookup: lookup.keys } : {}) }, isLookup, site, key, prefix, direct });
            },
        });
        resolution.waiting = waiting;
        if (earlier !== undefined && candidates.length === 0 && counts.dropped + counts.prelude === 0) {
            log.info("no new wrapper calls to resolve");
            return { changed: 0 };
        }
        // Call results are keyed by the call node: a call an earlier pass replaced (or rewrote) lost its result.
        if (earlier === undefined && log.debugging && recordedSeen < callResults.size) {
            const lost = [...callResults.keys()].filter((node) => !decided.has(node));
            log.debug(`${lost.length} recorded call result(s) unused: their call is no longer a wrapper call in the program (replaced by an earlier pass)`, lost[0]);
        }

        // One batch for every distinct request (the candidates' targets are settled decoders, pure lookups: equal
        // requests get equal answers); the answers the snapshot gives, by where they would go.
        const answers = new Map<Node, Value>();
        if (candidates.length > 0 && guest.broken !== undefined) {
            for (const { node } of candidates) keep("the sandbox is no longer usable", node);
        } else if (candidates.length > 0) {
            const unique = new Map<string, number>();
            const requests: ResolveRequest[] = [];
            const slots = candidates.map(({ request }) => {
                const id = requestId(request);
                let slot = unique.get(id);
                if (slot === undefined) {
                    slot = requests.push(request) - 1;
                    unique.set(id, slot);
                }
                return slot;
            });
            const results = guest.resolve(requests);
            for (const [i, candidate] of candidates.entries()) {
                const result = results[slots[i] as number];
                const { node, isLookup } = candidate;
                if (result === undefined || !result.ok) {
                    keep(result === undefined ? "no answer" : result.stale === true || result.env === true ? result.error : `call threw in the sandbox: ${result.error}`, node);
                    continue;
                }
                if ("nonPrimitive" in result) {
                    keep(`result is ${result.nonPrimitive === "object" ? "an object" : "a function"}${isLookup ? " even after the lookup" : ", used as a whole"}`, node);
                    continue;
                }
                if (!result.repeatable) {
                    keep("result changes between calls", node);
                    continue;
                }
                // Numbers from plain calls can come from environment checks (scoring functions); only table lookups
                // and strings are values the program would see the same in any environment.
                if (!isLookup && typeof result.value !== "string") {
                    keep(`result is a ${typeof result.value}, only strings are resolved`, node);
                    continue;
                }
                answers.set(node, result.value);
            }
        }

        // An answer comes from the snapshot's G.key and what it reads, the wrapper's target: only good where nothing
        // changes either before the call (for the target: no write; the runtime's own calls are what the guest ran).
        // Answers used as computed storage keys (`G[G.w(147)]()`) sharpen the analysis of what changes them, but only
        // while they hold up themselves: drop the answers that don't and analyse again, until none is dropped.
        const keyOf = (property: Node): string | undefined => {
            const value = answers.get(property);
            return typeof value === "string" ? value : undefined;
        };
        let effects = storageEffects(runtime, matcher, scopes, log, keyOf);
        /** The root statement by whose end the decoder `target` settled, as the program is now. */
        const settledIn = (target: string | undefined): Node | undefined => {
            const site = target === undefined ? undefined : resolution.settlingSites.get(target);
            return site === undefined ? undefined : effects.lastPreludeStatement(site);
        };
        for (;;) {
            let dropped = 0;
            for (const candidate of candidates) {
                if (!answers.has(candidate.node)) continue;
                const target = wrappers.get(candidate.key)?.target;
                // A direct call of the target (a wrapper call wrappers rewrote) has no recorded result: in the prelude
                // it may be a stage call, so only one that runs after its decoder settled is a lookup.
                const settled = settledIn(targetOf(candidate.key));
                const early = candidate.direct && !(settled === undefined ? effects.runsAfterPrelude(candidate.site) : effects.runsAfter(candidate.site, settled));
                const stale = early
                    ? { reason: "a direct call of the decoder that may run in the prelude before the decoder settled, where it can drive a stage", node: candidate.node }
                    : (effects.staleAt(candidate.site, [candidate.key]) ?? (target === undefined ? undefined : effects.staleAt(candidate.site, target, true)));
                if (stale === undefined) continue;
                keep(stale.reason, stale.node);
                answers.delete(candidate.node);
                dropped++;
            }
            if (dropped === 0) break;
            log.debug(`dropped ${dropped} answer(s) that may not hold; analysing again without them`);
            effects = storageEffects(runtime, matcher, scopes, log, keyOf);
        }
        // The accepted keys become literals below: what the analysis found with them holds for the program as it will be.
        shareStorageAnalysis(scopes, { matcher, effects });

        const replacements = new Map<Node, Node>();
        const byTarget = new Map<string, number>();
        for (const { node, isLookup, key, prefix } of candidates) {
            if (!answers.has(node)) continue;
            const value = valueToNode(answers.get(node), node, scopes) as Expression;
            replacements.set(node, prefix.length === 0 ? value : at<SequenceExpression>({ type: "SequenceExpression", expressions: [...prefix, value] }, node));
            if (isLookup) counts.lookups++;
            else counts.resolved++;
            const target = `${runtime.storage}.${(wrappers.get(key)?.target ?? [key]).join(".")}`;
            byTarget.set(target, (byTarget.get(target) ?? 0) + 1);
        }
        replaceNodes(program, replacements);

        log.info(
            `resolved ${counts.resolved} call(s) to strings and ${counts.lookups} table lookup(s), replaced ${counts.dropped} prelude call(s) proven pure lookups by their results, kept ${counts.prelude} with their results, left ${counts.kept}`
        );
        if (byTarget.size > 0) log.info(`resolved later calls by target: ${[...byTarget].map(([target, count]) => `${target} ${count}`).join(", ")}`);
        return { changed: counts.resolved + counts.lookups + counts.prelude + counts.dropped, bindingsChanged: false, stats: counts };
    },
};
