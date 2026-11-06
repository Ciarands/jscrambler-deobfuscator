import type { CallExpression, Expression, Node, SequenceExpression } from "../core/ast.js";
import { memberPath, propertyKey } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import { isCallable, isObject } from "../core/builtins.js";
import { constantEnv } from "../core/constants.js";
import { pushAll } from "../core/list.js";
import type { EvaluateEnv, Evaluation, Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import type { Held } from "../core/interpret.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import type { Path } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { factKey } from "../pipeline/facts.js";
import type { DecoderProof } from "./runtime/decoder.js";
import { DECODER_PROOF, proveDecoders } from "./runtime/decoder.js";
import type { Staleness } from "./runtime/effects.js";
import { shareStorageAnalysis, storageEffects } from "./runtime/effects.js";
import { RUNTIME } from "./runtime/model.js";
import { storageMatcher } from "./runtime/storage.js";
import { WRAPPER_REWRITES } from "./wrappers.js";

/** A lookup to make on a settled decoder: its wrapper `key`, the call's arguments, the reads on its result. */
interface Request {
    readonly key: string;
    readonly args: readonly Value[];
    readonly lookup: readonly string[];
}

/** A call site to resolve: where the result goes (`node`: the call, or the outermost member of a lookup on it). */
interface Candidate {
    readonly node: Node;
    readonly call: CallExpression;
    readonly request: Request;
    /** Lookups resolve to any primitive (they index a generated table); plain calls only to strings. */
    readonly isLookup: boolean;
    /** The reference to `G` the call goes through, and the wrapper key: what must still be the prelude's there. */
    readonly site: Node;
    readonly key: string;
    /** What the arguments run before their constant values (`e` of `G.w((e, 32))`): kept ahead of the answer. */
    readonly prefix: readonly Expression[];
}

/** What resolve-calls keeps between its runs: the first right after runtime, the others in the simplify group. */
interface Resolution {
    /** Wrapper call sites decided for good: resolved, kept with their results, or left for a reason that stays. */
    readonly decided: WeakSet<Node>;
    /** Sites of settled decoders whose arguments weren't constant yet, as the last run found them. */
    waiting: Set<Node>;
    readonly logged: WeakSet<Node>;
    readonly proof: DecoderProof;
    /**
     * Per settled decoder (its target path, `\0`-joined), the reference to `G` its settling call goes through: a call
     * of it that runs only after that call's root statement can't drive a stage. Found by the first run.
     */
    readonly settlingSites: Map<string, Node>;
    /** `WRAPPER_REWRITES` as of the last walk of the whole program: past it, wrapper call sites the walk didn't see. */
    rewritesWalked: number;
}

/** A value in a request's identity: strings quoted, numbers keeping `-0` apart, other primitives by type. */
const requestPart = (value: unknown): string =>
    typeof value === "string" ? JSON.stringify(value) : typeof value === "number" ? (Object.is(value, -0) ? "-0" : String(value)) : `${typeof value}:${String(value)}`;

const requestId = (request: Request): string => `${requestPart(request.key)}(${request.args.map(requestPart).join(",")})${request.lookup.map(requestPart).join(".")}`;

const RESOLUTION = factKey<Resolution>("resolve-calls");

const argumentValue = (arg: Node, env: EvaluateEnv): Evaluation | undefined => {
    const last = arg.type === "SequenceExpression" ? arg.expressions.at(-1) : arg;
    return last === undefined || last.type === "SpreadElement" ? undefined : evaluate(last, env);
};

/**
 * Resolve calls to the runtime's wrapper functions (`G.w(...)`), the string decoder's, from the decoder built on the
 * host (`proveDecoders`):
 * - The prelude's calls of a decoder in its proven order up to the one settling it keep running: `G.P1(50)` becomes
 *   `(G.P1(50), 1)`, so the decoder still gets its stages.
 * - Constant-argument calls of a settled decoder's wrappers (and of its target, `G.k.m(5)`) that run after its
 *   settling call are lookups on its final table: answered on the host, replaced when the result is a string (or a
 *   lookup's primitive). Other targets stay: a call can change state and still give the same result twice.
 * - The answers hold where nothing changes the decoder or its wrapper after the prelude, and the prelude writes them
 *   only where they are made (`effects.ts`).
 */
export const resolveCalls: Pass = {
    name: "resolve-calls",
    description: "Replace wrapper (decoder) calls with their results from the decoder built on the host",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.wrappers.size === 0) {
            log.info("no wrappers known, nothing to do");
            return { changed: 0 };
        }
        const { wrappers } = runtime;
        const earlier = facts.get(RESOLUTION);
        // Later runs only look for settled decoders' calls whose arguments were waiting to become constant. Wrappers
        // rewriting such calls since the last walk makes new sites of them; otherwise, until one has constant
        // arguments, there is nothing to do.
        if (earlier !== undefined && earlier.waiting.size === 0) {
            log.info("no wrapper calls wait for constant arguments");
            return { changed: 0 };
        }
        const rewrites = facts.get(WRAPPER_REWRITES) ?? 0;
        if (earlier !== undefined && earlier.rewritesWalked === rewrites) {
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
            proof: proveDecoders(runtime, matcher, scopes, log),
            settlingSites: new Map(),
            rewritesWalked: rewrites,
        };
        if (earlier === undefined) {
            facts.set(RESOLUTION, resolution);
            facts.set(DECODER_PROOF, resolution.proof);
        } else earlier.rewritesWalked = rewrites;
        const { decided, logged: loggedWaiting, proof } = resolution;
        const waiting = new Set<Node>();
        // Built on first use: later runs often find no call left to look at.
        let env: EvaluateEnv | undefined;
        const constants = (): EvaluateEnv => (env ??= constantEnv(scopes, log));
        const counts = { prelude: 0, resolved: 0, lookups: 0, kept: 0 };
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
        for (const [key, wrapper] of wrappers) wrapperOfTarget.set(wrapper.target.join("\u0000"), key);
        const targetOf = (key: string): string | undefined => wrappers.get(key)?.target.join("\u0000");
        traverse(program, {
            CallExpression(path) {
                const call: CallExpression = path.node;
                if (decided.has(call)) return;
                const callee = call.callee;
                if (callee.type !== "MemberExpression") return;
                let key = isStorage(callee.object) ? propertyKey(callee) : undefined;
                let site: Node = callee.object;
                if (key === undefined || !wrappers.has(key)) {
                    const target = memberPath(callee);
                    key = target !== undefined && isStorage(target.root) ? wrapperOfTarget.get(target.keys.join("\u0000")) : undefined;
                    if (key === undefined || target === undefined) return;
                    site = target.root;
                }

                if (proof.stageCalls.has(call)) {
                    decided.add(call);
                    const target = targetOf(key);
                    if (target !== undefined && proof.settling.get(target)?.call === call) resolution.settlingSites.set(target, site);
                    // The original call stays first in the sequence: its side effect drives the decoder's stages.
                    path.replace(at<SequenceExpression>({ type: "SequenceExpression", expressions: [call, valueToNode(proof.stageCalls.get(call), call, scopes)] }, call));
                    counts.prelude++;
                    return;
                }
                // Only a settled decoder's calls after its settling one are proven free of effects.
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
                const lookup = lookupOn(path);
                const isLookup = lookup.keys.length > 0;
                candidates.push({ node: isLookup ? lookup.outer.node : call, call, request: { key, args, lookup: lookup.keys }, isLookup, site, key, prefix });
            },
        });
        resolution.waiting = waiting;
        if (earlier !== undefined && candidates.length === 0 && counts.prelude === 0) {
            log.info("no new wrapper calls to resolve");
            return { changed: 0 };
        }

        // One host call for every distinct request (the candidates' decoders are settled: equal requests get equal
        // answers); the answers by where they would go.
        const answers = new Map<Node, Value>();
        const results = new Map<string, Held>();
        for (const candidate of candidates) {
            const { node, isLookup, request } = candidate;
            const id = requestId(request);
            let result = results.get(id);
            if (result === undefined) {
                result = proof.lookup(request.key, request.args, request.lookup);
                results.set(id, result);
            }
            if (!result.ok) {
                keep(`the host gave no answer: ${result.reason}`, node);
                continue;
            }
            const { value } = result;
            if (isObject(value)) {
                keep(`result is ${isCallable(value) ? "a function" : "an object"}${isLookup ? " even after the lookup" : ", used as a whole"}`, node);
                continue;
            }
            // Numbers from plain calls of other runtimes' functions can come from environment checks; only table lookups
            // and strings are values the program would see the same in any environment.
            if (!isLookup && typeof value !== "string") {
                keep(`result is a ${typeof value}, only strings are resolved`, node);
                continue;
            }
            answers.set(node, value);
        }

        // An answer comes from the decoder as the prelude leaves it, read through `G.key` and its target: only good where
        // nothing changes either (for the target and its holder: no write in the prelude but where they are made, none
        // after it), and where the call runs after the settling one. Answers used as computed storage keys
        // (`G[G.w(147)]()`) sharpen the analysis of what changes them, but only while they hold up themselves: drop the
        // answers that don't and analyse again, until none is dropped.
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
        /** Writes of the prelude to `path` other than the one statement making it (a wrapper's, a holder's or its copy's). */
        const rewritten = (path: readonly string[], node: Node): Staleness | undefined =>
            effects.preludeWritesTo(path) > 1 ? { reason: `the prelude writes ${runtime.storage}.${path.join(".")} besides where it is made`, node } : undefined;
        for (;;) {
            let dropped = 0;
            for (const candidate of candidates) {
                if (!answers.has(candidate.node)) continue;
                const target = wrappers.get(candidate.key)?.target;
                const targetId = targetOf(candidate.key);
                const settling = targetId === undefined ? undefined : proof.settling.get(targetId);
                const settled = settledIn(targetId);
                // A call that may run before the settling one may be a stage call, or come before a stage call.
                const early = settling?.after.has(candidate.call) !== true && !(settled === undefined ? effects.runsAfterPrelude(candidate.site) : effects.runsAfter(candidate.site, settled));
                const method = target?.[1];
                const holders = method === undefined ? [] : [...(settling?.holders ?? [])].map((holder) => [holder, method]);
                const stale = early
                    ? { reason: "a call of the decoder that may run in the prelude before it settled, where it can drive a stage", node: candidate.node }
                    : (effects.staleAt(candidate.site, [candidate.key]) ??
                      rewritten([candidate.key], candidate.node) ??
                      holders.map((path) => effects.staleAt(candidate.site, path, true) ?? rewritten(path, candidate.node)).find((found) => found !== undefined));
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

        log.info(`resolved ${counts.resolved} call(s) to strings and ${counts.lookups} table lookup(s), kept ${counts.prelude} prelude call(s) with their results, left ${counts.kept}`);
        if (byTarget.size > 0) log.info(`resolved later calls by target: ${[...byTarget].map(([target, count]) => `${target} ${count}`).join(", ")}`);
        return { changed: counts.resolved + counts.lookups + counts.prelude, bindingsChanged: false, stats: counts };
    },
};
