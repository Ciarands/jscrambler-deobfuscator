import type { CallExpression, Node } from "../core/ast.js";
import { propertyKey } from "../core/ast.js";
import { callOf, memberChain } from "../core/build.js";
import { evaluate } from "../core/evaluate.js";
import { sameItems } from "../core/list.js";
import { traverse } from "../core/traverse.js";
import { factKey } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { PropertyPath } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import type { StorageEffects } from "./emulate/effects.js";
import { storageAnalysis } from "./emulate/effects.js";

/**
 * How many wrappers runs rewrote calls. Wrappers is the one pass that makes wrapper call sites (direct calls of a
 * wrapper's target) after resolve-calls walked the program: resolve-calls walks again when this changes.
 */
export const WRAPPER_REWRITES = factKey<number>("wrapper rewrites");

/**
 * An argument whose evaluation runs no code of the program: no calls, assignments, getters (member reads) or
 * conversions. Only then can the inlined call read the target before the arguments, as the wrapper reads it after.
 */
const isInert = (node: Node): boolean => {
    switch (node.type) {
        case "Literal":
        case "Identifier":
        case "ThisExpression":
        case "FunctionExpression":
        case "ArrowFunctionExpression":
            return true;
        case "ArrayExpression":
            return node.elements.every((element) => element === null || (element.type !== "SpreadElement" && isInert(element)));
        case "ObjectExpression":
            return node.properties.every((p) => p.type === "Property" && !p.computed && p.kind === "init" && isInert(p.value));
        default:
            return evaluate(node).ok;
    }
};

/**
 * Why the arguments of `call`, run before the inlined call reads its target, could see another target, if they could.
 * Safe when they run no code, or when the target's object is reached only through `G`'s paths (model 3) and nothing
 * naming those paths changes it after the prelude.
 */
const reorderingRisk = (call: CallExpression, target: PropertyPath, site: Node, effects: StorageEffects): string | undefined => {
    if (call.arguments.every((arg) => arg.type !== "SpreadElement" && isInert(arg))) return undefined;
    const risk = "an argument could run code before the wrapper reads its target";
    if (!effects.reachedOnlyThroughStorage(target.slice(0, -1))) return `${risk}, and code other than G's paths may hold the target's object`;
    const stale = effects.staleAt(site, target);
    return stale === undefined ? undefined : `${risk}, and ${stale.reason}`;
};

/**
 * Wrapper inlining (#5): `G.w = function () { return typeof T === "function" ? T.apply(O, arguments) : T; }`.
 *
 * - Function targets: `G.w(a, b)` -> `O.m(a, b)`. The wrapper reads T after the arguments, the inlined call before:
 *   the same only when reading T runs no code and the arguments can't change T (`reorderingRisk`).
 * - Value targets: only `G.w()` -> `T`.
 *
 * The kind is the snapshot's, so only where nothing writes `G.w`, T or a prefix after the prelude. The site's own
 * storage reference roots the inlined path, so no shadowable name is introduced.
 */
export const wrappers: Pass = {
    name: "wrappers",
    description: "Inline calls through the runtime's wrapper functions by target kind",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.wrappers.size === 0) {
            log.info("no wrappers known, nothing to do");
            return { changed: 0 };
        }
        const { guest, storage } = runtime;
        const scopes = scope();
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);

        const kinds = new Map<string, { kind: "function" | "value"; target: PropertyPath }>();
        for (const [key, wrapper] of runtime.wrappers) {
            const name = `${storage}.${wrapper.target.join(".")}`;
            const info = guest.inspect(wrapper.target);
            if (info === undefined) {
                log.debug(`wrapper ${key}: can't read ${name}, left`, wrapper.definition);
                continue;
            }
            if (!info.data) {
                log.debug(`wrapper ${key}: ${name} is reached through an accessor, left`, wrapper.definition);
                continue;
            }
            const isFunction = info.type === "function";
            if (isFunction && (wrapper.receiver === undefined || !sameItems(wrapper.receiver, wrapper.target.slice(0, -1)))) {
                log.debug(`wrapper ${key}: applies ${name} with a different this, left`, wrapper.definition);
                continue;
            }
            kinds.set(key, { kind: isFunction ? "function" : "value", target: wrapper.target });
            log.debug(`wrapper ${key} -> ${name} (${isFunction ? "function" : "value"})`, wrapper.definition);
        }

        const counts = { inlined: 0, stale: 0, arguments: 0, valueArguments: 0 };
        const keep = (kind: "stale" | "arguments" | "valueArguments", reason: string, node: Node): void => {
            counts[kind]++;
            log.debug(`kept: ${reason}`, node);
        };
        traverse(program, {
            CallExpression(path) {
                const call: CallExpression = path.node;
                const callee = call.callee;
                if (callee.type !== "MemberExpression" || !matcher.isStorage(callee.object)) return;
                const key = propertyKey(callee);
                const entry = key === undefined ? undefined : kinds.get(key);
                if (entry === undefined || key === undefined) return;
                const stale = effects.staleAt(callee.object, [key]) ?? effects.staleAt(callee.object, entry.target, true);
                if (stale !== undefined) return keep("stale", stale.reason, stale.node);
                const target = memberChain(callee.object, entry.target, callee);
                if (entry.kind === "function") {
                    const risk = reorderingRisk(call, entry.target, callee.object, effects);
                    if (risk !== undefined) return keep("arguments", risk, call);
                    path.replace(callOf(target, call.arguments, call));
                } else {
                    if (call.arguments.length > 0) return keep("valueArguments", "value target called with arguments", call);
                    path.replace(target);
                }
                counts.inlined++;
            },
        });

        if (counts.inlined > 0) facts.set(WRAPPER_REWRITES, (facts.get(WRAPPER_REWRITES) ?? 0) + 1);
        log.info(
            `inlined ${counts.inlined} wrapper call(s) through ${kinds.size} wrapper(s); kept ${counts.stale} whose wrapper or target may change, ${counts.arguments} whose arguments could change the target first, ${counts.valueArguments} value target(s) called with arguments`
        );
        return { changed: counts.inlined, bindingsChanged: false, stats: { ...counts, wrappers: kinds.size } };
    },
};
