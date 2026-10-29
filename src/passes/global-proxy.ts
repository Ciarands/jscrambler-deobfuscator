import type { IdentifierReference, MemberExpression, Node } from "../core/ast.js";
import { propertyKey } from "../core/ast.js";
import { at } from "../core/build.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { RUNTIME } from "./emulate/model.js";
import { storageAnalysis } from "./emulate/effects.js";

/**
 * Global proxy: `G[k]` (where the emulated prelude left the global object) becomes `globalThis`.
 *
 * jscrambler's prelude stores the global object, found through an `Object.prototype` getter, on its storage object and
 * reaches globals through it (`G[611277].String`). Only reads of those slots are rewritten; `G` stays its own object
 * (main rewrote all of `G` to the global object, so `G[0] = ...` landed on `window[0]`). The definition
 * (`G[k] = (function () { ... })()`) is left for cleanup.
 *
 * A read is rewritten only where it sees the snapshot's value (nothing writes `G[k]` later, and it doesn't run while
 * the prelude is still setting it up) and where `globalThis` isn't a local name. The storage binding is told apart
 * from same-named locals by scope; locals that only ever hold `G` (`var g = G;`) count as `G`.
 */
export const globalProxy: Pass = {
    name: "global-proxy",
    description: "Replace reads of the runtime's global-object slots with globalThis",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.globalKeys.size === 0) {
            log.info("no global-object slots known, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);

        let replaced = 0;
        let kept = 0;
        const keep = (reason: string, node: Node): void => {
            kept++;
            log.debug(`kept: ${reason}`, node);
        };
        traverse(program, {
            MemberExpression(path) {
                const node = path.node as MemberExpression;
                if (!matcher.isStorage(node.object)) return;
                const key = propertyKey(node);
                if (key === undefined || !runtime.globalKeys.has(key) || path.isWriteTarget()) return;
                const stale = effects.staleAt(node.object, [key]);
                if (stale !== undefined) return keep(stale.reason, stale.node);
                if (scopes.nameBoundAt(node.object, "globalThis") !== false) return keep("globalThis is a local name here", node);
                path.replace(at<IdentifierReference>({ type: "Identifier", name: "globalThis" }, node));
                replaced++;
            },
        });

        for (const variable of matcher.aliases) log.debug(`${variable.name} only ever holds ${runtime.storage}`, variable.identifiers[0] as unknown as Node);
        log.info(`replaced ${replaced} read(s) of ${runtime.storage}[${[...runtime.globalKeys].join(" | ")}] with globalThis, kept ${kept}; ${matcher.aliases.size} alias(es) of ${runtime.storage}`);
        return { changed: replaced, bindingsChanged: false, stats: { replaced, kept, aliases: matcher.aliases.size } };
    },
};
