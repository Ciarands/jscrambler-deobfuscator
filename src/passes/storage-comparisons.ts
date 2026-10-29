import type { Node } from "../core/ast.js";
import { memberPath } from "../core/ast.js";
import { valueToNode } from "../core/build.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import { storageMatcher } from "./emulate/storage.js";

const EQUALITY: Readonly<Record<string, true>> = { "===": true, "!==": true, "==": true, "!=": true };

interface Candidate {
    readonly node: Node;
    readonly op: string;
    readonly left: { readonly site: Node; readonly path: PropertyPath };
    readonly right: { readonly site: Node; readonly path: PropertyPath };
}

/**
 * Storage comparisons: `G.k.m[1][10] != G.k.m[3][10]` becomes the boolean it always is.
 *
 * jscrambler's opaque predicates compare cells of a matrix a prelude builder made (rows that point at each other, so
 * cells are compared by identity) and hide the result in `x || pred` conditions and loop tests. Both sides are static
 * storage paths; where the analysis finds nothing that may change either after the prelude (model 3: `G` changes only
 * through code that names its paths), each reads the snapshot's value. Reading data properties runs no code, and two
 * objects (identity) or two primitives compare without conversions, so the comparison has no effect and its value is
 * the one the guest computes: the literal replaces it, and simplify folds the conditions. An object against a
 * primitive (a conversion would call into the object) or a path through a getter stays.
 */
export const storageComparisons: Pass = {
    name: "storage-comparisons",
    description: "Fold equality tests between stable runtime values (matrix opaque predicates)",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined) return { changed: 0 };
        const scopes = scope();
        const matcher = storageMatcher(program, runtime, scopes);
        /** A static path below the storage object: its reference to `G` and the keys. */
        const storagePath = (node: Node): { site: Node; path: PropertyPath } | undefined => {
            const path = memberPath(node);
            return path !== undefined && matcher.isStorage(path.root) ? { site: path.root, path: path.keys } : undefined;
        };
        const candidates: Candidate[] = [];
        traverse(program, {
            BinaryExpression(path) {
                const node = path.node;
                if (EQUALITY[node.operator] !== true) return;
                const left = storagePath(node.left);
                const right = left === undefined ? undefined : storagePath(node.right);
                if (left !== undefined && right !== undefined) candidates.push({ node, op: node.operator, left, right });
            },
        });
        if (candidates.length === 0) return { changed: 0 };

        const { effects } = storageAnalysis(program, runtime, scopes, log);
        let kept = 0;
        const stable = candidates.filter(({ node, left, right }) => {
            const stale = effects.staleAt(left.site, left.path) ?? effects.staleAt(right.site, right.path);
            if (stale === undefined) return true;
            kept++;
            log.debug(`kept: ${stale.reason}`, node);
            return false;
        });
        const answers = stable.length === 0 ? [] : runtime.guest.compare(stable.map(({ op, left, right }) => ({ left: left.path, right: right.path, op })));
        const replacements = new Map<Node, Node>();
        for (const [i, candidate] of stable.entries()) {
            const answer = answers[i];
            if (answer?.ok !== true) {
                kept++;
                log.debug(`kept: ${answer?.reason ?? "no answer"}`, candidate.node);
                continue;
            }
            replacements.set(candidate.node, valueToNode(answer.value, candidate.node));
        }
        replaceNodes(program, replacements);
        log.info(`folded ${replacements.size} comparison(s) of runtime values; kept ${kept}`);
        return { changed: replacements.size, bindingsChanged: false, stats: { folded: replacements.size, kept } };
    },
};
