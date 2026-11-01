import type { Statement } from "../../core/ast.js";
import { isFunctionNode } from "../../core/ast.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import { UnminifyContext } from "./context.js";
import { rewriteExpression } from "./expressions.js";
import { expandStatements, mergeElseIf, removeDeclarators, rewriteStatement, unlabelStatements } from "./statements.js";

/** Each rewrite is one step (`!(1 === x)` -> `1 !== x` -> `x !== 1`); more than this means a loop. */
const MAX_STEPS = 16;

/**
 * Exact readability rewrites webcrack's unminify makes that earlier passes don't, in one walk. Every refusal case
 * (`__proto__`, class `constructor`, NaN for inverted logic, maybe-undeclared `typeof`, tagged templates) lives with
 * its rewrite.
 *
 * Changing statement values (`a && b();` -> `if (a) { b(); }`, dropping `void 0;`) relies on the semantic model's
 * "the script's completion value is unused": only an eval of the whole script would see it.
 *
 * Runs last: the passes before it expect the minified shapes.
 */
export const unminify: Pass = {
    name: "unminify",
    description: "Readability rewrites: blocks, if/else for &&/?:, split declarations, plain keys, natural comparisons",
    run({ program, log, scope }: PassContext): PassResult {
        const context = new UnminifyContext(scope(), log);

        const rewrite = (path: Path): void => {
            for (let step = 0; step < MAX_STEPS; step++) {
                const statement = rewriteStatement(path, context);
                if (statement === null) return;
                const replacement = statement ?? rewriteExpression(path, context);
                if (replacement === undefined || replacement === path.node) return;
                path.replace(replacement);
            }
            log.warn(`stopped after ${MAX_STEPS} rewrites of one node`, path.node);
        };

        traverse(program, {
            enter(path) {
                const node = path.node;
                switch (node.type) {
                    case "Program":
                    case "StaticBlock":
                        expandStatements(node.body as Statement[], context);
                        return;
                    case "BlockStatement":
                        expandStatements(node.body, context, isFunctionNode(path.parent) && path.key === "body");
                        return;
                    case "SwitchCase":
                        expandStatements(node.consequent, context);
                        return;
                    default:
                        break;
                }
                rewrite(path);
            },
            exit(path) {
                const node = path.node;
                if (node.type === "Program" || node.type === "StaticBlock") unlabelStatements(node.body as Statement[], context);
                else if (node.type === "BlockStatement") unlabelStatements(node.body, context, isFunctionNode(path.parent) && path.key === "body");
                else if (node.type === "SwitchCase") unlabelStatements(node.consequent, context);
                mergeElseIf(node, context);
            },
        });
        if (context.unusedDeclarators.size > 0) removeDeclarators(program, context.unusedDeclarators);

        const stats = context.counts;
        const changed = Object.values(stats).reduce((sum, count) => sum + count, 0);
        log.info(
            `${changed} rewrite(s): ${Object.entries(stats)
                .filter(([, count]) => count > 0)
                .map(([name, count]) => `${name}=${count}`)
                .join(" ")}`
        );
        return { changed, stats };
    },
};
