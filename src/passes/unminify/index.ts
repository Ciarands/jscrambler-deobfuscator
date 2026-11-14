import type { Statement } from "../../core/ast.js";
import { isFunctionNode } from "../../core/ast.js";
import { ScopeInfo } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import { UnminifyContext } from "./context.js";
import { placeDeclarations } from "./declarations.js";
import { objectsFromEntryLists } from "./entries.js";
import { rewriteExpression } from "./expressions.js";
import { expandStatements, mergeElseIf, removeDeclarators, rewriteStatement, unlabelStatements } from "./statements.js";

/** Each rewrite is one step (`!(1 === x)` -> `1 !== x` -> `x !== 1`); more than this means a loop. */
const MAX_STEPS = 16;

/** The statement list a node holds, and whether it is a function's body (a block may end it with a `return;`). */
const statementList = (path: Path): { list: Statement[]; functionBody: boolean } | undefined => {
    const node = path.node;
    switch (node.type) {
        case "Program":
        case "StaticBlock":
            return { list: node.body as Statement[], functionBody: false };
        case "BlockStatement":
            return { list: node.body, functionBody: isFunctionNode(path.parent) && path.key === "body" };
        case "SwitchCase":
            return { list: node.consequent, functionBody: false };
        default:
            return undefined;
    }
};

/**
 * Exact readability rewrites webcrack's unminify makes that earlier passes don't, in one walk. Every refusal case
 * (`__proto__`, class `constructor`, NaN for inverted logic, maybe-undeclared `typeof`, tagged templates) lives with
 * its rewrite.
 *
 * Changing statement values (`a && b();` -> `if (a) { b(); }`, dropping `void 0;`) relies on the semantic model's
 * "the script's completion value is unused": only an eval of the whole script would see it.
 *
 * Runs last: the passes before it expect the minified shapes. Declarations move last of all, on a fresh scope analysis
 * of the otherwise final tree (`placeDeclarations`).
 */
export const unminify: Pass = {
    name: "unminify",
    description: "Readability rewrites: blocks, if/else for &&/?:, split declarations, plain keys, natural comparisons, declarations at first assignment",
    run({ program, log, scope }: PassContext): PassResult {
        const context = new UnminifyContext(program, scope(), log);
        let stoppedEarly = 0;

        const rewrite = (path: Path): void => {
            for (let step = 0; step < MAX_STEPS; step++) {
                const statement = rewriteStatement(path, context);
                if (statement === null) return;
                const replacement = statement ?? rewriteExpression(path, context);
                if (replacement === undefined || replacement === path.node) return;
                path.replace(replacement);
            }
            stoppedEarly = 1;
            log.warn(`stopped after ${MAX_STEPS} rewrites of one node: this ${path.node.type} may still have rewrites left undone`, path.node);
        };

        objectsFromEntryLists(program, context);
        traverse(program, {
            enter(path) {
                const statements = statementList(path);
                if (statements === undefined) rewrite(path);
                else expandStatements(statements.list, context, statements.functionBody);
            },
            exit(path) {
                const statements = statementList(path);
                if (statements !== undefined) unlabelStatements(statements.list, context, statements.functionBody);
                mergeElseIf(path.node, context);
            },
        });
        if (context.unusedDeclarators.size > 0) removeDeclarators(program, context.unusedDeclarators);
        placeDeclarations(program, new ScopeInfo(program), context);

        const counts = context.counts;
        const changed = Object.values(counts).reduce((sum, count) => sum + count, 0);
        log.info(
            `${changed} rewrite(s): ${Object.entries(counts)
                .filter(([, count]) => count > 0)
                .map(([name, count]) => `${name}=${count}`)
                .join(" ")}`
        );
        return { changed, stats: { ...counts, stoppedEarly } };
    },
};
