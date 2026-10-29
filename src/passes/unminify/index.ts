import type { Statement } from "../../core/ast.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import { UnminifyContext } from "./context.js";
import { rewriteExpression } from "./expressions.js";
import { expandStatements, mergeElseIf, rewriteStatement } from "./statements.js";

/** Rewrites of one node in a row (each one step: `!(1 === x)` -> `1 !== x` -> `x !== 1`). More means a loop. */
const MAX_STEPS = 16;

/**
 * Readability rewrites webcrack's unminify makes that our passes don't already, in one walk. Every rewrite is exact:
 *
 * - block-statements: `if (a) b();` -> `if (a) { b(); }` (if/loop bodies), `() => (a, b)` -> `() => { a; return b; }`
 * - split-variable-declarations: `var a = 1, b = 2;` -> `var a = 1; var b = 2;`
 * - split-for-loop-vars: `for (var a = 1, i = 0; i < n; i++)` -> `var a = 1; for (var i = 0; ...)` (leading `var`
 *   declarators the test and update don't use)
 * - computed keys: `{ "a": 1 }` -> `{ a: 1 }`, `x["a"]` -> `x.a` (not `__proto__`, not a class `constructor`, not
 *   `static prototype`)
 * - shorthand: `{ a: a }` -> `{ a }` (not `__proto__`)
 * - for-to-while: `for (; a;)` -> `while (a)`
 * - invert-boolean-logic: `!(a === b)` -> `a !== b`, `!(a && b)` -> `!a || !b` (equality only: NaN)
 * - logical-to-if: `a && b();` -> `if (a) { b(); }` (statements only)
 * - merge-else-if: `else { if (b) {} }` -> `else if (b) {}`
 * - remove-double-not: `!!x` -> `x` where only its truthiness is used
 * - string-literal-in-template-literal: `` `a${"b"}` `` -> `` `ab` `` (not tagged)
 * - ternary-to-if: `a ? b() : c();` and `return a ? b : c;` -> `if`/`else`
 * - truncate-number-literal: `x & 4294967297` -> `x & 1` (what the operator makes of the number)
 * - typeof-undefined: `typeof x > "u"` -> `typeof x === "undefined"`
 * - unary-expressions: `void x;`, `!x;`, `typeof x;` -> `x;` (not `typeof` of a maybe-undeclared global; `void 0;`
 *   goes); `return void x;` -> `x; return;`
 * - yoda: `1 === x` -> `x === 1` (constant on the left, not on the right)
 *
 * Covered before this pass: sequences (normalize), `!0`/`!1` (normalize), `void 0`, `1 / 0`, string and number
 * folding (simplify); literals print canonically (the printer ignores their source spelling). Not done:
 * `JSON.parse("...")` -> literal (exact only if nothing changes the builtin, which nothing here can prove).
 *
 * Changing statement values (`a && b();` -> `if (a) { b(); }`, dropping `void 0;`) relies on the semantic model's
 * "the script's completion value is unused": only an eval of the whole script would see it.
 *
 * Runs last: it only changes how the code reads, and the passes before it expect the minified shapes.
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
                    case "BlockStatement":
                    case "StaticBlock":
                        expandStatements(node.body as Statement[], context);
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
                mergeElseIf(path.node, context);
            },
        });

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
