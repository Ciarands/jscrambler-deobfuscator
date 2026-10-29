/**
 * Output metrics shared by the dev scripts (corpus runner, comparison with `main`). Diagnostics only: readability is
 * judged by reading the output, these just show where obfuscation is left and whether code went missing.
 */
import type { Node } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";

export const COUNTED = ["bytes", "machines", "switches", "functions", "deepCalls", "calls"] as const;
export type Counted = (typeof COUNTED)[number];
export type Metrics = Record<Counted, number> & { ms: number; error?: string };

/** The single statement of a loop body, looking through a one-statement block. */
const loneStatement = (body: Node): Node | undefined => (body.type === "BlockStatement" ? (body.body.length === 1 ? body.body[0] : undefined) : body);

/** A loop whose body is one `switch` on a variable: a flattened state machine, whatever loop form it took. */
const isMachine = (loop: Node): boolean => {
    if (loop.type !== "ForStatement" && loop.type !== "WhileStatement" && loop.type !== "DoWhileStatement") return false;
    const body = loneStatement(loop.body);
    return body?.type === "SwitchStatement" && (body.discriminant.type === "Identifier" || body.discriminant.type === "MemberExpression");
};

/**
 * - machines:  loops whose body is one `switch` on a variable: flattened machines left.
 * - deepCalls: calls like `a.b.c(...)`: wrapper / decoder calls left (also ordinary method chains).
 * - calls:     all calls. Restructuring passes must never lower this; a drop means code went missing.
 */
export const measure = (code: string, ms: number): Metrics => {
    const metrics: Metrics = { bytes: code.length, ms: Math.round(ms), machines: 0, switches: 0, functions: 0, deepCalls: 0, calls: 0 };
    traverse(parse(code), {
        enter(path) {
            const node = path.node;
            if (isMachine(node)) metrics.machines++;
            switch (node.type) {
                case "SwitchStatement":
                    metrics.switches++;
                    break;
                case "FunctionExpression":
                case "FunctionDeclaration":
                case "ArrowFunctionExpression":
                    metrics.functions++;
                    break;
                case "CallExpression":
                    metrics.calls++;
                    if (node.callee.type === "MemberExpression" && node.callee.object.type === "MemberExpression") metrics.deepCalls++;
                    break;
                default:
                    break;
            }
        },
    });
    return metrics;
};

export const errorMetrics = (ms: number, error: unknown): Metrics => ({
    bytes: 0,
    ms: Math.round(ms),
    machines: 0,
    switches: 0,
    functions: 0,
    deepCalls: 0,
    calls: 0,
    error: error instanceof Error ? error.message : String(error),
});
