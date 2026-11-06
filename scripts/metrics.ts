/** Output metrics for the dev scripts. Diagnostics only: they show leftover obfuscation and missing code. */
import type { Node } from "../src/core/ast.js";
import { memberPath } from "../src/core/ast.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";

export const COUNTED = ["bytes", "machines", "switches", "functions", "deepCalls", "calls"] as const;
export type Counted = (typeof COUNTED)[number];
export type Metrics = Record<Counted, number> & { ms: number; error?: string };

const loneStatement = (body: Node): Node | undefined => (body.type === "BlockStatement" ? (body.body.length === 1 ? body.body[0] : undefined) : body);

const isMachine = (loop: Node): boolean => {
    if (loop.type !== "ForStatement" && loop.type !== "WhileStatement" && loop.type !== "DoWhileStatement") return false;
    const body = loneStatement(loop.body);
    return body?.type === "SwitchStatement" && (body.discriminant.type === "Identifier" || body.discriminant.type === "MemberExpression");
};

const chainKey = (node: Node): string | undefined => {
    const path = memberPath(node);
    return path !== undefined && path.root.type === "Identifier" ? [path.root.name, ...path.keys].join("\u0000") : undefined;
};

/** `function () { return typeof T === "function" ? T.apply(O, arguments) : T; }` */
const isWrapper = (fn: Node): boolean => {
    if (fn.type !== "FunctionExpression" || fn.body?.body.length !== 1) return false;
    const ret = fn.body.body[0];
    if (ret?.type !== "ReturnStatement" || ret.argument?.type !== "ConditionalExpression") return false;
    const { test, consequent, alternate } = ret.argument;
    if (test.type !== "BinaryExpression" || test.operator !== "===" || test.left.type !== "UnaryExpression" || test.left.operator !== "typeof") return false;
    const target = chainKey(test.left.argument);
    if (target === undefined || chainKey(alternate) !== target || consequent.type !== "CallExpression" || consequent.callee.type !== "MemberExpression") return false;
    const apply = consequent.callee;
    return !apply.computed && apply.property.type === "Identifier" && apply.property.name === "apply" && chainKey(apply.object) === target;
};

/**
 * - machines:  loops whose body is one `switch` on a variable (flattened machines left).
 * - deepCalls: `a.b.c(...)` and calls of a wrapper-assigned member: runtime/decoder calls left (also ordinary chains).
 * - calls:     restructuring passes must never lower this; a drop means code went missing.
 */
export const measure = (code: string, ms: number): Metrics => {
    const metrics: Metrics = { bytes: code.length, ms: Math.round(ms), machines: 0, switches: 0, functions: 0, deepCalls: 0, calls: 0 };
    const wrappers = new Set<string>();
    const shallow: string[] = [];
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
                case "AssignmentExpression": {
                    const key = node.left.type === "MemberExpression" && isWrapper(node.right) ? chainKey(node.left) : undefined;
                    if (key !== undefined) wrappers.add(key);
                    break;
                }
                case "CallExpression": {
                    metrics.calls++;
                    if (node.callee.type !== "MemberExpression") break;
                    if (node.callee.object.type === "MemberExpression") metrics.deepCalls++;
                    else {
                        const key = chainKey(node.callee);
                        if (key !== undefined) shallow.push(key);
                    }
                    break;
                }
                default:
                    break;
            }
        },
    });
    for (const key of shallow) if (wrappers.has(key)) metrics.deepCalls++;
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
