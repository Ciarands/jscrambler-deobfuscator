import type { CallExpression, Expression, Function as FunctionNode, MemberExpression, Node } from "../core/ast.js";
import { isFunctionNode, memberPath } from "../core/ast.js";
import { valueToNode } from "../core/build.js";
import { pushAll } from "../core/list.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { reachingDynamicUse, strayReference, survey } from "./code-locks.js";
import { builderOf, definitionOf } from "./emulate/builders.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import { storageMatcher } from "./emulate/storage.js";

/** A literal argument or comparand: a literal, or a minus or `!` on one. */
const isLiteral = (node: Node): boolean =>
    (node.type === "Literal" && !("regex" in node && node.regex !== undefined && node.regex !== null)) ||
    (node.type === "UnaryExpression" && (node.operator === "-" || node.operator === "!") && node.argument.type === "Literal");

interface GateCall {
    readonly call: CallExpression;
    readonly path: PropertyPath;
}

/** A test made only of lock calls compared with literals, and the value it has where the checks pass. */
interface Gate {
    readonly test: Expression;
    readonly value: boolean;
    readonly calls: readonly GateCall[];
}

const GLOBAL_OBJECT_NAMES: ReadonlySet<string> = new Set(["globalThis", "window", "self"]);

/**
 * Domain locks: tests like `G.k.m(0, false, 105006) === 349182763 || ...` gating the program on a hash of the host.
 * Model 5 says the environment passes the runtime's checks (domain locks included), so such a test holds (`||` of
 * `===`/`==`) or fails (`&&` of `!==`/`!=`; `!` flips either).
 *
 * A lock qualifies when its builder reads the host (other hashes are hash-predicates' business) and nothing reaches
 * it but the gates' calls, as in code-locks' full mode (model 2). A test qualifies when every comparison is a
 * literal-argument call of a qualifying lock against a literal. Dropping the calls drops no effect: a domain lock's
 * code changes only objects its builder made (model 5, not proven).
 */
export const domainLocks: Pass = {
    name: "domain-locks",
    description: "Answer the runtime's domain-lock tests with what the licensed host gives (model 5)",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined) return { changed: 0 };
        const scopes = scope();
        const matcher = storageMatcher(program, runtime, scopes);
        /** `G.k.m(literals...)` compared with a literal by one of `operators`. */
        const comparison = (node: Node, operators: ReadonlySet<string>): GateCall | undefined => {
            if (node.type !== "BinaryExpression" || !operators.has(node.operator) || node.left.type === "PrivateIdentifier") return undefined;
            const [call, other] = node.left.type === "CallExpression" ? [node.left, node.right] : [node.right, node.left];
            if (call.type !== "CallExpression" || call.optional || !isLiteral(other) || !call.arguments.every((arg) => arg.type !== "SpreadElement" && isLiteral(arg))) return undefined;
            const path = memberPath(call.callee);
            return path !== undefined && path.keys.length === 2 && matcher.isStorage(path.root) ? { call, path: path.keys } : undefined;
        };
        const gateOf = (test: Expression): Gate | undefined => {
            if (test.type === "UnaryExpression" && test.operator === "!") {
                const inner = gateOf(test.argument);
                return inner === undefined ? undefined : { test, value: !inner.value, calls: inner.calls };
            }
            const value = test.type === "LogicalExpression" ? test.operator === "||" : test.type === "BinaryExpression" && (test.operator === "===" || test.operator === "==");
            const joiner = value ? "||" : "&&";
            const operators: ReadonlySet<string> = new Set(value ? ["===", "=="] : ["!==", "!="]);
            const calls: GateCall[] = [];
            const collect = (node: Node): boolean => {
                if (node.type === "LogicalExpression" && node.operator === joiner) return collect(node.left) && collect(node.right);
                const found = comparison(node, operators);
                if (found !== undefined) calls.push(found);
                return found !== undefined;
            };
            return collect(test) ? { test, value, calls } : undefined;
        };

        const gates: Gate[] = [];
        traverse(program, {
            enter(path) {
                const node = path.node;
                if (node.type !== "IfStatement" && node.type !== "ConditionalExpression") return;
                const gate = gateOf(node.test);
                if (gate !== undefined) gates.push(gate);
            },
        });
        if (gates.length === 0) return { changed: 0 };

        const callsOf = new Map<string, GateCall[]>();
        for (const gate of gates) for (const call of gate.calls) callsOf.set(JSON.stringify(call.path), [...(callsOf.get(JSON.stringify(call.path)) ?? []), call]);
        const { dynamic } = survey(program, matcher, scopes);
        const { effects } = storageAnalysis(program, runtime, scopes, log);
        const verdicts = new Map<string, boolean>();
        for (const [id, calls] of callsOf) {
            const path = (calls[0] as GateCall).path;
            const name = `${runtime.storage}.${path.join(".")}`;
            const definition = definitionOf(runtime, matcher.isStorage, path.slice(0, 1), true);
            const refusal = ((): { reason: string; node?: Node } | undefined => {
                if (typeof definition === "string") return { reason: definition };
                const builder = builderOf(definition.iife, scopes);
                if (typeof builder === "string") return { reason: builder, node: definition.iife };
                const method = builder.methods.get(path[1] as string);
                if (method === undefined) return { reason: `its builder gives it no plain function ${path[1] as string}`, node: definition.iife };
                if (!reachesHost(definition.iife, method, scopes)) return { reason: "it reads nothing of the host", node: method };
                const reaching = reachingDynamicUse(dynamic, path[0] as string, definition.statement, runtime, scopes, effects);
                if (reaching !== undefined) return { reason: `${runtime.storage} is used as a value or read with a computed key once the lock is built, which may reach it`, node: reaching };
                const callees = new Set(calls.map(({ call }) => (call.callee as MemberExpression).object as Node));
                const stray = strayReference(path, callees, definition.statement, program, runtime, matcher, effects);
                if (stray !== undefined) return { reason: `${runtime.storage}.${path[0]} is used other than by lock tests, its builder and unused wrappers`, node: stray };
                return undefined;
            })();
            verdicts.set(id, refusal === undefined);
            if (refusal === undefined) log.debug(`${name} is a domain lock: it reads the host, and only lock tests reach it (${calls.length} call(s))`);
            else log.debug(`${name} is no domain lock: ${refusal.reason}`, refusal.node);
        }

        const replacements = new Map<Node, Node>();
        for (const gate of gates) {
            if (!gate.calls.every(({ path }) => verdicts.get(JSON.stringify(path)) === true)) continue;
            log.debug(`a domain-lock test: the licensed host makes it ${String(gate.value)}`, gate.test);
            replacements.set(gate.test, valueToNode(gate.value, gate.test, scopes));
        }
        replaceNodes(program, replacements);
        log.info(`answered ${replacements.size} domain-lock test(s) of ${gates.length} candidate(s)`);
        return { changed: replacements.size, bindingsChanged: false, stats: { answered: replacements.size, candidates: gates.length } };
    },
};

/**
 * Whether a call of `method` may read the host: it, or a function of its builder it names (transitively), names the
 * global object (`globalThis`, `window`, `self`, the global ones) or a builder local some write gives it.
 */
const reachesHost = (iife: FunctionNode, method: FunctionNode, scopes: ScopeInfo): boolean => {
    const isGlobalObject = (node: Node | null): boolean => node?.type === "Identifier" && GLOBAL_OBJECT_NAMES.has(node.name) && scopes.isGlobalReference(node);
    const holders = new Set<Variable>();
    const functions = new Map<Variable, Node[]>();
    const written = (target: Node, value: Node | null): void => {
        const variable = target.type === "Identifier" ? scopes.variableOf(target) : undefined;
        if (variable === undefined || value === null) return;
        if (isGlobalObject(value)) holders.add(variable);
        if (isFunctionNode(value)) functions.set(variable, [...(functions.get(variable) ?? []), value]);
    };
    traverse(iife, {
        VariableDeclarator(path) {
            written(path.node.id, path.node.init);
        },
        AssignmentExpression(path) {
            if (path.node.operator === "=") written(path.node.left, path.node.right);
        },
        FunctionDeclaration(path) {
            const node = path.node as Node;
            if (node.type === "FunctionDeclaration" && node.id !== null) written(node.id, node);
        },
    });
    const seen = new Set<Node>();
    const work: Node[] = [method];
    for (let fn = work.pop(); fn !== undefined; fn = work.pop()) {
        if (seen.has(fn)) continue;
        seen.add(fn);
        let found = false;
        traverse(fn, {
            Identifier(path) {
                const variable = scopes.variableOf(path.node);
                if (isGlobalObject(path.node) || (variable !== undefined && holders.has(variable))) found = true;
                if (variable !== undefined) pushAll(work, functions.get(variable) ?? []);
            },
        });
        if (found) return true;
    }
    return false;
};
