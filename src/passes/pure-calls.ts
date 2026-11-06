import type { CallExpression, FunctionLike, IdentifierReference, Node } from "../core/ast.js";
import { isFunctionNode } from "../core/ast.js";
import { valueToNode } from "../core/build.js";
import { GLOBALS } from "../core/builtins.js";
import type { ConstantEnv } from "../core/constants.js";
import { constantEnv } from "../core/constants.js";
import type { Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import type { OuterBinding } from "../core/interpret.js";
import { argumentsKey, Interpreter } from "../core/interpret.js";
import type { PassLog } from "../core/log.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { scopeWithin } from "../core/scope.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import { factKey } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { RUNTIME } from "./runtime/model.js";

/** A pass may have created these since the scope analysis (`valueToNode`). */
const VALUE_NAMES: ReadonlySet<string> = new Set(["undefined", "NaN", "Infinity"]);

/**
 * Left out: what reaches state outside the call (`this`, `super`, `import.meta`, `new.target`, `import()`), what
 * runs later (`yield`, `await`, classes), `try` (could catch a strict-mode error the sloppy program ignores), `with`,
 * tagged templates (strings object cached per site), `debugger`. The interpreter refuses more as it meets it.
 */
const CALL_PURITY_NODES: ReadonlySet<string> = new Set([
    "BlockStatement",
    "ExpressionStatement",
    "VariableDeclaration",
    "VariableDeclarator",
    "ReturnStatement",
    "IfStatement",
    "ForStatement",
    "ForInStatement",
    "ForOfStatement",
    "WhileStatement",
    "DoWhileStatement",
    "BreakStatement",
    "ContinueStatement",
    "SwitchStatement",
    "SwitchCase",
    "LabeledStatement",
    "EmptyStatement",
    "ThrowStatement",
    "FunctionDeclaration",
    "FunctionExpression",
    "ArrowFunctionExpression",
    "Identifier",
    "Literal",
    "UnaryExpression",
    "BinaryExpression",
    "LogicalExpression",
    "ConditionalExpression",
    "AssignmentExpression",
    "UpdateExpression",
    "SequenceExpression",
    "MemberExpression",
    "ChainExpression",
    "CallExpression",
    "NewExpression",
    "ArrayExpression",
    "ObjectExpression",
    "Property",
    "SpreadElement",
    "TemplateLiteral",
    "TemplateElement",
    "ParenthesizedExpression",
    "AssignmentPattern",
    "ArrayPattern",
    "ObjectPattern",
    "RestElement",
]);

/** Steps (evaluated nodes and builtin work) one call may take. */
const CALL_STEPS = 2_000_000;
/** All rounds of one input together; past it, calls stay as they are (partial output). */
const TOTAL_STEPS = 50_000_000;

type Proof = { readonly ok: true } | { readonly ok: false; readonly reason: string; readonly node: Node };

const PROVEN: Proof = { ok: true };

/**
 * Proves functions pure: with primitive arguments, the result depends only on them and nothing outliving the call
 * changes, so the interpreter's answer is the program's.
 *
 * Rules: only `CALL_PURITY_NODES` types; no async/generator (code runs after the call returns); no `**` (approximated);
 * function declarations only directly in a function body (block ones bind differently in strict mode). Names are its
 * own, `constantEnv` constants (read only), functions pure themselves and fixed where named (`functionAt`), or
 * modelled globals (`GLOBALS`, read only); not `arguments` (sloppy `arguments` aliases parameters).
 *
 * Soundness: every object reached is one the call made, a pure function or a modelled builtin; the interpreter
 * refuses writes to the others, members and conversions it doesn't model, and whatever strict and sloppy code treat
 * differently (no `this`, `arguments` or `try`). A call that returns in the interpreter returned the same in the
 * program. Relies on model 7.
 *
 * Mutual recursion is proven coinductively: a function whose proof is running is assumed pure; results under an
 * assumption are kept once it is proven, dropped otherwise.
 */
class CallPurityProver {
    readonly #scopes: ScopeInfo;
    readonly #env: ConstantEnv;
    readonly #log: PassLog;
    readonly #proofs = new Map<FunctionLike, Proof>();
    readonly #stack: FunctionLike[] = [];
    /** Successes resting on a still-open assumption, in proof order. */
    readonly #pending: { readonly fn: FunctionLike; readonly proof: Proof }[] = [];
    /** The lowest stack index of an assumption the current proof made. */
    #assumed = Number.POSITIVE_INFINITY;

    constructor(scopes: ScopeInfo, env: ConstantEnv, log: PassLog) {
        this.#scopes = scopes;
        this.#env = env;
        this.#log = log;
    }

    prove(fn: FunctionLike): Proof {
        const known = this.#proofs.get(fn);
        if (known !== undefined) return known;
        const running = this.#stack.indexOf(fn);
        if (running !== -1) {
            this.#assumed = Math.min(this.#assumed, running);
            return PROVEN;
        }
        const depth = this.#stack.length;
        const outer = this.#assumed;
        const mark = this.#pending.length;
        this.#assumed = Number.POSITIVE_INFINITY;
        this.#stack.push(fn);
        const proof = this.#check(fn);
        this.#stack.pop();
        if (!proof.ok) {
            // Assumptions only ever make a proof succeed: a failure is final, and what rested on this one goes.
            this.#proofs.set(fn, proof);
            this.#pending.length = mark;
            this.#log.debug(`not pure: ${proof.reason}`, proof.node);
        } else if (this.#assumed >= depth) {
            for (const pending of this.#pending.splice(mark)) this.#proofs.set(pending.fn, pending.proof);
            this.#proofs.set(fn, proof);
            this.#log.debug("proven pure", fn);
        } else {
            this.#pending.push({ fn, proof });
        }
        this.#assumed = Math.min(outer, this.#assumed);
        return proof;
    }

    #check(root: FunctionLike): Proof {
        let refusal: { reason: string; node: Node } | undefined;
        traverse(root, {
            enter: (path) => {
                if (refusal !== undefined) return path.skip();
                const node = path.node;
                const reason = this.#nodeImpurity(node, path.parent, path.parentPath?.parent ?? null, path.key, root);
                if (reason !== undefined) refusal = { reason, node };
            },
        });
        return refusal === undefined ? PROVEN : { ok: false, ...refusal };
    }

    #nodeImpurity(node: Node, parent: Node | null, grandparent: Node | null, key: string | null, root: FunctionLike): string | undefined {
        if (!CALL_PURITY_NODES.has(node.type)) return `it uses ${node.type}`;
        switch (node.type) {
            case "FunctionDeclaration":
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                if (node.async || node.generator) return "it is or makes an async or generator function";
                if (node.type === "FunctionDeclaration" && node !== root && !(parent?.type === "BlockStatement" && isFunctionNode(grandparent) && key === "body"))
                    return "it declares a function in a block";
                return undefined;
            case "BinaryExpression":
                return node.operator === "**" ? "it uses **, whose result is implementation-approximated" : undefined;
            case "AssignmentExpression":
                return node.operator === "**=" ? "it uses **=, whose result is implementation-approximated" : undefined;
            case "Identifier":
                return this.#nameImpurity(node, node.name, parent, key, root);
            default:
                return undefined;
        }
    }

    #nameImpurity(node: Node, name: string, parent: Node | null, key: string | null, root: FunctionLike): string | undefined {
        if (parent?.type === "MemberExpression" && key === "property" && !parent.computed) return undefined;
        if (parent?.type === "Property" && key === "key" && !parent.computed) return undefined;
        if (parent?.type === "LabeledStatement" || parent?.type === "BreakStatement" || parent?.type === "ContinueStatement") return undefined;
        const reference = this.#scopes.referenceOf(node);
        const variable = reference === undefined ? undefined : this.#scopes.staticVariableOf(node);
        if (variable !== undefined && !(name === "arguments" && variable.defs.length === 0) && scopeWithin(variable.scope, root)) return undefined;
        const binding = this.outer(node);
        if (binding === OWN) return undefined;
        if (typeof binding === "string") return binding;
        if (reference?.isWrite() === true) return `it writes ${name}, which isn't its own`;
        if (!("function" in binding)) return undefined;
        const proof = this.prove(binding.function);
        return proof.ok ? undefined : `it uses ${name}, which isn't pure: ${proof.reason}`;
    }

    /** What an identifier declared outside the function using it means (`OWN`: it declares a name). */
    outer(node: Node): OuterBinding | typeof OWN | string {
        const name = (node as IdentifierReference).name;
        const scopes = this.#scopes;
        const reference = scopes.referenceOf(node);
        if (reference === undefined) {
            if (scopes.variableOf(node) !== undefined) return OWN;
            // An identifier a pass made since the analysis (`undefined` for `void 0`).
            if (VALUE_NAMES.has(name) && scopes.namesGlobal(node)) return { global: name };
            return `it names ${name}, which the analysis doesn't know`;
        }
        const variable = scopes.staticVariableOf(node);
        if (variable === undefined) return GLOBALS.has(name) ? { global: name } : `it uses the global ${name}`;
        if (name === "arguments" && variable.defs.length === 0) return "it uses arguments";
        // A binding the function writes is neither a constant nor a function for good.
        const constant = this.#env.lookup?.(node as IdentifierReference);
        if (constant?.ok === true) return { value: constant.value };
        const fn = this.#env.functionAt(node);
        if (fn !== undefined) return { function: fn };
        return reference.isWrite() ? `it writes ${name}, which isn't its own` : `it reads ${name}, which isn't a constant or a function there`;
    }
}

const OWN: unique symbol = Symbol("own");

interface Candidate {
    readonly call: CallExpression;
    readonly variable: Variable;
    readonly fn: FunctionLike;
    readonly args: readonly Value[];
}

/** Calls answered for good: not asked again in later rounds. */
const DECIDED = factKey<{ readonly decided: WeakSet<Node>; readonly logged: WeakSet<Node> }>("pure-calls");
/** Interpreter steps spent for this input, over all rounds. */
const SPENT = factKey<{ steps: number }>("pure-calls steps");

/**
 * Replaces calls of provably pure local functions with constant arguments by their primitive results, computed by
 * the host-side interpreter (`core/interpret.ts`; no program code runs). Constant arguments evaluate without effects,
 * so the call's only effect is its result. Runs in the simplify group: arguments and captures become constants as it
 * folds.
 */
export const pureCalls: Pass = {
    name: "pure-calls",
    description: "Replace calls of pure local functions with constant arguments by their results",
    run({ program, log, scope, facts }: PassContext): PassResult {
        const scopes = scope();
        if (scopes.manager.scopes.some((s) => s.type === "with" || s.directCallToEvalScope)) {
            log.info("the program uses with or direct eval: names may not mean what they seem, nothing to do");
            return { changed: 0 };
        }
        let state = facts.get(DECIDED);
        if (state === undefined) {
            state = { decided: new WeakSet(), logged: new WeakSet() };
            facts.set(DECIDED, state);
        }
        const { decided, logged } = state;
        const env = constantEnv(scopes, log);
        const prover = new CallPurityProver(scopes, env, log);
        const counts = { resolved: 0, strings: 0, characters: 0, kept: 0 };
        const keep = (reason: string, node: Node, final: boolean): void => {
            if (final) {
                decided.add(node);
                counts.kept++;
            }
            if (logged.has(node)) return;
            logged.add(node);
            log.debug(`kept: ${reason}`, node);
        };

        const candidates: Candidate[] = [];
        traverse(program, {
            CallExpression(path) {
                const call = path.node;
                if (decided.has(call) || call.optional || call.callee.type !== "Identifier") return;
                const fn = env.functionAt(call.callee);
                const variable = scopes.variableOf(call.callee);
                if (fn === undefined || variable === undefined) return;
                const args: Value[] = [];
                for (const [index, arg] of call.arguments.entries()) {
                    const result = arg.type === "SpreadElement" ? undefined : evaluate(arg, env);
                    if (result?.ok !== true) return keep(`argument ${index + 1} isn't a constant`, call, false);
                    args.push(result.value);
                }
                const proof = prover.prove(fn);
                if (!proof.ok) return keep(`${variable.name} isn't pure: ${proof.reason}`, call, false);
                candidates.push({ call, variable, fn, args });
            },
        });
        if (candidates.length === 0) {
            log.info("no calls of pure functions with constant arguments");
            return { changed: 0 };
        }

        const spent = facts.get(SPENT) ?? { steps: 0 };
        facts.set(SPENT, spent);
        const exhausted = (left: number): void => log.warn(`the pure-call step budget of ${TOTAL_STEPS} is used up: ${left} call(s) left as they are`);
        if (spent.steps >= TOTAL_STEPS) {
            exhausted(candidates.length);
            return { changed: 0 };
        }
        const runtime = facts.get(RUNTIME);
        const aliases = new Map<string, Map<string, string>>();
        for (const { owner, alias, original } of runtime?.aliases ?? []) {
            if (owner.length === 0) continue;
            const name = owner.join(".");
            aliases.set(name, (aliases.get(name) ?? new Map()).set(alias, original));
        }
        const interpreter = new Interpreter({
            outer: (identifier) => {
                const binding = prover.outer(identifier);
                if (binding === OWN) return `it reads ${identifier.name}, a local the interpreter doesn't bind`;
                if (typeof binding !== "string" && "function" in binding && !prover.prove(binding.function).ok) return `${identifier.name} isn't pure`;
                return binding;
            },
            aliases,
        });
        const replacements = new Map<Node, Node>();
        const results = new Map<FunctionLike, Map<string, { value: Value } | string>>();
        /** Functions a call of ran past its budget: their other calls would cost as much. */
        const tooLong = new Set<FunctionLike>();
        for (const [index, { call, variable, fn, args }] of candidates.entries()) {
            const left = TOTAL_STEPS - spent.steps;
            if (left <= 0) {
                exhausted(candidates.length - index);
                break;
            }
            if (tooLong.has(fn)) {
                keep(`a call of it ran past ${CALL_STEPS} steps`, call, true);
                continue;
            }
            let byArgs = results.get(fn);
            if (byArgs === undefined) {
                byArgs = new Map();
                results.set(fn, byArgs);
                log.debug(`interpreting calls of ${variable.name}`, fn);
            }
            const key = argumentsKey(args);
            let result = byArgs.get(key);
            if (result === undefined) {
                const limit = Math.min(CALL_STEPS, left);
                const answer = interpreter.call(fn, args, limit);
                spent.steps += answer.steps;
                // Cut short by the total budget, not by its own length: undecided (the check above stops the loop).
                if (!answer.ok && answer.exhausted && limit < CALL_STEPS) continue;
                if (!answer.ok && answer.exhausted) tooLong.add(fn);
                result = answer.ok ? { value: answer.value } : answer.reason;
                byArgs.set(key, result);
            }
            if (typeof result === "string") {
                keep(result, call, true);
                continue;
            }
            const value = result.value;
            const replacement = valueToNode(value, call, scopes);
            decided.add(call);
            replacements.set(call, replacement);
            counts.resolved++;
            if (typeof value === "string") {
                counts.strings++;
                counts.characters += value.length;
            }
            if (log.debugging) log.debug(`resolved to ${typeof value === "string" ? JSON.stringify(value.length > 40 ? `${value.slice(0, 40)}...` : value) : String(value)}`, call);
        }
        replaceNodes(program, replacements);
        log.info(`resolved ${counts.resolved} call(s) of pure functions (${counts.strings} to strings, ${counts.characters} characters in all), kept ${counts.kept}`);
        return { changed: counts.resolved, bindingsChanged: false, stats: counts };
    },
};
