import type { CallExpression, Expression, Node, Statement, VariableDeclaration } from "../core/ast.js";
import { isFunctionNode } from "../core/ast.js";
import { at, identifier, valueToNode } from "../core/build.js";
import type { ConstantEnv, FunctionLike } from "../core/constants.js";
import { constantEnv } from "../core/constants.js";
import type { Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import type { PassLog } from "../core/log.js";
import { printStatement } from "../core/print.js";
import type { Held } from "../core/sandbox.js";
import { Sandbox } from "../core/sandbox.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import { factKey } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

/** Builtins compute from their arguments (model 7); the few that don't throw in the pure realm (`HARDEN`). */
const PURE_GLOBALS: ReadonlySet<string> = new Set([
    "undefined",
    "NaN",
    "Infinity",
    "Array",
    "String",
    "Number",
    "Boolean",
    "Object",
    "Math",
    "JSON",
    "parseInt",
    "parseFloat",
    "isNaN",
    "isFinite",
    "encodeURIComponent",
    "decodeURIComponent",
    "encodeURI",
    "decodeURI",
    "escape",
    "unescape",
]);

/** A pass may have created these since the scope analysis (`valueToNode`). */
const VALUE_NAMES: ReadonlySet<string> = new Set(["undefined", "NaN", "Infinity"]);

/**
 * Left out: what reaches state outside the call (`this`, `super`, `import.meta`, `new.target`, `import()`), what
 * runs later (`yield`, `await`, classes), `try` (could catch a strict-mode error the sloppy program ignores), `with`,
 * tagged templates (strings object cached per site), `debugger`.
 */
const ALLOWED: ReadonlySet<string> = new Set([
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

/**
 * Makes the realm's builtins indistinguishable from the program's (model 7) or throwing, then freezes them all so a
 * write throws (strict mode). Run once, before any function is installed.
 *
 * Throws: what depends on more than the arguments or differs between engines (`Math.random`, approximated `Math`
 * functions, locale methods, `normalize`, regexes' engine-specific static state, `Function.prototype.toString`,
 * inconsistent sorts, non-integer `toString(radix)`), the `Function` constructor (would run in the guest's global
 * scope), and reflection that would reveal the freezing. Replacements keep `name` and `length`, with no `prototype`.
 */
const HARDEN = `(() => {
    "use strict";
    const define = Object.defineProperty, apply = Reflect.apply, ownKeys = Reflect.ownKeys, describe = Reflect.getOwnPropertyDescriptor, protoOf = Reflect.getPrototypeOf;
    const isInteger = Number.isInteger, valueOfNumber = Number.prototype.valueOf;
    const unavailable = (name, length) => {
        const method = { [name]() { throw new TypeError(name + " is not available in a pure evaluation"); } }[name];
        define(method, "length", { value: length });
        return method;
    };
    const block = (owner, key) => {
        const original = owner[key];
        define(owner, key, { value: unavailable(String(key), typeof original === "function" ? original.length : 0) });
    };
    const wrap = (owner, key, guard) => {
        const original = owner[key];
        const method = { [key](...args) { guard(this, args); return apply(original, this, args); } }[key];
        define(method, "length", { value: original.length });
        define(owner, key, { value: method });
    };
    block(Math, "random");
    for (const key of ["acos", "acosh", "asin", "asinh", "atan", "atanh", "atan2", "cbrt", "cos", "cosh", "exp", "expm1", "hypot", "log", "log1p", "log10", "log2", "pow", "sin", "sinh", "sqrt", "tan", "tanh"]) block(Math, key);
    for (const key of ["localeCompare", "toLocaleLowerCase", "toLocaleUpperCase", "normalize", "match", "matchAll", "search"]) block(String.prototype, key);
    for (const owner of [Object.prototype, Array.prototype, Number.prototype]) block(owner, "toLocaleString");
    for (const key of ["isFrozen", "isSealed", "isExtensible", "getOwnPropertyDescriptor", "getOwnPropertyDescriptors"]) block(Object, key);
    block(RegExp.prototype, "exec");
    block(Function.prototype, "toString");
    const sorting = (array, args) => {
        if (args[0] !== undefined) throw new TypeError("sorting with a comparator is not available in a pure evaluation");
        for (const key of ownKeys(array)) {
            const element = describe(array, key)?.value;
            if ((typeof element === "object" && element !== null) || typeof element === "function") throw new TypeError("sorting objects is not available in a pure evaluation");
        }
    };
    wrap(Array.prototype, "sort", sorting);
    if (typeof Array.prototype.toSorted === "function") wrap(Array.prototype, "toSorted", sorting);
    wrap(Number.prototype, "toString", (number, args) => {
        if (args[0] !== undefined && Number(args[0]) !== 10 && !isInteger(apply(valueOfNumber, number, []))) throw new TypeError("toString(radix) of a non-integer is not available in a pure evaluation");
    });
    const throwFunction = unavailable("Function", 1);
    define(Function.prototype, "constructor", { get: () => throwFunction(), set: undefined });
    const seen = new Set();
    const freeze = (object) => {
        if ((typeof object !== "object" && typeof object !== "function") || object === null || seen.has(object)) return;
        seen.add(object);
        for (const key of ownKeys(object)) {
            const descriptor = describe(object, key);
            if (descriptor === undefined) continue;
            if ("value" in descriptor) freeze(descriptor.value);
            else {
                freeze(descriptor.get);
                freeze(descriptor.set);
            }
        }
        freeze(protoOf(object));
        Object.freeze(object);
    };
    const hidden = [
        [][Symbol.iterator](),
        ""[Symbol.iterator](),
        new Map().entries(),
        new Set().values(),
        /a/[Symbol.matchAll](""),
        function* () {},
        async function () {},
        async function* () {},
        describe((function () { "use strict"; return arguments; })(), "callee")?.get,
    ];
    for (const root of hidden) freeze(root);
    freeze(globalThis);
})();`;

const SETUP_TIMEOUT_MS = 5000;
const CALL_TIMEOUT_MS = 250;
const LIMITS = { memoryBytes: 64 * 1024 * 1024, stackBytes: 1024 * 1024, timeoutMs: SETUP_TIMEOUT_MS };

interface Captures {
    readonly constants: Map<Variable, Value>;
    readonly functions: Map<Variable, FunctionLike>;
    readonly globals: Set<string>;
}

type Proof = { readonly ok: true; readonly captures: Captures } | { readonly ok: false; readonly reason: string; readonly node: Node };

const isWithin = (scope: Scope | null, fn: Node): boolean => {
    for (let current = scope; current !== null; current = current.upper) if ((current.block as unknown as Node) === fn) return true;
    return false;
};

/**
 * Proves functions pure: with primitive arguments, the result depends only on them, nothing outliving the call
 * changes, and the pure realm (`HARDEN`, strict mode) gives what the program gets.
 *
 * Rules: only `ALLOWED` node types; no async/generator (code runs after the call returns); no `**` (approximated);
 * function declarations only directly in a function body (block ones bind differently in strict mode). Names are its
 * own, `constantEnv` constants (read only), functions pure themselves and fixed where named (`functionAt`), or
 * `PURE_GLOBALS` (read only); not `arguments` (sloppy `arguments` aliases parameters).
 *
 * Soundness: every object reached is one it made, a pure function, or a builtin; distinguishing builtins throw and
 * the rest are frozen, so strict and sloppy code differ only where strict throws (no `this`, `arguments` or `try`).
 * A call that returns in the realm returned the same in the program. Relies on model 7.
 *
 * Mutual recursion is proven coinductively: a function whose proof is running is assumed pure; results under an
 * assumption are kept once it is proven, dropped otherwise.
 */
class PurityProver {
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
            return { ok: true, captures: { constants: new Map(), functions: new Map(), globals: new Set() } };
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
        const captures: Captures = { constants: new Map(), functions: new Map(), globals: new Set() };
        let refusal: { reason: string; node: Node } | undefined;
        traverse(root, {
            enter: (path) => {
                if (refusal !== undefined) return path.skip();
                const node = path.node;
                const reason = this.#nodeImpurity(node, path.parent, path.parentPath?.parent ?? null, path.key, root, captures);
                if (reason !== undefined) refusal = { reason, node };
            },
        });
        return refusal === undefined ? { ok: true, captures } : { ok: false, ...refusal };
    }

    #nodeImpurity(node: Node, parent: Node | null, grandparent: Node | null, key: string | null, root: FunctionLike, captures: Captures): string | undefined {
        if (!ALLOWED.has(node.type)) return `it uses ${node.type}`;
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
                return this.#nameImpurity(node, node.name, parent, key, root, captures);
            default:
                return undefined;
        }
    }

    #nameImpurity(node: Node, name: string, parent: Node | null, key: string | null, root: FunctionLike, captures: Captures): string | undefined {
        if (parent?.type === "MemberExpression" && key === "property" && !parent.computed) return undefined;
        if (parent?.type === "Property" && key === "key" && !parent.computed) return undefined;
        if (parent?.type === "LabeledStatement" || parent?.type === "BreakStatement" || parent?.type === "ContinueStatement") return undefined;
        const scopes = this.#scopes;
        const reference = scopes.referenceOf(node);
        if (reference === undefined) {
            if (scopes.variableOf(node) !== undefined) return undefined;
            // An identifier a pass made since the analysis (`undefined` for `void 0`).
            if (VALUE_NAMES.has(name) && !scopes.declaresName(name)) {
                captures.globals.add(name);
                return undefined;
            }
            return `it names ${name}, which the analysis doesn't know`;
        }
        const variable = scopes.staticVariableOf(node);
        if (variable === undefined) {
            // Writing one throws in the realm (the global object is frozen).
            if (!PURE_GLOBALS.has(name)) return `it uses the global ${name}`;
            captures.globals.add(name);
            return undefined;
        }
        if (name === "arguments" && variable.defs.length === 0) return "it uses arguments";
        if (isWithin(variable.scope, root)) return undefined;
        // A binding the function writes is neither a constant nor a function for good.
        const constant = this.#env.lookup?.(node as Expression);
        if (constant?.ok === true) {
            captures.constants.set(variable, constant.value);
            return undefined;
        }
        const fn = this.#env.functionAt(node);
        if (fn === undefined) return reference.isWrite() ? `it writes ${name}, which isn't its own` : `it reads ${name}, which isn't a constant or a function there`;
        const proof = this.prove(fn);
        if (!proof.ok) return `it uses ${name}, which isn't pure: ${proof.reason}`;
        captures.functions.set(variable, fn);
        return undefined;
    }

    /** All captures of a proven function and the pure functions it uses, or why they can't share one scope. */
    closure(variable: Variable, fn: FunctionLike): Captures | string {
        const all: Captures = { constants: new Map(), functions: new Map([[variable, fn]]), globals: new Set() };
        const queue: FunctionLike[] = [fn];
        const visited = new Set<FunctionLike>();
        for (let current = queue.pop(); current !== undefined; current = queue.pop()) {
            if (visited.has(current)) continue;
            visited.add(current);
            const proof = this.#proofs.get(current);
            if (proof === undefined || !proof.ok) return "a function it uses wasn't proven";
            for (const [captured, value] of proof.captures.constants) all.constants.set(captured, value);
            for (const name of proof.captures.globals) all.globals.add(name);
            for (const [captured, used] of proof.captures.functions) {
                all.functions.set(captured, used);
                queue.push(used);
            }
        }
        const names = new Map<string, Variable | undefined>();
        for (const name of all.globals) names.set(name, undefined);
        for (const captured of [...all.constants.keys(), ...all.functions.keys()]) {
            if (names.has(captured.name) && names.get(captured.name) !== captured) return `two of the names it uses are ${captured.name}`;
            names.set(captured.name, captured);
        }
        return all;
    }
}

/** Means the primitive whatever names are in scope. */
const literalText = (value: Value): string => {
    if (value === undefined) return "void 0";
    if (typeof value === "string") return JSON.stringify(value);
    if (typeof value !== "number") return String(value);
    if (Number.isNaN(value)) return "0 / 0";
    if (value === Number.POSITIVE_INFINITY) return "1 / 0";
    if (value === Number.NEGATIVE_INFINITY) return "-1 / 0";
    return Object.is(value, -0) ? "-0" : String(value);
};

const declarationOf = (name: string, fn: FunctionLike): Statement =>
    fn.type === "FunctionDeclaration"
        ? fn
        : at<VariableDeclaration>(
              {
                  type: "VariableDeclaration",
                  kind: "const",
                  declare: false,
                  declarations: [{ type: "VariableDeclarator", id: identifier(name, fn), init: fn, definite: false, start: fn.start, end: fn.end, range: fn.range }],
              },
              fn
          );

/** Captures are declared in a scope of their own so the harness's names can't meet theirs. */
const harnessOf = (name: string, captures: Captures): string => {
    const constants = [...captures.constants].map(([variable, value]) => `const ${variable.name} = ${literalText(value)};`);
    const functions = [...captures.functions].map(([variable, fn]) => printStatement(declarationOf(variable.name, fn)));
    const values = [...captures.functions.keys()].map((variable) => variable.name).join(", ");
    return `(() => {
    "use strict";
    const [run, functions] = (() => {
${[...constants, ...functions].join("\n")}
        return [${name}, [${values}]];
    })();
    for (const fn of functions) {
        Object.freeze(fn);
        if (Object.prototype.hasOwnProperty.call(fn, "prototype")) Object.freeze(fn.prototype);
    }
    return {
        call: (args) => {
            const value = run(...args);
            const type = typeof value;
            return type === "string" || type === "number" || type === "boolean" || value === null || value === undefined ? { value } : { type };
        },
    };
})()`;
};

interface Candidate {
    readonly call: CallExpression;
    readonly variable: Variable;
    readonly fn: FunctionLike;
    readonly args: readonly Value[];
}

/** Calls answered for good: not asked again in later rounds. */
const DECIDED = factKey<{ readonly decided: WeakSet<Node>; readonly logged: WeakSet<Node> }>("pure-calls");

const argsKey = (args: readonly Value[]): string =>
    args.map((value) => (typeof value === "string" ? JSON.stringify(value) : typeof value === "number" && Object.is(value, -0) ? "-0" : `${typeof value}:${String(value)}`)).join(",");

/**
 * Replaces calls of provably pure local functions with constant arguments by their primitive results, evaluated in
 * a QuickJS realm of their own (never the runtime's guest). Constant arguments evaluate without effects, so the
 * call's only effect is its result. Runs in the simplify group: arguments and captures become constants as it folds.
 */
export const pureCalls: Pass = {
    name: "pure-calls",
    description: "Replace calls of pure local functions with constant arguments by their results",
    async run({ program, log, scope, facts }: PassContext): Promise<PassResult> {
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
        const prover = new PurityProver(scopes, env, log);
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

        const replacements = new Map<Node, Node>();
        const sandbox = await Sandbox.create(LIMITS);
        try {
            const setup = sandbox.execute(HARDEN, SETUP_TIMEOUT_MS);
            if (!setup.ok) {
                log.warn(`couldn't set the pure realm up: ${setup.error}`);
                return { changed: 0 };
            }
            const harnesses = new Map<FunctionLike, Held | string>();
            const results = new Map<FunctionLike, Map<string, { value: Value } | string>>();
            for (const { call, variable, fn, args } of candidates) {
                let harness = harnesses.get(fn);
                if (harness === undefined) {
                    const captures = prover.closure(variable, fn);
                    const held = typeof captures === "string" ? undefined : sandbox.hold(harnessOf(variable.name, captures), SETUP_TIMEOUT_MS);
                    harness = typeof captures === "string" ? captures : held?.ok === true ? held.held : `the pure realm refused its code: ${held?.ok === false ? held.error : "no answer"}`;
                    harnesses.set(fn, harness);
                    if (typeof harness !== "string") log.debug(`evaluating calls of ${variable.name} in the pure realm`, fn);
                }
                if (typeof harness === "string") {
                    keep(harness, call, true);
                    continue;
                }
                let byArgs = results.get(fn);
                if (byArgs === undefined) {
                    byArgs = new Map();
                    results.set(fn, byArgs);
                }
                const key = argsKey(args);
                let result = byArgs.get(key);
                if (result === undefined) {
                    const answer = sandbox.invoke(["call"], args, CALL_TIMEOUT_MS, harness);
                    if (!answer.ok) {
                        result = answer.timedOut ? `it ran past ${CALL_TIMEOUT_MS} ms` : `it threw: ${answer.error}`;
                        // Its other calls would cost as much.
                        if (answer.timedOut) harnesses.set(fn, `a call of it ran past ${CALL_TIMEOUT_MS} ms`);
                    } else {
                        const returned = answer.value as { value?: Value; type?: string };
                        result =
                            "type" in returned
                                ? `it returns ${returned.type === "function" ? "a function" : `a${returned.type === "object" ? "n" : ""} ${String(returned.type)}`}`
                                : { value: returned.value };
                    }
                    byArgs.set(key, result);
                }
                if (typeof result === "string") {
                    keep(result, call, true);
                    continue;
                }
                const value = result.value;
                const replacement = valueToNode(value, call);
                const named = replacement.type === "UnaryExpression" ? replacement.argument : replacement;
                if (named.type === "Identifier" && scopes.declaresName(named.name)) {
                    keep(`its result is ${named.name}, a name the program declares`, call, true);
                    continue;
                }
                decided.add(call);
                replacements.set(call, replacement);
                counts.resolved++;
                if (typeof value === "string") {
                    counts.strings++;
                    counts.characters += value.length;
                }
                if (log.debugging) log.debug(`resolved to ${typeof value === "string" ? JSON.stringify(value.length > 40 ? `${value.slice(0, 40)}...` : value) : String(value)}`, call);
            }
        } finally {
            sandbox.dispose();
        }
        replaceNodes(program, replacements);
        log.info(`resolved ${counts.resolved} call(s) of pure functions (${counts.strings} to strings, ${counts.characters} characters in all), kept ${counts.kept}`);
        return { changed: counts.resolved, bindingsChanged: false, stats: counts };
    },
};
