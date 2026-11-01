import type { ArrowFunctionExpression, Function as FunctionNode, IdentifierReference, MemberExpression, Node, VariableDeclaration } from "./ast.js";
import type { JsValue, Run } from "./builtins.js";
import {
    ArrayObject,
    Bound,
    Closure,
    copyOwn,
    deleteMember,
    EXHAUSTED,
    forInKeys,
    getMember,
    GLOBALS,
    hasProperty,
    isCallable,
    isObject,
    iterate,
    MAX_STRING,
    Native,
    PlainObject,
    Refused,
    refuse,
    setMember,
    shapeOf,
    Thrown,
    thrown,
    toNum,
    toPrimitive,
    toStr,
    truthy,
    typeOf,
} from "./builtins.js";
import type { Value } from "./evaluate.js";
import { binary, unary } from "./evaluate.js";
import { bindingNames, hoistedDeclarations } from "./hoisting.js";

type FunctionLike = FunctionNode | ArrowFunctionExpression;

/** What a name the interpreted code doesn't declare stands for. */
export type OuterBinding = { readonly value: Value } | { readonly function: FunctionLike } | { readonly global: string };

export type Answer =
    | { readonly ok: true; readonly value: Value; readonly steps: number }
    /** `exhausted`: the step budget ran out (another budget might answer). */
    | { readonly ok: false; readonly reason: string; readonly steps: number; readonly exhausted: boolean };

export interface InterpreterOptions {
    /** A name the code doesn't declare: what it is, or why it can't be used. Asked once per identifier node. */
    readonly outer: (identifier: IdentifierReference) => OuterBinding | string;
    /** Builtin aliases the program added (model 7): by owner (`String.prototype`), the alias's original name. */
    readonly aliases?: ReadonlyMap<string, ReadonlyMap<string, string>>;
}

/** Nested interpreted calls; deeper ones refuse (host stack). */
const MAX_DEPTH = 200;

const TDZ: unique symbol = Symbol("uninitialized");

interface Slot {
    value: JsValue | typeof TDZ;
    readonly mutable: boolean;
}

class Env {
    readonly slots = new Map<string, Slot>();
    constructor(readonly parent: Env | null) {}
}

interface Jump {
    readonly type: "break" | "continue";
    readonly label: string | undefined;
}

interface Return {
    readonly type: "return";
    readonly value: JsValue;
}

type Completion = Jump | Return | undefined;

const BREAK: Jump = { type: "break", label: undefined };
const CONTINUE: Jump = { type: "continue", label: undefined };
const NO_LABELS: readonly string[] = [];

/** Unwinds an optional chain that met `null`/`undefined` to its `ChainExpression`. */
const SHORT_CIRCUIT = { shortCircuit: true };

interface Lexical {
    readonly name: string;
    readonly constant: boolean;
}

interface Plan {
    readonly names: readonly string[];
    /** Every parameter a plain name: no parameter expressions, no destructuring. */
    readonly simple: boolean;
    readonly vars: readonly string[];
    readonly functions: readonly FunctionNode[];
    readonly lexical: readonly Lexical[];
}

/** Statement-list `let`/`const` names; classes, block functions and `using` refuse. */
const lexicalOf = (statements: readonly Node[]): Lexical[] => {
    const names: Lexical[] = [];
    for (const statement of statements) {
        if (statement.type === "VariableDeclaration") {
            if (statement.kind === "var") continue;
            if (statement.kind !== "let" && statement.kind !== "const") refuse(`it uses ${statement.kind} declarations`);
            for (const declarator of statement.declarations) for (const name of bindingNames(declarator.id)) names.push({ name, constant: statement.kind === "const" });
        } else if (statement.type === "ClassDeclaration") {
            refuse("it declares a class");
        } else if (statement.type === "FunctionDeclaration") {
            refuse("it declares a function in a block");
        }
    }
    return names;
};

const declare = (env: Env, lexical: readonly Lexical[]): Env => {
    if (lexical.length === 0) return env;
    const scoped = new Env(env);
    for (const { name, constant } of lexical) scoped.slots.set(name, { value: TDZ, mutable: !constant });
    return scoped;
};

const continues = (completion: Completion, labels: readonly string[]): boolean =>
    completion === undefined || (completion.type === "continue" && (completion.label === undefined || labels.includes(completion.label)));

/** What a loop the body left completes with: an unlabelled break ends it normally. */
const exitOf = (completion: Completion): Completion => (completion?.type === "break" && completion.label === undefined ? undefined : completion);

const isLoop = (node: Node): boolean =>
    node.type === "ForStatement" || node.type === "ForInStatement" || node.type === "ForOfStatement" || node.type === "WhileStatement" || node.type === "DoWhileStatement";

const unparenthesized = (node: Node): Node => (node.type === "ParenthesizedExpression" ? unparenthesized(node.expression) : node);

const staticKey = (key: Node): string => {
    if (key.type === "Identifier") return key.name;
    if (key.type === "Literal" && key.value !== null && typeof key.value !== "object") return String(key.value);
    return refuse(`it uses a ${key.type} key`);
};

type Reference = { readonly identifier: IdentifierReference } | { readonly object: JsValue; readonly key: string };

/** Tells primitive argument lists apart exactly (`-0`, `NaN`, `"1"` and `1`), for caching answers. */
export const argumentsKey = (args: readonly Value[]): string =>
    args.map((arg) => (typeof arg === "string" ? JSON.stringify(arg) : Object.is(arg, -0) ? "-0" : `${typeof arg}:${String(arg)}`)).join(",");

/**
 * Runs calls of functions over the AST on the host, without executing program code: environments, statements and
 * expressions are the interpreter's, operators on primitives are `evaluate.ts`'s, builtins `builtins.ts`'s. Covers
 * what the purity provers admit: no `this`, `arguments`, `try`, classes, generators, `async`, `with` or getters;
 * whatever else it meets refuses. A throw is no answer (no `try` could catch it), so only paths that return need
 * the program's order of effects. Steps (evaluated nodes and builtin work) are counted against a budget, so an
 * answer doesn't depend on the host's speed. Results are only primitives.
 */
export class Interpreter {
    readonly #outer: InterpreterOptions["outer"];
    readonly #aliases: ReadonlyMap<string, ReadonlyMap<string, string>>;
    readonly #outerValues = new Map<Node, JsValue>();
    readonly #closures = new Map<FunctionLike, Closure>();
    readonly #plans = new WeakMap<Node, Plan>();
    readonly #lexical = new WeakMap<Node, readonly Lexical[]>();
    #steps = 0;
    #limit = 0;
    #depth = 0;
    readonly #run: Run;

    constructor(options: InterpreterOptions) {
        this.#outer = options.outer;
        this.#aliases = options.aliases ?? new Map();
        this.#run = {
            step: (count) => {
                this.#steps += count;
                if (this.#steps > this.#limit) throw EXHAUSTED;
            },
            call: (callee, self, args) => this.#callValue(callee, self, args),
            aliasOf: (owner, name) => this.#aliases.get(owner)?.get(name),
            hasAliases: (owner) => (this.#aliases.get(owner)?.size ?? 0) > 0,
        };
    }

    /** Calls `fn` (closed over the outer bindings only) with `args`, within `maxSteps` steps. */
    call(fn: FunctionLike, args: readonly Value[], maxSteps: number): Answer {
        this.#steps = 0;
        this.#limit = maxSteps;
        this.#depth = 0;
        try {
            const result = this.#invoke(this.#closureOf(fn), args);
            if (isObject(result)) return { ok: false, reason: `it returns ${isCallable(result) ? "a function" : "an object"}`, steps: this.#steps, exhausted: false };
            return { ok: true, value: result, steps: this.#steps };
        } catch (error) {
            const steps = Math.min(this.#steps, maxSteps);
            if (error === EXHAUSTED) return { ok: false, reason: `it ran past ${maxSteps} steps`, steps, exhausted: true };
            const reason =
                error instanceof Refused
                    ? error.reason
                    : error instanceof Thrown
                      ? `it threw: ${error.message}`
                      : `it threw on the host: ${error instanceof Error ? error.message : "an unknown error"}`;
            return { ok: false, reason, steps, exhausted: false };
        }
    }

    #step(): void {
        if (++this.#steps > this.#limit) throw EXHAUSTED;
    }

    #closureOf(fn: FunctionLike): Closure {
        let closure = this.#closures.get(fn);
        if (closure === undefined) {
            closure = new Closure(fn, null);
            this.#closures.set(fn, closure);
        }
        return closure;
    }

    #outerValue(identifier: IdentifierReference): JsValue {
        if (this.#outerValues.has(identifier)) return this.#outerValues.get(identifier);
        const binding = this.#outer(identifier);
        let resolved: JsValue;
        if (typeof binding === "string") return refuse(binding);
        if ("value" in binding) resolved = binding.value;
        else if ("function" in binding) resolved = this.#closureOf(binding.function);
        else if (GLOBALS.has(binding.global)) resolved = GLOBALS.get(binding.global);
        else return refuse(`it uses the global ${binding.global}, which isn't modelled`);
        this.#outerValues.set(identifier, resolved);
        return resolved;
    }

    // ------------------------------------------------------------ calls

    #callValue(callee: JsValue, self: JsValue, args: readonly JsValue[]): JsValue {
        this.#step();
        if (callee instanceof Closure) return this.#invoke(callee, args);
        if (callee instanceof Native && callee.call !== undefined) return callee.call(self, args, this.#run);
        if (callee instanceof Bound) return this.#callValue(callee.target, callee.self, [...callee.args, ...args]);
        return thrown("TypeError: not a function");
    }

    #planOf(fn: FunctionLike): Plan {
        const known = this.#plans.get(fn);
        if (known !== undefined) return known;
        if (fn.async || fn.generator) refuse("it is or makes an async function or a generator");
        const names: string[] = [];
        for (const param of fn.params) {
            if (param.type === "TSParameterProperty") refuse("it has a parameter property");
            bindingNames(param.type === "RestElement" ? param.argument : (param as Node), new Set()).forEach((name) => names.push(name));
        }
        const body = fn.body;
        const statements: readonly Node[] = body !== null && body.type === "BlockStatement" ? body.body : [];
        const hoisted = { vars: new Set<string>(), functions: [] as FunctionNode[] };
        for (const statement of statements) hoistedDeclarations(statement, hoisted);
        for (const declaration of hoisted.functions) {
            if (!statements.includes(declaration)) refuse("it declares a function in a block");
            if (declaration.async || declaration.generator) refuse("it declares an async function or a generator");
        }
        const plan: Plan = {
            names,
            simple: fn.params.every((param) => param.type === "Identifier"),
            vars: [...hoisted.vars],
            functions: hoisted.functions,
            lexical: lexicalOf(statements.filter((statement) => statement.type !== "FunctionDeclaration")),
        };
        this.#plans.set(fn, plan);
        return plan;
    }

    /** FunctionDeclarationInstantiation, then the body. */
    #invoke(closure: Closure, args: readonly JsValue[]): JsValue {
        if (this.#depth >= MAX_DEPTH) refuse(`it nests calls deeper than ${MAX_DEPTH}`);
        this.#depth++;
        try {
            const fn = closure.node;
            const plan = this.#planOf(fn);
            let scope = closure.env instanceof Env ? closure.env : null;
            if (fn.type === "FunctionExpression" && fn.id !== null) {
                scope = new Env(scope);
                scope.slots.set(fn.id.name, { value: closure, mutable: false });
            }
            const env = new Env(scope);
            for (const name of plan.names) env.slots.set(name, { value: plan.simple ? undefined : TDZ, mutable: true });
            for (const [i, param] of fn.params.entries()) {
                if (param.type === "RestElement") this.#bind(param.argument, new ArrayObject(args.slice(i)), env, "init");
                else this.#bind(param as Node, args[i], env, "init");
            }
            const body = fn.body;
            if (body === null) return refuse("it has no body");
            if (body.type !== "BlockStatement") return this.#eval(body, env);
            let varEnv = env;
            if (!plan.simple) varEnv = new Env(env);
            for (const name of plan.vars) {
                if (varEnv.slots.has(name)) continue;
                const param = varEnv === env ? undefined : env.slots.get(name);
                varEnv.slots.set(name, { value: param === undefined ? undefined : param.value, mutable: true });
            }
            const lexEnv = declare(varEnv, plan.lexical);
            for (const declaration of plan.functions) {
                if (declaration.id !== null) varEnv.slots.set(declaration.id.name, { value: new Closure(declaration, lexEnv), mutable: true });
            }
            const completion = this.#statements(body.body, lexEnv);
            return completion?.type === "return" ? completion.value : undefined;
        } finally {
            this.#depth--;
        }
    }

    // ------------------------------------------------------------ bindings

    #lookup(identifier: IdentifierReference, env: Env | null): JsValue {
        const name = identifier.name;
        for (let scope = env; scope !== null; scope = scope.parent) {
            const slot = scope.slots.get(name);
            if (slot === undefined) continue;
            if (slot.value === TDZ) return thrown(`ReferenceError: ${name} is read before its declaration`);
            return slot.value;
        }
        return this.#outerValue(identifier);
    }

    #assign(identifier: IdentifierReference, value: JsValue, env: Env | null): void {
        const name = identifier.name;
        for (let scope = env; scope !== null; scope = scope.parent) {
            const slot = scope.slots.get(name);
            if (slot === undefined) continue;
            if (slot.value === TDZ) return void thrown(`ReferenceError: ${name} is written before its declaration`);
            if (!slot.mutable) return void refuse(`it writes ${name}, a constant or a function's own name`);
            slot.value = value;
            return;
        }
        refuse(`it writes ${name}, which isn't its own`);
    }

    #initialize(name: string, value: JsValue, env: Env): void {
        for (let scope: Env | null = env; scope !== null; scope = scope.parent) {
            const slot = scope.slots.get(name);
            if (slot === undefined) continue;
            slot.value = value;
            return;
        }
        refuse(`it declares ${name} where the interpreter has no binding`);
    }

    #reference(target: Node, env: Env): Reference {
        const node = unparenthesized(target);
        if (node.type === "Identifier") return { identifier: node as IdentifierReference };
        if (node.type === "MemberExpression") {
            const object = this.#eval(node.object, env);
            return { object, key: this.#key(node, env) };
        }
        return refuse(`it assigns to a ${node.type}`);
    }

    #get(reference: Reference, env: Env): JsValue {
        return "identifier" in reference ? this.#lookup(reference.identifier, env) : getMember(reference.object, reference.key, this.#run);
    }

    #put(reference: Reference, value: JsValue, env: Env): void {
        if ("identifier" in reference) this.#assign(reference.identifier, value, env);
        else setMember(reference.object, reference.key, value, this.#run);
    }

    /** Binds `pattern` to `value`: `init` initializes declared bindings, `assign` puts (assignments, `var`). */
    #bind(pattern: Node, value: JsValue, env: Env, mode: "init" | "assign"): void {
        this.#step();
        switch (pattern.type) {
            case "Identifier":
                if (mode === "init") this.#initialize(pattern.name, value, env);
                else this.#assign(pattern as IdentifierReference, value, env);
                return;
            case "MemberExpression":
            case "ParenthesizedExpression":
                if (mode === "init") refuse("it declares a member");
                this.#put(this.#reference(pattern, env), value, env);
                return;
            case "AssignmentPattern":
                this.#bind(pattern.left, value === undefined ? this.#eval(pattern.right, env) : value, env, mode);
                return;
            case "ArrayPattern": {
                const iterator = iterate(value, this.#run);
                for (const element of pattern.elements) {
                    if (element === null) {
                        iterator.next();
                        continue;
                    }
                    if (element.type === "RestElement") {
                        const reference = this.#early(element.argument, env, mode);
                        const rest: JsValue[] = [];
                        for (let next = iterator.next(); next.done !== true; next = iterator.next()) rest.push(next.value);
                        this.#finish(element.argument, reference, new ArrayObject(rest), env, mode);
                        continue;
                    }
                    const [target, fallback] = element.type === "AssignmentPattern" ? [element.left as Node, element.right] : [element as Node, null];
                    const reference = this.#early(target, env, mode);
                    const next = iterator.next();
                    let item = next.done === true ? undefined : next.value;
                    if (item === undefined && fallback !== null) item = this.#eval(fallback, env);
                    this.#finish(target, reference, item, env, mode);
                }
                return;
            }
            case "ObjectPattern": {
                if (value === null || value === undefined) return void thrown(`TypeError: cannot destructure ${value}`);
                const used = new Set<string>();
                for (const property of pattern.properties) {
                    if (property.type === "RestElement") {
                        const reference = this.#early(property.argument, env, mode);
                        const rest = new PlainObject();
                        copyOwn(rest, value, used, this.#run);
                        this.#finish(property.argument, reference, rest, env, mode);
                        continue;
                    }
                    const key = property.computed ? toStr(this.#eval(property.key, env), this.#run) : staticKey(property.key);
                    used.add(key);
                    const [target, fallback] = property.value.type === "AssignmentPattern" ? [property.value.left as Node, property.value.right] : [property.value as Node, null];
                    const reference = this.#early(target, env, mode);
                    let item = getMember(value, key, this.#run);
                    if (item === undefined && fallback !== null) item = this.#eval(fallback, env);
                    this.#finish(target, reference, item, env, mode);
                }
                return;
            }
            default:
                refuse(`it binds a ${pattern.type}`);
        }
    }

    /** A destructuring assignment's simple target is evaluated before its value is read (spec order). */
    #early(target: Node, env: Env, mode: "init" | "assign"): Reference | undefined {
        if (mode === "init") return undefined;
        const node = unparenthesized(target);
        return node.type === "Identifier" || node.type === "MemberExpression" ? this.#reference(node, env) : undefined;
    }

    #finish(target: Node, reference: Reference | undefined, value: JsValue, env: Env, mode: "init" | "assign"): void {
        if (reference === undefined) this.#bind(target, value, env, mode);
        else this.#put(reference, value, env);
    }

    // ------------------------------------------------------------ statements

    #scoped(owner: Node, statements: readonly Node[], env: Env): Env {
        let lexical = this.#lexical.get(owner);
        if (lexical === undefined) {
            lexical = lexicalOf(statements);
            this.#lexical.set(owner, lexical);
        }
        return declare(env, lexical);
    }

    #statements(statements: readonly Node[], env: Env): Completion {
        for (const statement of statements) {
            const completion = this.#exec(statement, env, NO_LABELS);
            if (completion !== undefined) return completion;
        }
        return undefined;
    }

    #declare(declaration: VariableDeclaration, env: Env): void {
        for (const declarator of declaration.declarations) {
            if (declaration.kind === "var") {
                if (declarator.init !== null) this.#bind(declarator.id, this.#eval(declarator.init, env), env, "assign");
            } else {
                this.#bind(declarator.id, declarator.init === null ? undefined : this.#eval(declarator.init, env), env, "init");
            }
        }
    }

    #exec(node: Node, env: Env, labels: readonly string[]): Completion {
        this.#step();
        switch (node.type) {
            case "ExpressionStatement":
                this.#eval(node.expression, env);
                return undefined;
            case "VariableDeclaration":
                if (node.kind !== "var" && node.kind !== "let" && node.kind !== "const") return refuse(`it uses ${node.kind} declarations`);
                this.#declare(node, env);
                return undefined;
            case "ReturnStatement":
                return { type: "return", value: node.argument === null ? undefined : this.#eval(node.argument, env) };
            case "IfStatement":
                if (truthy(this.#eval(node.test, env))) return this.#exec(node.consequent, env, NO_LABELS);
                return node.alternate === null ? undefined : this.#exec(node.alternate, env, NO_LABELS);
            case "BlockStatement":
                return this.#statements(node.body, this.#scoped(node, node.body, env));
            case "EmptyStatement":
            // Instantiated with its function's body (`#planOf` refuses others).
            case "FunctionDeclaration":
                return undefined;
            case "BreakStatement":
                return node.label === null ? BREAK : { type: "break", label: node.label.name };
            case "ContinueStatement":
                return node.label === null ? CONTINUE : { type: "continue", label: node.label.name };
            case "LabeledStatement": {
                const body = node.body;
                const inner = isLoop(body) || body.type === "LabeledStatement" ? [...labels, node.label.name] : NO_LABELS;
                const completion = this.#exec(body, env, inner);
                return completion?.type === "break" && completion.label === node.label.name ? undefined : completion;
            }
            case "WhileStatement":
                while (truthy(this.#eval(node.test, env))) {
                    const completion = this.#exec(node.body, env, labels);
                    if (!continues(completion, labels)) return exitOf(completion);
                }
                return undefined;
            case "DoWhileStatement":
                do {
                    const completion = this.#exec(node.body, env, labels);
                    if (!continues(completion, labels)) return exitOf(completion);
                } while (truthy(this.#eval(node.test, env)));
                return undefined;
            case "ForStatement":
                return this.#for(node, env, labels);
            case "ForInStatement":
            case "ForOfStatement":
                return this.#forInOf(node, env, labels);
            case "SwitchStatement": {
                const discriminant = this.#eval(node.discriminant, env);
                const scoped = this.#scoped(
                    node,
                    node.cases.flatMap((c) => c.consequent),
                    env
                );
                let start = -1;
                for (const [i, c] of node.cases.entries()) {
                    if (c.test !== null && this.#eval(c.test, scoped) === discriminant) {
                        start = i;
                        break;
                    }
                }
                if (start === -1) start = node.cases.findIndex((c) => c.test === null);
                if (start === -1) return undefined;
                for (const c of node.cases.slice(start)) {
                    const completion = this.#statements(c.consequent, scoped);
                    if (completion !== undefined) return exitOf(completion);
                }
                return undefined;
            }
            case "ThrowStatement":
                return thrown(`it throws ${typeOf(this.#eval(node.argument, env))}`);
            default:
                return refuse(`it uses ${node.type}`);
        }
    }

    #for(node: Node & { type: "ForStatement" }, env: Env, labels: readonly string[]): Completion {
        let loopEnv = env;
        let perIteration: readonly string[] = [];
        const init = node.init;
        if (init?.type === "VariableDeclaration") {
            if (init.kind !== "var") {
                const lexical = lexicalOf([init]);
                loopEnv = declare(env, lexical);
                if (init.kind === "let") perIteration = lexical.map((l) => l.name);
            }
            this.#exec(init, loopEnv, NO_LABELS);
        } else if (init !== null) {
            this.#eval(init, env);
        }
        // CreatePerIterationEnvironment: closures of one iteration keep its copies of the `let` names.
        const copy = (last: Env): Env => {
            if (perIteration.length === 0) return last;
            const next = new Env(last.parent);
            for (const name of perIteration) {
                const slot = last.slots.get(name);
                if (slot !== undefined) next.slots.set(name, { value: slot.value, mutable: true });
            }
            return next;
        };
        let iterationEnv = copy(loopEnv);
        for (;;) {
            if (node.test !== null && !truthy(this.#eval(node.test, iterationEnv))) return undefined;
            const completion = this.#exec(node.body, iterationEnv, labels);
            if (!continues(completion, labels)) return exitOf(completion);
            iterationEnv = copy(iterationEnv);
            if (node.update !== null) this.#eval(node.update, iterationEnv);
        }
    }

    #forInOf(node: Node & { type: "ForInStatement" | "ForOfStatement" }, env: Env, labels: readonly string[]): Completion {
        if (node.type === "ForOfStatement" && node.await) return refuse("it uses for await");
        const left: Node = node.left;
        const declaration = left.type === "VariableDeclaration" ? left : undefined;
        const [declarator, ...others] = declaration?.declarations ?? [];
        if (declaration !== undefined && (declarator === undefined || others.length > 0 || declarator.init !== null)) refuse("its loop head declares something other than one binding");
        const lexical = declaration === undefined || declaration.kind === "var" ? [] : lexicalOf([declaration]);
        const subject = this.#eval(node.right, declare(env, lexical));
        const run = this.#run;
        const body = (value: JsValue): Completion => {
            let iterationEnv = env;
            if (declarator !== undefined) {
                const target = declarator.id;
                if (lexical.length === 0) this.#bind(target, value, env, "assign");
                else {
                    iterationEnv = declare(env, lexical);
                    this.#bind(target, value, iterationEnv, "init");
                }
            } else if (left.type === "ArrayPattern" || left.type === "ObjectPattern") {
                this.#bind(left, value, env, "assign");
            } else {
                this.#put(this.#reference(left, env), value, env);
            }
            return this.#exec(node.body, iterationEnv, labels);
        };
        if (node.type === "ForOfStatement") {
            for (const value of iterate(subject, run)) {
                const completion = body(value);
                if (!continues(completion, labels)) return exitOf(completion);
            }
            return undefined;
        }
        const keys = forInKeys(subject, run);
        const shape = shapeOf(subject);
        for (const key of keys) {
            run.step(1);
            const completion = body(key);
            if (!continues(completion, labels)) return exitOf(completion);
            // Whether keys added while enumerating are visited is engine-dependent (deleted ones would be skipped).
            if (shapeOf(subject) !== shape) return refuse("it changes which keys an object has while enumerating them");
        }
        return undefined;
    }

    // ------------------------------------------------------------ expressions

    #key(node: MemberExpression, env: Env): string {
        if (node.computed) return toStr(this.#eval(node.property, env), this.#run);
        if (node.property.type !== "Identifier") return refuse("it uses a private name");
        return node.property.name;
    }

    #arguments(list: readonly Node[], env: Env): JsValue[] {
        const args: JsValue[] = [];
        for (const arg of list) {
            if (arg.type === "SpreadElement") for (const item of iterate(this.#eval(arg.argument, env), this.#run)) args.push(item);
            else args.push(this.#eval(arg, env));
        }
        return args;
    }

    #looseEquals(left: JsValue, right: JsValue): boolean {
        if (isObject(left) && isObject(right)) return left === right;
        if (isObject(left) || isObject(right)) {
            const [object, other] = isObject(left) ? [left, right] : [right, left];
            if (other === null || other === undefined) return false;
            return this.#looseEquals(toPrimitive(object, this.#run), other);
        }
        const result = binary("==", left as Value, right as Value);
        return result.ok && result.value === true;
    }

    #binary(operator: string, left: JsValue, right: JsValue): JsValue {
        switch (operator) {
            case "===":
                return left === right;
            case "!==":
                return left !== right;
            case "==":
                return this.#looseEquals(left, right);
            case "!=":
                return !this.#looseEquals(left, right);
            case "in":
                if (!isObject(right)) return thrown("TypeError: in on a primitive");
                return hasProperty(right, toStr(left, this.#run), this.#run);
            case "**":
                return refuse("it uses **, whose result is implementation-approximated");
            default:
                break;
        }
        const result = binary(operator, toPrimitive(left, this.#run), toPrimitive(right, this.#run));
        if (!result.ok) return refuse(`it uses ${operator}`);
        if (typeof result.value === "string" && result.value.length > MAX_STRING) refuse(`it makes a string longer than ${MAX_STRING} characters`);
        return result.value;
    }

    #call(node: Node & { type: "CallExpression" }, env: Env): JsValue {
        const callee = unparenthesized(node.callee);
        let fn: JsValue;
        let self: JsValue;
        if (callee.type === "MemberExpression") {
            self = this.#eval(callee.object, env);
            if (callee.optional && (self === null || self === undefined)) throw SHORT_CIRCUIT;
            fn = getMember(self, this.#key(callee, env), this.#run);
        } else {
            fn = this.#eval(callee, env);
        }
        if (node.optional && (fn === null || fn === undefined)) throw SHORT_CIRCUIT;
        return this.#callValue(fn, self, this.#arguments(node.arguments, env));
    }

    #eval(node: Node, env: Env): JsValue {
        this.#step();
        switch (node.type) {
            case "Literal":
                if ("regex" in node) return refuse("it makes a regular expression");
                if (typeof node.value === "bigint") return refuse("it uses a bigint");
                return node.value as Value;
            case "Identifier":
                return this.#lookup(node as IdentifierReference, env);
            case "ParenthesizedExpression":
                return this.#eval(node.expression, env);
            case "TemplateLiteral": {
                let text = "";
                for (const [i, quasi] of node.quasis.entries()) {
                    if (quasi.value.cooked === null) return refuse("its template has an invalid escape");
                    text += quasi.value.cooked;
                    const expression = node.expressions[i];
                    if (expression !== undefined) text += toStr(this.#eval(expression, env), this.#run);
                    if (text.length > MAX_STRING) refuse(`it makes a string longer than ${MAX_STRING} characters`);
                }
                return text;
            }
            case "ArrayExpression": {
                const items: JsValue[] = [];
                for (const element of node.elements) {
                    if (element === null) items.length++;
                    else if (element.type === "SpreadElement") for (const item of iterate(this.#eval(element.argument, env), this.#run)) items.push(item);
                    else items.push(this.#eval(element, env));
                }
                return new ArrayObject(items);
            }
            case "ObjectExpression": {
                const object = new PlainObject();
                for (const property of node.properties) {
                    if (property.type === "SpreadElement") {
                        copyOwn(object, this.#eval(property.argument, env), new Set(), this.#run);
                        continue;
                    }
                    if (property.kind !== "init") return refuse("it defines a getter or setter");
                    const key = property.computed ? toStr(this.#eval(property.key, env), this.#run) : staticKey(property.key);
                    if (key === "__proto__" && !property.computed && !property.shorthand && !property.method) return refuse("it sets a prototype in an object literal");
                    object.props.set(key, this.#eval(property.value, env));
                }
                return object;
            }
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                if (node.async || node.generator) return refuse("it makes an async function or a generator");
                return new Closure(node, env);
            case "UnaryExpression": {
                const argument = unparenthesized(node.argument);
                if (node.operator === "delete") {
                    if (argument.type !== "MemberExpression") return refuse("it deletes something other than a member");
                    const object = this.#eval(argument.object, env);
                    const key = this.#key(argument, env);
                    if (object === null || object === undefined) return thrown(`TypeError: cannot delete ${key} of ${object}`);
                    return deleteMember(object, key);
                }
                const operand = this.#eval(argument, env);
                if (node.operator === "typeof") return typeOf(operand);
                if (node.operator === "!") return !truthy(operand);
                if (node.operator === "void") return undefined;
                const result = unary(node.operator, toPrimitive(operand, this.#run));
                return result.ok ? result.value : refuse(`it uses ${node.operator}`);
            }
            case "UpdateExpression": {
                const reference = this.#reference(node.argument, env);
                const old = toNum(this.#get(reference, env), this.#run);
                const next = node.operator === "++" ? old + 1 : old - 1;
                this.#put(reference, next, env);
                return node.prefix ? next : old;
            }
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier") return refuse("it uses a private name");
                const left = this.#eval(node.left, env);
                return this.#binary(node.operator, left, this.#eval(node.right, env));
            }
            case "LogicalExpression": {
                const left = this.#eval(node.left, env);
                const done = node.operator === "&&" ? !truthy(left) : node.operator === "||" ? truthy(left) : left !== null && left !== undefined;
                return done ? left : this.#eval(node.right, env);
            }
            case "ConditionalExpression":
                return this.#eval(truthy(this.#eval(node.test, env)) ? node.consequent : node.alternate, env);
            case "SequenceExpression": {
                let last: JsValue;
                for (const expression of node.expressions) last = this.#eval(expression, env);
                return last;
            }
            case "AssignmentExpression":
                return this.#assignment(node, env);
            case "MemberExpression": {
                const object = this.#eval(node.object, env);
                if (node.optional && (object === null || object === undefined)) throw SHORT_CIRCUIT;
                return getMember(object, this.#key(node, env), this.#run);
            }
            case "ChainExpression":
                try {
                    return this.#eval(node.expression, env);
                } catch (error) {
                    if (error === SHORT_CIRCUIT) return undefined;
                    throw error;
                }
            case "CallExpression":
                return this.#call(node, env);
            case "NewExpression": {
                const callee = this.#eval(node.callee, env);
                const args = this.#arguments(node.arguments, env);
                if (callee instanceof Native && callee.construct !== undefined) return callee.construct(args, this.#run);
                return refuse("it constructs something other than an array");
            }
            default:
                return refuse(`it uses ${node.type}`);
        }
    }

    #assignment(node: Node & { type: "AssignmentExpression" }, env: Env): JsValue {
        const { operator, left } = node;
        if (operator === "=") {
            if (left.type === "ArrayPattern" || left.type === "ObjectPattern") {
                const value = this.#eval(node.right, env);
                this.#bind(left, value, env, "assign");
                return value;
            }
            const reference = this.#reference(left, env);
            const value = this.#eval(node.right, env);
            this.#put(reference, value, env);
            return value;
        }
        const reference = this.#reference(left, env);
        const current = this.#get(reference, env);
        if (operator === "&&=" || operator === "||=" || operator === "??=") {
            const done = operator === "&&=" ? !truthy(current) : operator === "||=" ? truthy(current) : current !== null && current !== undefined;
            if (done) return current;
            const value = this.#eval(node.right, env);
            this.#put(reference, value, env);
            return value;
        }
        const value = this.#binary(operator.slice(0, -1), current, this.#eval(node.right, env));
        this.#put(reference, value, env);
        return value;
    }
}
