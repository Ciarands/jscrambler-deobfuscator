import type { Function as FunctionNode, FunctionLike, IdentifierReference, MemberExpression, Node, VariableDeclaration } from "./ast.js";
import type { JsValue, Run } from "./builtins.js";
import {
    ArgumentsObject,
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
import { forEachChild } from "./traverse.js";

/** What a name the interpreted code doesn't declare stands for. */
export type OuterBinding = { readonly value: JsValue } | { readonly function: FunctionLike } | { readonly global: string };

export type Answer =
    | { readonly ok: true; readonly value: Value; readonly steps: number }
    /** `exhausted`: the step budget ran out (another budget might answer). */
    | { readonly ok: false; readonly reason: string; readonly steps: number; readonly exhausted: boolean };

/** A session's answer: objects included (the session keeps them, and the closures' state, for later calls). */
export type Held = { readonly ok: true; readonly value: JsValue; readonly steps: number } | { readonly ok: false; readonly reason: string; readonly steps: number; readonly exhausted: boolean };

export interface InterpreterOptions {
    /** A name the code doesn't declare: what it is, or why it can't be used. Asked once per identifier node. */
    readonly outer: (identifier: IdentifierReference) => OuterBinding | string;
    /** Builtin aliases the program added (model 7): by owner (`String.prototype`), the alias's original name. */
    readonly aliases?: ReadonlyMap<string, ReadonlyMap<string, string>>;
    /**
     * A function expression the caller proved equal to a value (a name probe whose only possible result it knows):
     * evaluating the expression gives that value instead of a closure. Asked each time one is evaluated.
     */
    readonly substitute?: (fn: FunctionLike) => { readonly value: JsValue } | undefined;
}

/** Nested interpreted calls; deeper ones refuse (host stack). */
const MAX_DEPTH = 200;

const TDZ: unique symbol = Symbol("uninitialized");

type Slot = JsValue | typeof TDZ;

/**
 * The names one kind of environment binds (a function's, a block's, a loop head's), known before its code runs: each
 * name the code reads resolves to a slot of an environment some fixed number of parents up, or to an outer binding.
 */
class Scope {
    readonly names: string[] = [];
    readonly mutable: boolean[] = [];
    readonly #index = new Map<string, number>();
    /** The code of functions whose closures are made in this scope's environments. */
    readonly functions = new Map<FunctionLike, FunctionCode>();

    /** `ownThis`: a non-arrow function's scope, whose environments hold the call's `this`. */
    constructor(
        readonly parent: Scope | null,
        readonly ownThis = false
    ) {}

    /** Binds `name` (again: the later binding's mutability holds). */
    declare(name: string, mutable: boolean): number {
        const known = this.#index.get(name);
        if (known !== undefined) {
            this.mutable[known] = mutable;
            return known;
        }
        this.#index.set(name, this.names.length);
        this.names.push(name);
        this.mutable.push(mutable);
        return this.names.length - 1;
    }

    indexOf(name: string): number | undefined {
        return this.#index.get(name);
    }
}

class Env {
    /** A non-arrow function's `this` (its scope's `ownThis`). */
    self: JsValue = undefined;
    constructor(
        readonly scope: Scope,
        readonly parent: Env | null,
        readonly values: Slot[]
    ) {}
}

const envAt = (env: Env, hops: number): Env => {
    let at = env;
    for (let i = 0; i < hops; i++) at = at.parent as Env;
    return at;
};

interface Binding {
    readonly hops: number;
    readonly index: number;
    readonly mutable: boolean;
}

/** Where `name` is bound from `scope`: environments up and slot; `undefined` when the code doesn't declare it. */
const resolve = (scope: Scope | null, name: string): Binding | undefined => {
    let hops = 0;
    for (let at = scope; at !== null; at = at.parent, hops++) {
        const index = at.indexOf(name);
        if (index !== undefined) return { hops, index, mutable: at.mutable[index] === true };
    }
    return undefined;
};

interface Jump {
    readonly type: "break" | "continue";
    readonly label: string | undefined;
}

interface Return {
    readonly type: "return";
}

/** A `return` unwinding to its call; the value is the interpreter's `#returned` (nothing runs while it unwinds). */
type Completion = Jump | Return | undefined;

const BREAK: Jump = { type: "break", label: undefined };
const CONTINUE: Jump = { type: "continue", label: undefined };
const RETURN: Return = { type: "return" };
const NO_LABELS: readonly string[] = [];

/** Unwinds an optional chain that met `null`/`undefined` to its `ChainExpression`. */
const SHORT_CIRCUIT = { shortCircuit: true };

/** Compiled code: an expression's value, a statement's completion, a pattern binding a value. */
type Code = (env: Env) => JsValue;
type Exec = (env: Env) => Completion;
type Binder = (env: Env, value: JsValue) => void;
type Writer = (env: Env, value: JsValue) => void;
type KeyCode = (env: Env) => string;
type Operator = (left: JsValue, right: JsValue) => JsValue;

/** Where an assignment or a pattern writes: a binding, or a member whose object and key are evaluated first. */
type Target =
    | { readonly kind: "binding"; readonly lookup: Code; readonly assign: Writer }
    | { readonly kind: "member"; readonly object: Code; readonly key: KeyCode }
    | { readonly kind: "invalid"; readonly reason: string };

/** A target evaluated: its environment, or its object and key. */
interface Reference {
    readonly target: Target;
    readonly env: Env;
    readonly object: JsValue;
    readonly key: string;
}

/** A pattern element: written through a reference evaluated before its value is read (`early`), else bound. */
interface ElementCode {
    readonly early: Target | null;
    readonly bind: Binder;
    readonly fallback: Code | null;
}

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
    /** Whether calls bind `arguments` (a non-arrow function naming it), or why that refuses. */
    readonly arguments: boolean | string;
}

/** A function compiled for closures made in one scope. */
interface FunctionCode {
    /** A named function expression's scope of its own name. */
    readonly named: Scope | null;
    readonly scope: Scope;
    /** The function environment's slots before the parameters are bound. */
    readonly initial: readonly Slot[];
    readonly argumentsIndex: number;
    readonly params: (env: Env, args: readonly JsValue[]) => void;
    readonly body: Code;
}

/** Calls `visit` on the nodes of `fn` outside nested non-arrow functions (which have their own `arguments` and `this`). */
const ownNodes = (fn: Node, visit: (node: Node, parent: Node) => void): void => {
    const walk = (node: Node): void =>
        forEachChild(node, (child) => {
            if (child.type === "FunctionExpression" || child.type === "FunctionDeclaration") return;
            visit(child, node);
            walk(child);
        });
    walk(fn);
};

/** Whether `node` reads the binding `arguments` (not a property or key of that name). */
const namesArguments = (node: Node, parent: Node): boolean => {
    if (node.type !== "Identifier" || node.name !== "arguments") return false;
    if (parent.type === "MemberExpression" && parent.property === node && !parent.computed) return false;
    return !((parent.type === "Property" || parent.type === "MethodDefinition") && parent.key === node && !parent.computed && !(parent.type === "Property" && parent.shorthand));
};

/**
 * Whether anything in `fn`, nested functions included, may write one of `names`: assignments, updates, loop heads, and
 * declarators with an initializer (a `var` of a parameter's name writes the parameter).
 */
const writesAnyOf = (fn: Node, names: ReadonlySet<string>): boolean => {
    let found = false;
    const written = (target: Node): boolean => {
        if (target.type === "VariableDeclaration") return target.declarations.some((declarator) => written(declarator.id));
        return [...bindingNames(target)].some((name) => names.has(name));
    };
    const walk = (node: Node): void =>
        forEachChild(node, (child) => {
            if (found) return;
            const target =
                child.type === "AssignmentExpression"
                    ? child.left
                    : child.type === "UpdateExpression"
                      ? child.argument
                      : child.type === "ForInStatement" || child.type === "ForOfStatement"
                        ? child.left
                        : child.type === "VariableDeclarator" && child.init !== null
                          ? child.id
                          : undefined;
            if (target !== undefined && written(target as Node)) found = true;
            walk(child);
        });
    walk(fn);
    return found;
};

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

/**
 * The scope of an environment binding `statements`' `let`/`const` names, all uninitialized: `null` when they declare
 * none (no environment is made); what `lexicalOf` refuses with, thrown when the code runs.
 */
const lexicalScope = (parent: Scope, statements: readonly Node[]): { readonly scope: Scope; readonly initial: readonly Slot[] } | null | { readonly error: unknown } => {
    let lexical: Lexical[];
    try {
        lexical = lexicalOf(statements);
    } catch (error) {
        return { error };
    }
    if (lexical.length === 0) return null;
    const scope = new Scope(parent);
    for (const { name, constant } of lexical) scope.declare(name, !constant);
    return { scope, initial: scope.names.map(() => TDZ) };
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

/** A number that is an array index: reads and writes by it are those by its string (`ToString` of it can't run code). */
const isIndex = (key: number): boolean => key >= 0 && key < 4294967295 && Number.isInteger(key);

const readTdz = (name: string): never => thrown(`ReferenceError: ${name} is read before its declaration`);
const writeTdz = (name: string): never => thrown(`ReferenceError: ${name} is written before its declaration`);
const tooLong = (): never => refuse(`it makes a string longer than ${MAX_STRING} characters`);

/** Host operators on primitives, which `evaluate.ts`'s `binary` gives too. */
const PRIMITIVE_OPERATORS: Readonly<Record<string, (left: never, right: never) => Value>> = {
    "-": (l: number, r: number) => l - r,
    "*": (l: number, r: number) => l * r,
    "/": (l: number, r: number) => l / r,
    "%": (l: number, r: number) => l % r,
    "<": (l: number, r: number) => l < r,
    "<=": (l: number, r: number) => l <= r,
    ">": (l: number, r: number) => l > r,
    ">=": (l: number, r: number) => l >= r,
    "<<": (l: number, r: number) => l << r,
    ">>": (l: number, r: number) => l >> r,
    ">>>": (l: number, r: number) => l >>> r,
    "&": (l: number, r: number) => l & r,
    "|": (l: number, r: number) => l | r,
    "^": (l: number, r: number) => l ^ r,
};

/** Tells primitive argument lists apart exactly (`-0`, `NaN`, `"1"` and `1`), for caching answers. */
export const argumentsKey = (args: readonly Value[]): string =>
    args.map((arg) => (typeof arg === "string" ? JSON.stringify(arg) : Object.is(arg, -0) ? "-0" : `${typeof arg}:${String(arg)}`)).join(",");

/** What `name` is bound to where `closure` was made, if its environment binds it: values the closure's code may reach. */
export const closureBinding = (closure: Closure, name: string): { readonly value: JsValue } | undefined => {
    for (let env = closure.env instanceof Env ? closure.env : null; env !== null; env = env.parent) {
        const index = env.scope.indexOf(name);
        if (index === undefined) continue;
        const value = env.values[index];
        return { value: value === TDZ ? undefined : value };
    }
    return undefined;
};

/**
 * Runs calls of functions over the AST on the host, without executing program code: environments, statements and
 * expressions are the interpreter's, operators on primitives are `evaluate.ts`'s, builtins `builtins.ts`'s. Covers
 * what the purity provers admit, plus `this` (of method calls, `call`/`apply`/`bind` and callbacks given one) and
 * `arguments` (while nothing writes a parameter it would alias); no `try`, classes, generators, `async`, `with` or
 * getters: whatever else it meets refuses. A throw is no answer (no `try` could catch it), so only paths that return
 * need the program's order of effects. Steps (evaluated nodes and builtin work) are counted against a budget, so an
 * answer doesn't depend on the host's speed. `call` answers only primitives; a session (`evaluate`, `callHeld`,
 * `member`) keeps objects and closures, with their state, between its calls.
 *
 * Code is compiled to closures the first time it runs (a function's when it is first called, a statement list's
 * statements when each first runs), with every name resolved to its slot; what the code refuses, it refuses when it
 * runs, after the same steps as evaluating the AST node by node. A session's code is the AST as it first ran.
 */
export class Interpreter {
    readonly #outer: InterpreterOptions["outer"];
    readonly #aliases: ReadonlyMap<string, ReadonlyMap<string, string>>;
    readonly #outerValues = new Map<Node, JsValue>();
    readonly #closures = new Map<FunctionLike, Closure>();
    readonly #plans = new WeakMap<Node, Plan>();
    /** The scope `evaluate` runs expressions in: it declares nothing. */
    readonly #root = new Scope(null);
    readonly #evaluated = new Map<Node, Code>();
    /** The code of closures made outside any environment (outer functions). */
    readonly #rootFunctions = new Map<FunctionLike, FunctionCode>();
    #steps = 0;
    #limit = 0;
    #depth = 0;
    #returned: JsValue = undefined;
    readonly #run: Run;
    readonly #substitute: InterpreterOptions["substitute"];

    constructor(options: InterpreterOptions) {
        this.#outer = options.outer;
        this.#aliases = options.aliases ?? new Map();
        this.#substitute = options.substitute;
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
        const held = this.#held(() => this.#invoke(this.#closureOf(fn), args, undefined), maxSteps);
        if (held.ok && isObject(held.value)) return { ok: false, reason: `it returns ${isCallable(held.value) ? "a function" : "an object"}`, steps: held.steps, exhausted: false };
        return held as Answer;
    }

    /** Evaluates an expression over the outer bindings only, within `maxSteps` steps; an object it gives is kept. */
    evaluate(node: Node, maxSteps: number): Held {
        return this.#held(() => {
            let code = this.#evaluated.get(node);
            if (code === undefined) {
                code = this.#expression(node, this.#root);
                this.#evaluated.set(node, code);
            }
            return code(new Env(this.#root, null, []));
        }, maxSteps);
    }

    /** Calls a value an earlier `evaluate`/`callHeld`/`member` gave (its closures keep their state). */
    callHeld(callee: JsValue, self: JsValue, args: readonly JsValue[], maxSteps: number): Held {
        return this.#held(() => this.#callValue(callee, self, args), maxSteps);
    }

    /** Reads a member of a value an earlier answer gave, as the program would. */
    member(object: JsValue, key: string, maxSteps: number): Held {
        return this.#held(() => getMember(object, key, this.#run), maxSteps);
    }

    #held(work: () => JsValue, maxSteps: number): Held {
        this.#steps = 0;
        this.#limit = maxSteps;
        this.#depth = 0;
        try {
            return { ok: true, value: work(), steps: this.#steps };
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

    /** Code that takes its step, then refuses (or throws `error`): what the AST walk did on meeting the node. */
    #failing(error: unknown): (env: Env) => never {
        return () => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            throw error;
        };
    }

    #refusing(reason: string): (env: Env) => never {
        return () => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            return refuse(reason);
        };
    }

    // ------------------------------------------------------------ calls

    #callValue(callee: JsValue, self: JsValue, args: readonly JsValue[]): JsValue {
        if (++this.#steps > this.#limit) throw EXHAUSTED;
        if (callee instanceof Closure) return this.#invoke(callee, args, self);
        if (callee instanceof Native && callee.call !== undefined) return callee.call(self, args, this.#run);
        // Argument lists are always fresh arrays nothing else holds: a bound function without arguments passes its own on.
        if (callee instanceof Bound) return this.#callValue(callee.target, callee.self, callee.args.length === 0 ? args : [...callee.args, ...args]);
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
        const simple = fn.params.every((param) => param.type === "Identifier");
        const lexical = lexicalOf(statements.filter((statement) => statement.type !== "FunctionDeclaration"));
        let usesArguments = false;
        if (fn.type !== "ArrowFunctionExpression" && body !== null) ownNodes(body as Node, (node, parent) => (usesArguments ||= namesArguments(node, parent)));
        const declaresArguments =
            names.includes("arguments") || hoisted.vars.has("arguments") || hoisted.functions.some((f) => f.id?.name === "arguments") || lexical.some((l) => l.name === "arguments");
        const plan: Plan = {
            names,
            simple,
            vars: [...hoisted.vars],
            functions: hoisted.functions,
            lexical,
            // Sloppy-mode `arguments` of simple parameters aliases them: exact while no parameter is ever written (its
            // elements aren't either: `ArgumentsObject` refuses).
            arguments: !usesArguments
                ? false
                : declaresArguments
                  ? "it declares a binding named arguments"
                  : simple && writesAnyOf(fn, new Set(names))
                    ? "it writes a parameter its arguments object may alias"
                    : true,
        };
        this.#plans.set(fn, plan);
        return plan;
    }

    /** FunctionDeclarationInstantiation, then the body. `self`: the call's `this`. */
    #invoke(closure: Closure, args: readonly JsValue[], self: JsValue): JsValue {
        if (this.#depth >= MAX_DEPTH) refuse(`it nests calls deeper than ${MAX_DEPTH}`);
        this.#depth++;
        try {
            const fn = closure.node;
            const plan = this.#planOf(fn);
            const outer = closure.env instanceof Env ? closure.env : null;
            const code = this.#functionCode(fn, plan, outer === null ? null : outer.scope);
            const scope = code.named === null ? outer : new Env(code.named, outer, [closure]);
            const env = new Env(code.scope, scope, code.initial.slice());
            if (code.scope.ownThis) {
                // A primitive or missing `this` is the global object or a wrapper in sloppy mode, itself in strict mode.
                env.self = self;
                if (plan.arguments === true) env.values[code.argumentsIndex] = new ArgumentsObject([...args]);
                else if (typeof plan.arguments === "string") refuse(plan.arguments);
            }
            code.params(env, args);
            return code.body(env);
        } finally {
            this.#depth--;
        }
    }

    #functionCode(fn: FunctionLike, plan: Plan, parent: Scope | null): FunctionCode {
        const compiled = parent === null ? this.#rootFunctions : parent.functions;
        let code = compiled.get(fn);
        if (code === undefined) {
            code = this.#function(fn, plan, parent);
            compiled.set(fn, code);
        }
        return code;
    }

    #function(fn: FunctionLike, plan: Plan, parent: Scope | null): FunctionCode {
        let named: Scope | null = null;
        if (fn.type === "FunctionExpression" && fn.id !== null) {
            named = new Scope(parent);
            named.declare(fn.id.name, false);
        }
        const scope = new Scope(named ?? parent, fn.type !== "ArrowFunctionExpression");
        const argumentsIndex = scope.ownThis && plan.arguments === true ? scope.declare("arguments", true) : -1;
        for (const name of plan.names) scope.declare(name, true);

        const body = fn.body;
        let run: Code;
        if (body === null) {
            run = () => refuse("it has no body");
        } else if (body.type !== "BlockStatement") {
            run = this.#expression(body, scope);
        } else {
            // Parameter expressions get their own environment: `var`s start as the parameters of their names.
            const varScope = plan.simple ? scope : new Scope(scope);
            const copies: (readonly [number, number])[] = [];
            for (const name of plan.vars) {
                if (varScope.indexOf(name) !== undefined) continue;
                const index = varScope.declare(name, true);
                const param = varScope === scope ? undefined : scope.indexOf(name);
                if (param !== undefined) copies.push([index, param]);
            }
            const functions: (readonly [number, FunctionNode])[] = [];
            for (const declaration of plan.functions) if (declaration.id !== null) functions.push([varScope.declare(declaration.id.name, true), declaration]);
            let lexScope = varScope;
            let lexInitial: readonly Slot[] | null = null;
            if (plan.lexical.length > 0) {
                lexScope = new Scope(varScope);
                for (const { name, constant } of plan.lexical) lexScope.declare(name, !constant);
                lexInitial = lexScope.names.map(() => TDZ);
            }
            const statements = this.#statements(body.body, lexScope);
            const separate = varScope !== scope;
            const varInitial: readonly Slot[] = varScope.names.map(() => undefined);
            run = (env) => {
                let varEnv = env;
                if (separate) {
                    const values = varInitial.slice();
                    for (const [index, param] of copies) values[index] = env.values[param];
                    varEnv = new Env(varScope, env, values);
                }
                const lexEnv = lexInitial === null ? varEnv : new Env(lexScope, varEnv, lexInitial.slice());
                for (const [index, declaration] of functions) varEnv.values[index] = new Closure(declaration, lexEnv);
                return statements(lexEnv) === RETURN ? this.#returned : undefined;
            };
        }

        const initial = scope.names.map((_, index) => (!plan.simple && index !== argumentsIndex ? TDZ : undefined));
        const binders = fn.params.map((param) =>
            param.type === "RestElement" ? { rest: true, bind: this.#binder(param.argument, scope, "init") } : { rest: false, bind: this.#binder(param as Node, scope, "init") }
        );
        const params = (env: Env, args: readonly JsValue[]): void => {
            for (let i = 0; i < binders.length; i++) {
                const { rest, bind } = binders[i] as (typeof binders)[number];
                bind(env, rest ? new ArrayObject(args.slice(i)) : args[i]);
            }
        };
        return { named, scope, initial, argumentsIndex, params, body: run };
    }

    // ------------------------------------------------------------ bindings

    /** Reads a binding (no step): `undefined` names are outer ones. */
    #lookup(identifier: IdentifierReference, scope: Scope): Code {
        const name = identifier.name;
        const binding = resolve(scope, name);
        if (binding === undefined) return () => this.#outerValue(identifier);
        const { hops, index } = binding;
        return (env) => {
            const value = envAt(env, hops).values[index];
            return value === TDZ ? readTdz(name) : value;
        };
    }

    /** PutValue on a binding: the code's own, initialized and mutable. */
    #assigner(identifier: IdentifierReference, scope: Scope): Writer {
        const name = identifier.name;
        const binding = resolve(scope, name);
        if (binding === undefined) return () => refuse(`it writes ${name}, which isn't its own`);
        const { hops, index, mutable } = binding;
        return (env, value) => {
            const values = envAt(env, hops).values;
            if (values[index] === TDZ) writeTdz(name);
            if (!mutable) refuse(`it writes ${name}, a constant or a function's own name`);
            values[index] = value;
        };
    }

    /** Initializes a declared binding. */
    #initializer(name: string, scope: Scope): Writer {
        const binding = resolve(scope, name);
        if (binding === undefined) return () => refuse(`it declares ${name} where the interpreter has no binding`);
        const { hops, index } = binding;
        return (env, value) => {
            envAt(env, hops).values[index] = value;
        };
    }

    #target(node: Node, scope: Scope): Target {
        const target = unparenthesized(node);
        if (target.type === "Identifier") return { kind: "binding", lookup: this.#lookup(target as IdentifierReference, scope), assign: this.#assigner(target as IdentifierReference, scope) };
        if (target.type === "MemberExpression") return { kind: "member", object: this.#expression(target.object, scope), key: this.#key(target, scope) };
        return { kind: "invalid", reason: `it assigns to a ${target.type}` };
    }

    #reference(target: Target, env: Env): Reference {
        if (target.kind === "invalid") return refuse(target.reason);
        if (target.kind === "binding") return { target, env, object: undefined, key: "" };
        const object = target.object(env);
        return { target, env, object, key: target.key(env) };
    }

    #put(reference: Reference, value: JsValue): void {
        const { target } = reference;
        if (target.kind === "binding") target.assign(reference.env, value);
        else setMember(reference.object, reference.key, value, this.#run);
    }

    /** Binds `pattern` to a value: `init` initializes declared bindings, `assign` puts (assignments, `var`). */
    #binder(pattern: Node, scope: Scope, mode: "init" | "assign"): Binder {
        switch (pattern.type) {
            case "Identifier": {
                const write = mode === "init" ? this.#initializer(pattern.name, scope) : this.#assigner(pattern as IdentifierReference, scope);
                return (env, value) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    write(env, value);
                };
            }
            case "MemberExpression":
            case "ParenthesizedExpression": {
                if (mode === "init") return this.#refusing("it declares a member");
                const target = this.#target(pattern, scope);
                return (env, value) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    this.#put(this.#reference(target, env), value);
                };
            }
            case "AssignmentPattern": {
                const fallback = this.#expression(pattern.right, scope);
                const bind = this.#binder(pattern.left, scope, mode);
                return (env, value) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    bind(env, value === undefined ? fallback(env) : value);
                };
            }
            case "ArrayPattern": {
                const elements = pattern.elements.map((element) =>
                    element === null ? null : element.type === "RestElement" ? { rest: true, code: this.#element(element.argument, null, scope, mode) } : { rest: false, code: this.#element(element, undefined, scope, mode) }
                );
                const run = this.#run;
                return (env, value) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const iterator = iterate(value, run);
                    for (const element of elements) {
                        if (element === null) {
                            iterator.next();
                            continue;
                        }
                        if (element.rest) {
                            this.#bindElement(element.code, env, () => {
                                const rest: JsValue[] = [];
                                for (let next = iterator.next(); next.done !== true; next = iterator.next()) rest.push(next.value);
                                return new ArrayObject(rest);
                            });
                            continue;
                        }
                        this.#bindElement(element.code, env, () => {
                            const next = iterator.next();
                            return next.done === true ? undefined : next.value;
                        });
                    }
                };
            }
            case "ObjectPattern": {
                const properties = pattern.properties.map((property) => {
                    if (property.type === "RestElement") return { rest: true as const, code: this.#element(property.argument, null, scope, mode) };
                    let key: KeyCode | string | { readonly error: unknown };
                    if (property.computed) {
                        const computed = this.#expression(property.key, scope);
                        key = (env: Env) => toStr(computed(env), this.#run);
                    } else {
                        try {
                            key = staticKey(property.key);
                        } catch (error) {
                            key = { error };
                        }
                    }
                    return { rest: false as const, key, code: this.#element(property.value, undefined, scope, mode) };
                });
                const run = this.#run;
                return (env, value) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    if (value === null || value === undefined) return void thrown(`TypeError: cannot destructure ${value}`);
                    const used = new Set<string>();
                    for (const property of properties) {
                        if (property.rest) {
                            this.#bindElement(property.code, env, () => {
                                const rest = new PlainObject();
                                copyOwn(rest, value, used, run);
                                return rest;
                            });
                            continue;
                        }
                        const { key: code } = property;
                        let key: string;
                        if (typeof code === "string") key = code;
                        else if (typeof code === "function") key = code(env);
                        else throw code.error;
                        used.add(key);
                        this.#bindElement(property.code, env, () => getMember(value, key, run));
                    }
                };
            }
            default:
                return this.#refusing(`it binds a ${pattern.type}`);
        }
    }

    /**
     * A pattern element, `target = fallback` or `target` (`fallback` `undefined`: split `element`; `null`: a rest
     * element's argument, taken whole).
     */
    #element(element: Node, fallback: null | undefined, scope: Scope, mode: "init" | "assign"): ElementCode {
        const [target, otherwise] = fallback === undefined && element.type === "AssignmentPattern" ? [element.left as Node, this.#expression(element.right, scope)] : [element, null];
        const node = unparenthesized(target);
        // A destructuring assignment's simple target is evaluated before its value is read (spec order).
        const early = mode === "assign" && (node.type === "Identifier" || node.type === "MemberExpression") ? this.#target(node, scope) : null;
        return { early, bind: this.#binder(target, scope, mode), fallback: otherwise };
    }

    #bindElement(code: ElementCode, env: Env, read: () => JsValue): void {
        const reference = code.early === null ? undefined : this.#reference(code.early, env);
        let item = read();
        if (item === undefined && code.fallback !== null) item = code.fallback(env);
        if (reference === undefined) code.bind(env, item);
        else this.#put(reference, item);
    }

    // ------------------------------------------------------------ statements

    /** A statement list; each statement is compiled when it first runs. */
    #statements(statements: readonly Node[], scope: Scope): Exec {
        const count = statements.length;
        const code: Exec[] = statements.map((statement, i) => (env: Env) => {
            const compiled = this.#statement(statement, scope, NO_LABELS);
            code[i] = compiled;
            return compiled(env);
        });
        return (env) => {
            for (let i = 0; i < count; i++) {
                const completion = (code[i] as Exec)(env);
                if (completion !== undefined) return completion;
            }
            return undefined;
        };
    }

    #declaration(declaration: VariableDeclaration, scope: Scope): (env: Env) => void {
        const declarators: ((env: Env) => void)[] = [];
        for (const declarator of declaration.declarations) {
            if (declaration.kind === "var") {
                if (declarator.init === null) continue;
                const init = this.#expression(declarator.init, scope);
                const bind = this.#binder(declarator.id, scope, "assign");
                declarators.push((env) => bind(env, init(env)));
            } else {
                const init = declarator.init === null ? null : this.#expression(declarator.init, scope);
                const bind = this.#binder(declarator.id, scope, "init");
                declarators.push((env) => bind(env, init === null ? undefined : init(env)));
            }
        }
        return (env) => {
            for (const declare of declarators) declare(env);
        };
    }

    #statement(node: Node, scope: Scope, labels: readonly string[]): Exec {
        switch (node.type) {
            case "ExpressionStatement": {
                const expression = this.#expression(node.expression, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    expression(env);
                    return undefined;
                };
            }
            case "VariableDeclaration": {
                if (node.kind !== "var" && node.kind !== "let" && node.kind !== "const") return this.#refusing(`it uses ${node.kind} declarations`);
                const declare = this.#declaration(node, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    declare(env);
                    return undefined;
                };
            }
            case "ReturnStatement": {
                const argument = node.argument === null ? null : this.#expression(node.argument, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    this.#returned = argument === null ? undefined : argument(env);
                    return RETURN;
                };
            }
            case "IfStatement": {
                const test = this.#expression(node.test, scope);
                const consequent = this.#statement(node.consequent, scope, NO_LABELS);
                const alternate = node.alternate === null ? null : this.#statement(node.alternate, scope, NO_LABELS);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    if (truthy(test(env))) return consequent(env);
                    return alternate === null ? undefined : alternate(env);
                };
            }
            case "BlockStatement": {
                const lexical = lexicalScope(scope, node.body);
                if (lexical !== null && "error" in lexical) return this.#failing(lexical.error);
                const statements = this.#statements(node.body, lexical === null ? scope : lexical.scope);
                if (lexical === null) {
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        return statements(env);
                    };
                }
                const { scope: inner, initial } = lexical;
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return statements(new Env(inner, env, initial.slice()));
                };
            }
            case "EmptyStatement":
            // Instantiated with its function's body (`#planOf` refuses others).
            case "FunctionDeclaration":
                return () => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return undefined;
                };
            case "BreakStatement":
            case "ContinueStatement": {
                const type = node.type === "BreakStatement" ? "break" : "continue";
                const jump: Jump = node.label === null ? (type === "break" ? BREAK : CONTINUE) : { type, label: node.label.name };
                return () => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return jump;
                };
            }
            case "LabeledStatement": {
                const body = node.body;
                const label = node.label.name;
                const code = this.#statement(body, scope, isLoop(body) || body.type === "LabeledStatement" ? [...labels, label] : NO_LABELS);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const completion = code(env);
                    return completion?.type === "break" && completion.label === label ? undefined : completion;
                };
            }
            case "WhileStatement": {
                const test = this.#expression(node.test, scope);
                const body = this.#statement(node.body, scope, NO_LABELS);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    while (truthy(test(env))) {
                        const completion = body(env);
                        if (completion !== undefined && !continues(completion, labels)) return exitOf(completion);
                    }
                    return undefined;
                };
            }
            case "DoWhileStatement": {
                const test = this.#expression(node.test, scope);
                const body = this.#statement(node.body, scope, NO_LABELS);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    do {
                        const completion = body(env);
                        if (completion !== undefined && !continues(completion, labels)) return exitOf(completion);
                    } while (truthy(test(env)));
                    return undefined;
                };
            }
            case "ForStatement":
                return this.#for(node, scope, labels);
            case "ForInStatement":
            case "ForOfStatement":
                return this.#forInOf(node, scope, labels);
            case "SwitchStatement":
                return this.#switch(node, scope);
            case "ThrowStatement": {
                const argument = this.#expression(node.argument, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return thrown(`it throws ${typeOf(argument(env))}`);
                };
            }
            default:
                return this.#refusing(`it uses ${node.type}`);
        }
    }

    #for(node: Node & { type: "ForStatement" }, scope: Scope, labels: readonly string[]): Exec {
        const init = node.init;
        let loopScope = scope;
        let loopInitial: readonly Slot[] | null = null;
        /** CreatePerIterationEnvironment: closures of one iteration keep its copies of the `let` names. */
        let perIteration = false;
        let initDeclaration: Exec | null = null;
        let initExpression: Code | null = null;
        if (init?.type === "VariableDeclaration") {
            if (init.kind !== "var") {
                const lexical = lexicalScope(scope, [init]);
                if (lexical !== null && "error" in lexical) return this.#failing(lexical.error);
                if (lexical !== null) {
                    loopScope = lexical.scope;
                    loopInitial = lexical.initial;
                    perIteration = init.kind === "let";
                }
            }
            initDeclaration = this.#statement(init, loopScope, NO_LABELS);
        } else if (init !== null) {
            initExpression = this.#expression(init, scope);
        }
        const test = node.test === null ? null : this.#expression(node.test, loopScope);
        const update = node.update === null ? null : this.#expression(node.update, loopScope);
        const body = this.#statement(node.body, loopScope, NO_LABELS);
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const loopEnv = loopInitial === null ? env : new Env(loopScope, env, loopInitial.slice());
            if (initDeclaration !== null) initDeclaration(loopEnv);
            else if (initExpression !== null) initExpression(env);
            let iterationEnv = perIteration ? new Env(loopScope, loopEnv.parent, loopEnv.values.slice()) : loopEnv;
            for (;;) {
                if (test !== null && !truthy(test(iterationEnv))) return undefined;
                const completion = body(iterationEnv);
                if (completion !== undefined && !continues(completion, labels)) return exitOf(completion);
                if (perIteration) iterationEnv = new Env(loopScope, iterationEnv.parent, iterationEnv.values.slice());
                if (update !== null) update(iterationEnv);
            }
        };
    }

    #forInOf(node: Node & { type: "ForInStatement" | "ForOfStatement" }, scope: Scope, labels: readonly string[]): Exec {
        if (node.type === "ForOfStatement" && node.await) return this.#refusing("it uses for await");
        const left: Node = node.left;
        const declaration = left.type === "VariableDeclaration" ? left : undefined;
        const [declarator, ...others] = declaration?.declarations ?? [];
        if (declaration !== undefined && (declarator === undefined || others.length > 0 || declarator.init !== null)) return this.#refusing("its loop head declares something other than one binding");
        const lexical = declaration === undefined || declaration.kind === "var" ? null : lexicalScope(scope, [declaration]);
        if (lexical !== null && "error" in lexical) return this.#failing(lexical.error);
        const headScope = lexical === null ? scope : lexical.scope;
        const subject = this.#expression(node.right, headScope);
        let assign: (env: Env, value: JsValue) => Env;
        if (declarator !== undefined) {
            if (lexical === null) {
                const bind = this.#binder(declarator.id, scope, "assign");
                assign = (env, value) => {
                    bind(env, value);
                    return env;
                };
            } else {
                const bind = this.#binder(declarator.id, headScope, "init");
                const { initial } = lexical;
                assign = (env, value) => {
                    const iterationEnv = new Env(headScope, env, initial.slice());
                    bind(iterationEnv, value);
                    return iterationEnv;
                };
            }
        } else if (left.type === "ArrayPattern" || left.type === "ObjectPattern") {
            const bind = this.#binder(left, scope, "assign");
            assign = (env, value) => {
                bind(env, value);
                return env;
            };
        } else {
            const target = this.#target(left, scope);
            assign = (env, value) => {
                this.#put(this.#reference(target, env), value);
                return env;
            };
        }
        const body = this.#statement(node.body, headScope, NO_LABELS);
        const forOf = node.type === "ForOfStatement";
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const value = subject(lexical === null ? env : new Env(headScope, env, lexical.initial.slice()));
            const run = this.#run;
            if (forOf) {
                for (const item of iterate(value, run)) {
                    const completion = body(assign(env, item));
                    if (!continues(completion, labels)) return exitOf(completion);
                }
                return undefined;
            }
            const keys = forInKeys(value, run);
            const shape = shapeOf(value);
            for (const key of keys) {
                run.step(1);
                const completion = body(assign(env, key));
                if (!continues(completion, labels)) return exitOf(completion);
                // Whether keys added while enumerating are visited is engine-dependent (deleted ones would be skipped).
                if (shapeOf(value) !== shape) return refuse("it changes which keys an object has while enumerating them");
            }
            return undefined;
        };
    }

    #switch(node: Node & { type: "SwitchStatement" }, scope: Scope): Exec {
        const discriminant = this.#expression(node.discriminant, scope);
        const lexical = lexicalScope(
            scope,
            node.cases.flatMap((c) => c.consequent)
        );
        if (lexical !== null && "error" in lexical) {
            const { error } = lexical;
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                discriminant(env);
                throw error;
            };
        }
        const inner = lexical === null ? scope : lexical.scope;
        const tests = node.cases.map((c) => (c.test === null ? null : this.#expression(c.test, inner)));
        const bodies = node.cases.map((c) => this.#statements(c.consequent, inner));
        const fallback = node.cases.findIndex((c) => c.test === null);
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const value = discriminant(env);
            const scoped = lexical === null ? env : new Env(inner, env, lexical.initial.slice());
            let start = -1;
            for (let i = 0; i < tests.length; i++) {
                const test = tests[i];
                if (test !== null && test !== undefined && test(scoped) === value) {
                    start = i;
                    break;
                }
            }
            if (start === -1) start = fallback;
            if (start === -1) return undefined;
            for (let i = start; i < bodies.length; i++) {
                const completion = (bodies[i] as Exec)(scoped);
                if (completion !== undefined) return exitOf(completion);
            }
            return undefined;
        };
    }

    // ------------------------------------------------------------ expressions

    #key(node: MemberExpression, scope: Scope): KeyCode {
        if (node.computed) {
            const property = this.#expression(node.property, scope);
            return (env) => toStr(property(env), this.#run);
        }
        if (node.property.type !== "Identifier") return () => refuse("it uses a private name");
        const name = node.property.name;
        return () => name;
    }

    #arguments(list: readonly Node[], scope: Scope): (env: Env) => JsValue[] {
        if (list.some((arg) => arg.type === "SpreadElement")) {
            const parts = list.map((arg) => (arg.type === "SpreadElement" ? { spread: true, code: this.#expression(arg.argument, scope) } : { spread: false, code: this.#expression(arg, scope) }));
            return (env) => {
                const args: JsValue[] = [];
                for (const { spread, code } of parts) {
                    if (spread) for (const item of iterate(code(env), this.#run)) args.push(item);
                    else args.push(code(env));
                }
                return args;
            };
        }
        const codes = list.map((arg) => this.#expression(arg, scope));
        switch (codes.length) {
            case 0:
                return () => [];
            case 1: {
                const first = codes[0] as Code;
                return (env) => [first(env)];
            }
            case 2: {
                const first = codes[0] as Code;
                const second = codes[1] as Code;
                return (env) => {
                    const a = first(env);
                    return [a, second(env)];
                };
            }
            default:
                return (env) => {
                    const args: JsValue[] = [];
                    for (const code of codes) args.push(code(env));
                    return args;
                };
        }
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

    /** A binary operator on two values. */
    #operator(operator: string): Operator {
        const run = this.#run;
        switch (operator) {
            case "===":
                return (left, right) => left === right;
            case "!==":
                return (left, right) => left !== right;
            case "==":
                return (left, right) => this.#looseEquals(left, right);
            case "!=":
                return (left, right) => !this.#looseEquals(left, right);
            case "in":
                return (left, right) => {
                    if (!isObject(right)) return thrown("TypeError: in on a primitive");
                    return hasProperty(right, toStr(left, run), run);
                };
            case "**":
                return () => refuse("it uses **, whose result is implementation-approximated");
            default:
                break;
        }
        const general: Operator = (left, right) => {
            const result = binary(operator, toPrimitive(left, run), toPrimitive(right, run));
            if (!result.ok) return refuse(`it uses ${operator}`);
            if (typeof result.value === "string" && result.value.length > MAX_STRING) tooLong();
            return result.value;
        };
        // On primitives (`typeof` isn't "object": JsValue functions are objects), the host operator.
        if (operator === "+") {
            return (left, right) => {
                if (typeof left === "object" || typeof right === "object") return general(left, right);
                const result = (left as number) + (right as number);
                if (typeof result === "string" && (result as string).length > MAX_STRING) tooLong();
                return result;
            };
        }
        const primitive = PRIMITIVE_OPERATORS[operator] as ((left: JsValue, right: JsValue) => Value) | undefined;
        if (primitive === undefined) return general;
        return (left, right) => (typeof left === "object" || typeof right === "object" ? general(left, right) : primitive(left, right));
    }

    #expression(node: Node, scope: Scope): Code {
        const run = this.#run;
        switch (node.type) {
            case "Literal": {
                if ("regex" in node) return this.#refusing("it makes a regular expression");
                if (typeof node.value === "bigint") return this.#refusing("it uses a bigint");
                const value = node.value as Value;
                return () => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return value;
                };
            }
            case "Identifier":
                return this.#identifier(node as IdentifierReference, scope);
            case "ParenthesizedExpression": {
                const expression = this.#expression(node.expression, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return expression(env);
                };
            }
            case "TemplateLiteral": {
                const quasis = node.quasis.map((quasi) => quasi.value.cooked);
                const expressions = node.expressions.map((expression) => this.#expression(expression, scope));
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    let text = "";
                    for (let i = 0; i < quasis.length; i++) {
                        const cooked = quasis[i];
                        if (cooked === null || cooked === undefined) return refuse("its template has an invalid escape");
                        text += cooked;
                        const expression = expressions[i];
                        if (expression !== undefined) text += toStr(expression(env), run);
                        if (text.length > MAX_STRING) tooLong();
                    }
                    return text;
                };
            }
            case "ArrayExpression": {
                const elements = node.elements.map((element) =>
                    element === null ? null : element.type === "SpreadElement" ? { spread: true, code: this.#expression(element.argument, scope) } : { spread: false, code: this.#expression(element, scope) }
                );
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const items: JsValue[] = [];
                    for (const element of elements) {
                        if (element === null) items.length++;
                        else if (element.spread) for (const item of iterate(element.code(env), run)) items.push(item);
                        else items.push(element.code(env));
                    }
                    return new ArrayObject(items);
                };
            }
            case "ObjectExpression":
                return this.#object(node, scope);
            case "FunctionExpression":
            case "ArrowFunctionExpression": {
                if (node.async || node.generator) return this.#refusing("it makes an async function or a generator");
                const fn: FunctionLike = node;
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const substituted = this.#substitute?.(fn);
                    return substituted === undefined ? new Closure(fn, env) : substituted.value;
                };
            }
            case "UnaryExpression":
                return this.#unary(node, scope);
            case "UpdateExpression":
                return this.#update(node, scope);
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier") return this.#refusing("it uses a private name");
                const left = this.#expression(node.left, scope);
                const right = this.#expression(node.right, scope);
                if (node.operator === "===") {
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        const value = left(env);
                        return value === right(env);
                    };
                }
                if (node.operator === "!==") {
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        const value = left(env);
                        return value !== right(env);
                    };
                }
                const operator = this.#operator(node.operator);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = left(env);
                    return operator(value, right(env));
                };
            }
            case "LogicalExpression": {
                const left = this.#expression(node.left, scope);
                const right = this.#expression(node.right, scope);
                if (node.operator === "&&") {
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        const value = left(env);
                        return truthy(value) ? right(env) : value;
                    };
                }
                if (node.operator === "||") {
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        const value = left(env);
                        return truthy(value) ? value : right(env);
                    };
                }
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = left(env);
                    return value !== null && value !== undefined ? value : right(env);
                };
            }
            case "ConditionalExpression": {
                const test = this.#expression(node.test, scope);
                const consequent = this.#expression(node.consequent, scope);
                const alternate = this.#expression(node.alternate, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return truthy(test(env)) ? consequent(env) : alternate(env);
                };
            }
            case "SequenceExpression": {
                const expressions = node.expressions.map((expression) => this.#expression(expression, scope));
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    let last: JsValue;
                    for (const expression of expressions) last = expression(env);
                    return last;
                };
            }
            case "AssignmentExpression":
                return this.#assignment(node, scope);
            case "MemberExpression":
                return this.#member(node, scope);
            case "ThisExpression": {
                let hops = 0;
                let at: Scope | null = scope;
                while (at !== null && !at.ownThis) {
                    at = at.parent;
                    hops++;
                }
                if (at === null) return this.#refusing("it reads this outside its functions");
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const self = envAt(env, hops).self;
                    return isObject(self) ? self : refuse(`it reads this of a call with ${self === undefined ? "no" : `a ${typeOf(self)}`} receiver`);
                };
            }
            case "ChainExpression": {
                const expression = this.#expression(node.expression, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    try {
                        return expression(env);
                    } catch (error) {
                        if (error === SHORT_CIRCUIT) return undefined;
                        throw error;
                    }
                };
            }
            case "CallExpression":
                return this.#call(node, scope);
            case "NewExpression": {
                const callee = this.#expression(node.callee, scope);
                const args = this.#arguments(node.arguments, scope);
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const constructor = callee(env);
                    const values = args(env);
                    if (constructor instanceof Native && constructor.construct !== undefined) return constructor.construct(values, run);
                    return refuse("it constructs something other than an array");
                };
            }
            default:
                return this.#refusing(`it uses ${node.type}`);
        }
    }

    #identifier(identifier: IdentifierReference, scope: Scope): Code {
        const name = identifier.name;
        const binding = resolve(scope, name);
        if (binding === undefined) {
            let known = false;
            let value: JsValue;
            return () => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                if (!known) {
                    value = this.#outerValue(identifier);
                    known = true;
                }
                return value;
            };
        }
        const { hops, index } = binding;
        switch (hops) {
            case 0:
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = env.values[index];
                    return value === TDZ ? readTdz(name) : value;
                };
            case 1:
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = (env.parent as Env).values[index];
                    return value === TDZ ? readTdz(name) : value;
                };
            default:
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = envAt(env, hops).values[index];
                    return value === TDZ ? readTdz(name) : value;
                };
        }
    }

    #object(node: Node & { type: "ObjectExpression" }, scope: Scope): Code {
        const run = this.#run;
        type Part = (env: Env, object: PlainObject) => void;
        const parts: Part[] = node.properties.map((property): Part => {
            if (property.type === "SpreadElement") {
                const argument = this.#expression(property.argument, scope);
                return (env, object) => copyOwn(object, argument(env), new Set(), run);
            }
            if (property.kind !== "init") return () => refuse("it defines a getter or setter");
            const value = this.#expression(property.value, scope);
            if (property.computed) {
                const key = this.#expression(property.key, scope);
                return (env, object) => {
                    const name = toStr(key(env), run);
                    object.props.set(name, value(env));
                };
            }
            let name: string;
            try {
                name = staticKey(property.key);
            } catch (error) {
                return () => {
                    throw error;
                };
            }
            if (name === "__proto__" && !property.shorthand && !property.method) return () => refuse("it sets a prototype in an object literal");
            return (env, object) => {
                object.props.set(name, value(env));
            };
        });
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const object = new PlainObject();
            for (const part of parts) part(env, object);
            return object;
        };
    }

    #unary(node: Node & { type: "UnaryExpression" }, scope: Scope): Code {
        const argument = unparenthesized(node.argument);
        const operator = node.operator;
        if (operator === "delete") {
            if (argument.type !== "MemberExpression") return this.#refusing("it deletes something other than a member");
            const object = this.#expression(argument.object, scope);
            const key = this.#key(argument, scope);
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const target = object(env);
                const name = key(env);
                if (target === null || target === undefined) return thrown(`TypeError: cannot delete ${name} of ${target}`);
                return deleteMember(target, name);
            };
        }
        const operand = this.#expression(argument, scope);
        const run = this.#run;
        switch (operator) {
            case "typeof":
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return typeOf(operand(env));
                };
            case "!":
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    return !truthy(operand(env));
                };
            case "void":
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    operand(env);
                    return undefined;
                };
            default:
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const result = unary(operator, toPrimitive(operand(env), run));
                    return result.ok ? result.value : refuse(`it uses ${operator}`);
                };
        }
    }

    #update(node: Node & { type: "UpdateExpression" }, scope: Scope): Code {
        const run = this.#run;
        const increment = node.operator === "++";
        const prefix = node.prefix;
        const argument = unparenthesized(node.argument);
        if (argument.type === "Identifier") {
            const binding = resolve(scope, argument.name);
            if (binding !== undefined && binding.mutable) {
                const { hops, index } = binding;
                const name = argument.name;
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const values = envAt(env, hops).values;
                    const current = values[index];
                    if (current === TDZ) return readTdz(name);
                    const old = typeof current === "number" ? current : toNum(current, run);
                    const next = increment ? old + 1 : old - 1;
                    values[index] = next;
                    return prefix ? next : old;
                };
            }
        }
        const target = this.#target(argument, scope);
        if (target.kind === "invalid") return this.#refusing(target.reason);
        if (target.kind === "binding") {
            const { lookup, assign } = target;
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const old = toNum(lookup(env), run);
                const next = increment ? old + 1 : old - 1;
                assign(env, next);
                return prefix ? next : old;
            };
        }
        const { object, key } = target;
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const base = object(env);
            const name = key(env);
            const old = toNum(getMember(base, name, run), run);
            const next = increment ? old + 1 : old - 1;
            setMember(base, name, next, run);
            return prefix ? next : old;
        };
    }

    #member(node: MemberExpression, scope: Scope): Code {
        const run = this.#run;
        const object = this.#expression(node.object, scope);
        const optional = node.optional;
        if (node.computed) {
            const property = this.#expression(node.property, scope);
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const base = object(env);
                if (optional && (base === null || base === undefined)) throw SHORT_CIRCUIT;
                const key = property(env);
                if (typeof key === "number" && isIndex(key)) {
                    if (typeof base === "string") return base[key];
                    if (base instanceof ArrayObject) return base.items[key];
                }
                return getMember(base, toStr(key, run), run);
            };
        }
        const key = this.#key(node, scope);
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const base = object(env);
            if (optional && (base === null || base === undefined)) throw SHORT_CIRCUIT;
            return getMember(base, key(env), run);
        };
    }

    #call(node: Node & { type: "CallExpression" }, scope: Scope): Code {
        const run = this.#run;
        const callee = unparenthesized(node.callee);
        const args = this.#arguments(node.arguments, scope);
        const optional = node.optional;
        if (callee.type === "MemberExpression") {
            const object = this.#expression(callee.object, scope);
            const key = this.#key(callee, scope);
            const optionalObject = callee.optional;
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const self = object(env);
                if (optionalObject && (self === null || self === undefined)) throw SHORT_CIRCUIT;
                const fn = getMember(self, key(env), run);
                if (optional && (fn === null || fn === undefined)) throw SHORT_CIRCUIT;
                return this.#callValue(fn, self, args(env));
            };
        }
        const code = this.#expression(callee, scope);
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const fn = code(env);
            // A plain call's `this` is `undefined`.
            if (optional && (fn === null || fn === undefined)) throw SHORT_CIRCUIT;
            return this.#callValue(fn, undefined, args(env));
        };
    }

    #assignment(node: Node & { type: "AssignmentExpression" }, scope: Scope): Code {
        const { operator, left } = node;
        const right = this.#expression(node.right, scope);
        const run = this.#run;
        if (operator === "=" && (left.type === "ArrayPattern" || left.type === "ObjectPattern")) {
            const bind = this.#binder(left, scope, "assign");
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const value = right(env);
                bind(env, value);
                return value;
            };
        }
        const target = this.#target(left, scope);
        if (target.kind === "invalid") return this.#refusing(target.reason);
        const logical = operator === "&&=" || operator === "||=" || operator === "??=";
        const done = (current: JsValue): boolean => (operator === "&&=" ? !truthy(current) : operator === "||=" ? truthy(current) : current !== null && current !== undefined);
        const combine = operator === "=" || logical ? null : this.#operator(operator.slice(0, -1));
        if (target.kind === "binding") {
            const { lookup, assign } = target;
            const name = unparenthesized(left).type === "Identifier" ? (unparenthesized(left) as IdentifierReference).name : "";
            const binding = resolve(scope, name);
            if (operator === "=") {
                if (binding !== undefined && binding.mutable) {
                    const { hops, index } = binding;
                    return (env) => {
                        if (++this.#steps > this.#limit) throw EXHAUSTED;
                        const value = right(env);
                        const values = envAt(env, hops).values;
                        if (values[index] === TDZ) writeTdz(name);
                        values[index] = value;
                        return value;
                    };
                }
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const value = right(env);
                    assign(env, value);
                    return value;
                };
            }
            if (logical) {
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const current = lookup(env);
                    if (done(current)) return current;
                    const value = right(env);
                    assign(env, value);
                    return value;
                };
            }
            const operate = combine as Operator;
            if (binding !== undefined && binding.mutable) {
                const { hops, index } = binding;
                return (env) => {
                    if (++this.#steps > this.#limit) throw EXHAUSTED;
                    const values = envAt(env, hops).values;
                    const current = values[index];
                    if (current === TDZ) return readTdz(name);
                    const value = operate(current, right(env));
                    values[index] = value;
                    return value;
                };
            }
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const value = operate(lookup(env), right(env));
                assign(env, value);
                return value;
            };
        }
        const { object } = target;
        const computed = node.left.type === "MemberExpression" && node.left.computed ? this.#expression(node.left.property, scope) : null;
        if (operator === "=" && computed !== null) {
            // `a[i] = v` on an array by index: what `setMember` does with the index's string.
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const base = object(env);
                const key = computed(env);
                const name = typeof key === "number" ? key : toStr(key, run);
                const value = right(env);
                if (typeof name === "number") {
                    if (base instanceof ArrayObject && !base.frozen && isIndex(name)) {
                        const items = base.items;
                        if (!(name in items)) base.shape++;
                        items[name] = value;
                        return value;
                    }
                    setMember(base, String(name), value, run);
                    return value;
                }
                setMember(base, name, value, run);
                return value;
            };
        }
        const { key } = target;
        if (operator === "=") {
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const base = object(env);
                const name = key(env);
                const value = right(env);
                setMember(base, name, value, run);
                return value;
            };
        }
        if (logical) {
            return (env) => {
                if (++this.#steps > this.#limit) throw EXHAUSTED;
                const base = object(env);
                const name = key(env);
                const current = getMember(base, name, run);
                if (done(current)) return current;
                const value = right(env);
                setMember(base, name, value, run);
                return value;
            };
        }
        const operate = combine as Operator;
        return (env) => {
            if (++this.#steps > this.#limit) throw EXHAUSTED;
            const base = object(env);
            const name = key(env);
            const value = operate(getMember(base, name, run), right(env));
            setMember(base, name, value, run);
            return value;
        };
    }
}
