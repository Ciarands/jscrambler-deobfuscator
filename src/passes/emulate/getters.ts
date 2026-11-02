import type { Function as FunctionNode, FunctionLike, Node, Statement } from "../../core/ast.js";
import { isIndexKey, propertyKey } from "../../core/ast.js";
import { binary, unary } from "../../core/evaluate.js";
import type { Value } from "../../core/evaluate.js";
import { hoistedDeclarations } from "../../core/hoisting.js";
import type { PrintedFunctions } from "../../core/print.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { parentsWithin } from "./builders.js";
import type { AccessorFunctions, FunctionSite, Guest, Lookup, PropertyPath } from "./guest.js";
import { pathName } from "./guest.js";

/**
 * Whether a getter the setup installed answers, on every later call, what emulate's probes saw: the proof behind
 * every getter-based alias (user decision 2026-11-02: a static proof, or no alias).
 *
 * 1. The getter's code: the guest tells where the installed function starts (QuickJS's `fileName`, `lineNumber`,
 *    `columnNumber`; each run has its own file), found in the printed statement's function starts.
 * 2. The values it closes over: the statement that installed it is evaluated abstractly (`Evaluator`, phase
 *    "setup"): its frames, their variables and local arrays, and every `Object.defineProperty` it makes. A value is a
 *    primitive, a builtin (a path from the global object through properties the builtins had before the program
 *    ran, as the guest finds them), the storage object, a closure, an object the evaluation made, or unknown; sets of
 *    them where paths join. No accessor the program added may run before the statement finishes (it may be one the
 *    statement installed, answering from frames still running): the evaluation refuses any lookup that may reach one.
 * 3. The getter's calls (phase "call"): its code may write only what its own call makes, and read only its own
 *    values, its arguments and `this` (per call), builtins (model 7: builtins intact; the program adds nothing to
 *    them but the aliases emulate tracks, so a property they lack stays absent), and what enclosing frames left
 *    behind where nothing but their own body writes it (they finished before the getter could run; locals and
 *    local arrays never handed on). A global the builtins lack is a live read (`host`). The same calls tell whether
 *    `G.key(...)` uses `G` (its `this`) at all (`GetterProofs.thisFree`).
 *
 * The subset: `var` declarations, expression statements, `if`, `return`, blocks, `try`/`catch` (setup only), calls of
 * functions it can tell, local arrays and plain objects, `arguments` read by index, primitive operators. Anything else
 * refuses with a reason.
 */

type AV =
    | { readonly k: "prim"; readonly v: Value }
    /** A builtin object or function: `path` from the global object (an owner's path, or a holder's path and key). */
    | { readonly k: "builtin"; readonly path: PropertyPath; readonly type: string }
    | { readonly k: "storage" }
    | { readonly k: "fn"; readonly node: FunctionLike; readonly env: number }
    | { readonly k: "obj"; readonly id: number }
    /** Phase "call": a value the call's arguments or `this` give (another each call); `index` for `arguments[index]`. */
    | { readonly k: "arg"; readonly index?: number }
    /** Phase "call": the analysed call's `arguments`. */
    | { readonly k: "args" }
    /** Phase "call": the global property `name` the builtins lack, as read now (it may change). */
    | { readonly k: "host"; readonly name: string }
    /** Phase "call": `typeof host(name) == "undefined"` (`when` true), or its negation. */
    | { readonly k: "guard"; readonly name: string; readonly when: boolean }
    | { readonly k: "unknown" };

type Values = readonly AV[];

const UNKNOWN: AV = { k: "unknown" };
const ARG: AV = { k: "arg" };
const UNDEFINED: AV = { k: "prim", v: undefined };
const prim = (v: Value): AV => ({ k: "prim", v });

const MAX_VALUES = 8;
const MAX_STEPS = 2_000_000;
const MAX_DEPTH = 64;
const MAX_STRING = 1 << 16;
/** The frame of the program's top level (or its lone IIFE): its bindings are resolved by `#rootBinding`. */
const ROOT = 0;

const FUNCTION_CALL: PropertyPath = ["Function", "prototype", "call"];
const FUNCTION_APPLY: PropertyPath = ["Function", "prototype", "apply"];
const DEFINE_PROPERTY: PropertyPath = ["Object", "defineProperty"];
/** The only other builtin the setup phase calls: it reads no property, so it runs no program code. */
const HAS_OWN_PROPERTY: PropertyPath = ["Object", "prototype", "hasOwnProperty"];

const samePath = (a: PropertyPath, b: PropertyPath): boolean => a.length === b.length && a.every((key, i) => key === b[i]);

const sameValue = (a: AV, b: AV): boolean => {
    switch (a.k) {
        case "prim":
            return b.k === "prim" && Object.is(a.v, b.v);
        case "builtin":
            return b.k === "builtin" && samePath(a.path, b.path);
        case "fn":
            return b.k === "fn" && a.node === b.node && a.env === b.env;
        case "obj":
            return b.k === "obj" && a.id === b.id;
        case "arg":
            return b.k === "arg" && a.index === b.index;
        case "host":
            return b.k === "host" && a.name === b.name;
        case "guard":
            return b.k === "guard" && a.name === b.name && a.when === b.when;
        default:
            return a.k === b.k;
    }
};

const union = (a: Values, b: Values): Values => {
    if (a.length === 0) return b;
    const out = [...a];
    for (const value of b) if (!out.some((known) => sameValue(known, value))) out.push(value);
    return out.length > MAX_VALUES ? [UNKNOWN] : out;
};

class Refusal {
    constructor(
        readonly reason: string,
        readonly node: Node | undefined
    ) {}
}

const refuse = (reason: string, node?: Node): never => {
    throw new Refusal(reason, node);
};

interface HeapObject {
    readonly kind: "frame" | "array" | "object" | "arguments";
    /** Frame variables by name; array and object properties by key; an `arguments` object's values past its parameters. */
    readonly props: Map<string, Values>;
    /** A frame's function (none for `ROOT`) and its lexical parent frame. */
    readonly fn?: FunctionLike;
    readonly parent?: number;
    /** An `arguments` object's frame, the parameter names it maps, and how many arguments the call passed. */
    readonly frame?: number;
    readonly params?: readonly string[];
    readonly argc?: number;
    /** The local array variable an array literal initialises. */
    readonly holder?: Variable;
}

class State {
    constructor(
        public heap: Map<number, HeapObject>,
        /** Host globals this path found undefined (`guard`). */
        public facts: ReadonlySet<string>,
        /** Phase "call" on a setter: its writes of the forwarded global so far; -1 when paths disagree. */
        public hostWrites: number,
        /** Phase "setup": names it may have added to builtins so far (an accessor may sit there). */
        public added: ReadonlySet<string>
    ) {}

    /** Objects only this state holds: written in place. Any sharing (`clone`, `join`, a catcher) ends it. */
    owned = new Set<HeapObject>();

    clone(): State {
        this.owned = new Set();
        return new State(new Map(this.heap), this.facts, this.hostWrites, this.added);
    }

    set(other: State): void {
        this.heap = other.heap;
        this.facts = other.facts;
        this.hostWrites = other.hostWrites;
        this.added = other.added;
        this.owned = other.owned;
        other.owned = new Set();
    }

    /** Copy-on-write: the object as this state may change it. */
    writable(id: number): HeapObject {
        const object = this.heap.get(id);
        if (object === undefined) return refuse("an object the evaluation lost");
        if (this.owned.has(object)) return object;
        const copy = { ...object, props: new Map(object.props) };
        this.heap.set(id, copy);
        this.owned.add(copy);
        return copy;
    }

    static join(a: State | undefined, b: State | undefined): State | undefined {
        if (a === undefined) return b;
        if (b === undefined || a === b) return a;
        a.owned = new Set();
        b.owned = new Set();
        const heap = new Map(a.heap);
        for (const [id, other] of b.heap) {
            const mine = heap.get(id);
            if (mine === undefined) heap.set(id, other);
            else if (mine !== other) {
                const props = new Map(mine.props);
                for (const [key, values] of other.props) props.set(key, union(props.get(key) ?? [UNDEFINED], values));
                for (const [key, values] of mine.props) if (!other.props.has(key)) props.set(key, union(values, [UNDEFINED]));
                heap.set(id, { ...mine, props });
            }
        }
        const facts = new Set([...a.facts].filter((name) => b.facts.has(name)));
        const added = a.added === b.added ? a.added : new Set([...a.added, ...b.added]);
        return new State(heap, facts, a.hostWrites === b.hostWrites ? a.hostWrites : -1, added);
    }
}

interface Flow {
    readonly normal: State | undefined;
    readonly returns: readonly { readonly values: Values; readonly state: State }[];
}

/** An `Object.defineProperty` the setup evaluation made: what it may target, under which key, with which accessors. */
export interface Installation {
    readonly targets: Values;
    readonly keys: Values;
    readonly getters: Values;
    readonly setters: Values;
}

interface Mode {
    readonly phase: "setup" | "call";
    /** Phase "call": `arguments` holds no value (a call with none). */
    readonly zero: boolean;
    /** Phase "call": the global a setter forwards to (its one write). */
    readonly forwards: string | undefined;
    /** Phase "call": objects (and frames) with an id at least this were made by the analysed call. */
    readonly watermark: number;
    /** Phase "call": the analysed function; functions inside it may be called. */
    readonly root: FunctionLike | undefined;
    /**
     * Phase "call" of an accessor (or of `G.key()`): the answer must not depend on `this` or the arguments beyond
     * passing them on, nor may it run code they lead to (a getter on the receiver, a conversion), nor throw.
     */
    readonly accessor: boolean;
    /** Phase "call", asking only where `this` goes: a global the builtins lack is just another value from outside. */
    readonly opaqueGlobals: boolean;
}

const SETUP: Mode = { phase: "setup", zero: false, forwards: undefined, watermark: 0, root: undefined, accessor: false, opaqueGlobals: false };

const isWithin = (node: Node, root: Node): boolean => node.start >= root.start && node.end <= root.end;

/** What the evaluator needs from emulate: scopes, the guest's builtin lookups, the owners and their original names. */
export interface EvaluatorContext {
    readonly scopes: ScopeInfo;
    readonly guest: Guest;
    readonly storage: string;
    /** The program and its lone root IIFE: their bindings are the program's own (`#rootBinding`). */
    readonly rootBlocks: ReadonlySet<Node>;
    readonly owners: readonly PropertyPath[];
    /** Each owner's own names before the program ran, by owner index. */
    readonly before: readonly ReadonlySet<string>[];
    /** The guest's answers to `lookup`, shared by every evaluation (builtins don't change: model 7). */
    readonly lookups: Map<string, Lookup | undefined>;
}

/** Abstract evaluation of a setup statement, then of calls of the getters it installed (see the module comment). */
export class Evaluator {
    readonly #cx: EvaluatorContext;
    readonly #fixedVariables = new Map<Variable, boolean>();
    readonly #slotsMemo = new Map<Variable, boolean>();
    readonly #parents = new Map<Node, Map<Node, Node>>();
    readonly #fixedArguments = new Map<Node, boolean>();
    #nextId = ROOT + 1;
    #steps = 0;
    #depth = 0;
    #mode: Mode = SETUP;
    /** Phase "setup": what the program added to builtins before the statement (`AddedNames`). */
    #added: AddedNames = { names: new Set(), accessors: new Set() };
    /** Join of the states a throw may leave, for each `try` being evaluated (innermost last). */
    readonly #catchers: (State | undefined)[] = [];
    readonly installations: Installation[] = [];
    /** Phase "call": the globals the builtins lack that the call read. */
    readonly hostReads = new Set<string>();
    /** Phase "call": whether the call read `this`. */
    usesThis = false;

    constructor(cx: EvaluatorContext) {
        this.#cx = cx;
    }

    /**
     * The setup statement `f(args)` (`f` a root function declaration, or a function expression): its final state, or
     * why it can't be told. `globalArgs`: arguments the guest found to hold the global object right before it ran.
     * `added`: what the program added to builtins before it.
     *
     * No program accessor may run before the statement finishes (an installed getter would answer from frames still
     * running, and its calls there aren't what the proof covers): reads and writes that may reach one refuse.
     */
    runSetup(statement: Statement, globalArgs: ReadonlySet<Node>, added: AddedNames): State | Refusal {
        try {
            this.#mode = SETUP;
            this.#added = added;
            const state = new State(new Map([[ROOT, { kind: "frame", props: new Map() }]]), new Set(), 0, new Set());
            const call = statement.type === "ExpressionStatement" && statement.expression.type === "CallExpression" ? statement.expression : undefined;
            const callee = call?.callee;
            if (call === undefined || (callee?.type !== "Identifier" && callee?.type !== "FunctionExpression" && callee?.type !== "ArrowFunctionExpression"))
                return refuse("the statement isn't a call of a root function or a function expression", statement);
            const args = call.arguments.map((arg): Values => {
                if (arg.type === "SpreadElement") return refuse("it spreads arguments", arg);
                return globalArgs.has(arg) ? [{ k: "builtin", path: [], type: "object" }] : this.#eval(arg, ROOT, state);
            });
            for (const fn of this.#eval(callee, ROOT, state)) {
                if (fn.k !== "fn") return refuse("the statement calls something other than a function of the program", call);
                this.#invoke(fn, args, state);
            }
            return state;
        } catch (error) {
            if (error instanceof Refusal) return error;
            throw error;
        }
    }

    /**
     * One call of `fn` (a closure of the final setup state `after`), from outside: its arguments and `this` per call,
     * or none (`zero`). `forwards`: a setter, which must write that global once on every path. Returns what it may
     * return, or why it isn't a call whose answers stay what they were.
     */
    call(fn: AV, after: State, options: { zero: boolean; accessor: boolean; forwards?: string; opaqueGlobals?: boolean }): { values: Values; state: State } | Refusal {
        try {
            if (fn.k !== "fn") return refuse("the accessor isn't a function of the setup");
            this.#mode = {
                phase: "call",
                zero: options.zero,
                forwards: options.forwards,
                watermark: this.#nextId,
                root: fn.node,
                accessor: options.accessor,
                opaqueGlobals: options.opaqueGlobals ?? false,
            };
            this.hostReads.clear();
            this.usesThis = false;
            const state = after.clone();
            state.facts = new Set();
            state.hostWrites = 0;
            const values = this.#invoke(fn, undefined, state);
            return { values, state };
        } catch (error) {
            if (error instanceof Refusal) return error;
            throw error;
        }
    }

    #step(node: Node): void {
        if (++this.#steps > MAX_STEPS) refuse(`the evaluation ran past ${MAX_STEPS} steps`, node);
    }

    get #setup(): boolean {
        return this.#mode.phase === "setup";
    }

    /** Phase "setup" goes on with an unknown value; phase "call" refuses. */
    #unknown(reason: string, node: Node | undefined): Values {
        return this.#setup ? [UNKNOWN] : refuse(reason, node);
    }

    #own(id: number): boolean {
        return this.#mode.phase === "setup" || id >= this.#mode.watermark;
    }

    /** A throw may come here: the innermost `try`'s catch block may start from this state too. */
    #effect(state: State): void {
        const last = this.#catchers.length - 1;
        if (last >= 0) this.#catchers[last] = State.join(this.#catchers[last], state);
    }

    /**
     * `#effect` after writes of `written` (object, key) and of `state.added`, without joining the whole heap: every
     * earlier state a throw may leave is in the catcher already, and these writes are all this one adds.
     */
    #effectWrites(state: State, written: readonly (readonly [number, string])[]): void {
        const catcher = this.#catchers.at(-1);
        if (catcher === undefined) return;
        for (const [id, key] of written) {
            this.#ensure(catcher, state, id);
            const values = state.heap.get(id)?.props.get(key) ?? [UNDEFINED];
            const target = catcher.writable(id);
            target.props.set(key, union(target.props.get(key) ?? [UNDEFINED], values));
            for (const value of values) this.#ensureValue(catcher, state, value);
        }
        if (state.added !== catcher.added) catcher.added = new Set([...catcher.added, ...state.added]);
    }

    /** Object `id` (made since the `try` began) in the catcher, with the objects it reaches. */
    #ensure(catcher: State, state: State, id: number): void {
        if (catcher.heap.has(id)) return;
        const object = state.heap.get(id);
        if (object === undefined) return;
        catcher.heap.set(id, object);
        state.owned.delete(object);
        for (const values of object.props.values()) for (const value of values) this.#ensureValue(catcher, state, value);
        if (object.parent !== undefined) this.#ensure(catcher, state, object.parent);
        if (object.frame !== undefined) this.#ensure(catcher, state, object.frame);
    }

    #ensureValue(catcher: State, state: State, value: AV): void {
        if (value.k === "obj") this.#ensure(catcher, state, value.id);
        else if (value.k === "fn") this.#ensure(catcher, state, value.env);
    }

    // ------------------------------------------------------------ frames and calls

    /**
     * Calls closure `fn`. `args`: the values passed, or `undefined` for phase "call"'s analysed call (arguments per
     * call). The state becomes the join of the call's exits; returns what it may return. `this` is never tracked:
     * unknown in phase "setup", per call in phase "call".
     */
    #invoke(fn: AV & { k: "fn" }, args: readonly Values[] | undefined, state: State): Values {
        const node = fn.node;
        if (node.async || (node.type !== "ArrowFunctionExpression" && node.generator)) return refuse("it calls an async function or a generator", node);
        if (++this.#depth > MAX_DEPTH) refuse(`calls nest deeper than ${MAX_DEPTH}`, node);
        try {
            const frame = this.#enterFrame(node, fn.env, args, state);
            const body = node.body;
            if (body === null) return refuse("a function without a body", node);
            if (body.type !== "BlockStatement") {
                const values = this.#eval(body, frame, state);
                return values;
            }
            const flow = this.#statements(body.body, frame, state);
            let exit = flow.normal;
            let values: Values = flow.normal === undefined ? [] : [UNDEFINED];
            for (const returned of flow.returns) {
                exit = State.join(exit, returned.state);
                values = union(values, returned.values);
            }
            // No exit: every path throws; the caller's path ends too.
            if (exit !== undefined) state.set(exit);
            return values;
        } finally {
            this.#depth--;
        }
    }

    #enterFrame(fn: FunctionLike, env: number, args: readonly Values[] | undefined, state: State): number {
        const id = this.#nextId++;
        const props = new Map<string, Values>();
        const params: string[] = [];
        for (const [i, param] of fn.params.entries()) {
            if (param.type === "Identifier") {
                params.push(param.name);
                props.set(param.name, args === undefined ? (this.#mode.zero ? [UNDEFINED] : [{ k: "arg", index: i }]) : (args[i] ?? [UNDEFINED]));
            } else if (param.type === "RestElement" && param.argument.type === "Identifier" && args === undefined) {
                props.set(param.argument.name, this.#mode.zero ? [{ k: "args" }] : [ARG]);
            } else return refuse("a destructuring, default or rest parameter", param);
        }
        state.heap.set(id, { kind: "frame", props, fn, parent: env });
        if (fn.type !== "ArrowFunctionExpression") {
            if (args === undefined) props.set("arguments", [{ k: "args" }]);
            else {
                const argumentsId = this.#nextId++;
                const extra = new Map<string, Values>();
                for (let i = params.length; i < args.length; i++) extra.set(String(i), args[i] as Values);
                state.heap.set(argumentsId, { kind: "arguments", props: extra, frame: id, params, argc: args.length });
                props.set("arguments", [{ k: "obj", id: argumentsId }]);
            }
        }
        if (fn.body?.type === "BlockStatement") {
            const statements = fn.body.body;
            const hoisted = { vars: new Set<string>(), functions: [] as FunctionNode[] };
            for (const statement of statements) hoistedDeclarations(statement, hoisted);
            for (const name of hoisted.vars) if (!props.has(name)) props.set(name, [UNDEFINED]);
            for (const declaration of hoisted.functions) {
                if (!statements.includes(declaration) || declaration.id === null) return refuse("a function declared in a block", declaration);
                props.set(declaration.id.name, [{ k: "fn", node: declaration, env: id }]);
            }
        }
        return id;
    }

    // ------------------------------------------------------------ statements

    #statements(statements: readonly Node[], frame: number, state: State): Flow {
        let normal: State | undefined = state;
        const returns: { values: Values; state: State }[] = [];
        for (const statement of statements) {
            if (normal === undefined) break;
            const flow = this.#statement(statement, frame, normal);
            for (const returned of flow.returns) returns.push(returned);
            normal = flow.normal;
        }
        return { normal, returns };
    }

    #statement(node: Node, frame: number, state: State): Flow {
        this.#step(node);
        switch (node.type) {
            case "ExpressionStatement":
                return { normal: this.#eval(node.expression, frame, state).length === 0 ? undefined : state, returns: [] };
            case "VariableDeclaration": {
                if (node.kind !== "var") return refuse(`a ${node.kind} declaration`, node);
                for (const declarator of node.declarations) {
                    if (declarator.id.type !== "Identifier") return refuse("a destructuring declaration", declarator);
                    if (declarator.init === null) continue;
                    const values = this.#eval(declarator.init, frame, state, declarator);
                    if (values.length === 0) return { normal: undefined, returns: [] };
                    this.#writeVariable(declarator.id, values, frame, state);
                }
                return { normal: state, returns: [] };
            }
            case "FunctionDeclaration":
            case "EmptyStatement":
                return { normal: state, returns: [] };
            case "BlockStatement":
                if (node.body.some((statement) => statement.type === "FunctionDeclaration")) return refuse("a function declared in a block", node);
                return this.#statements(node.body, frame, state);
            case "ReturnStatement": {
                const values = node.argument === null ? [UNDEFINED] : this.#eval(node.argument, frame, state);
                return { normal: undefined, returns: values.length === 0 ? [] : [{ values: this.#underFacts(values, state), state }] };
            }
            case "ThrowStatement":
                if (!this.#setup) return refuse("it may throw", node);
                this.#eval(node.argument, frame, state);
                this.#effect(state);
                return { normal: undefined, returns: [] };
            case "IfStatement": {
                const test = this.#eval(node.test, frame, state);
                const branches = this.#branches(test, state);
                let normal: State | undefined;
                const returns: { values: Values; state: State }[] = [];
                for (const [taken, branchState] of branches) {
                    const flow = taken
                        ? this.#statement(node.consequent, frame, branchState)
                        : node.alternate === null
                          ? { normal: branchState, returns: [] }
                          : this.#statement(node.alternate, frame, branchState);
                    normal = State.join(normal, flow.normal);
                    for (const returned of flow.returns) returns.push(returned);
                }
                return { normal, returns };
            }
            case "TryStatement": {
                if (!this.#setup) return refuse("a try statement", node);
                if (node.finalizer !== null) return refuse("a finally block", node);
                this.#catchers.push(state.clone());
                let flow: Flow;
                let thrown: State | undefined;
                try {
                    flow = this.#statement(node.block, frame, state);
                } finally {
                    thrown = this.#catchers.pop();
                }
                // The catch parameter is never read (`#identifier` refuses catch bindings).
                let normal = flow.normal;
                let returns = flow.returns;
                if (node.handler !== null && thrown !== undefined) {
                    // A throw from the catch block may leave what it started from.
                    this.#effect(thrown);
                    const caught = this.#statement(node.handler.body, frame, thrown);
                    normal = State.join(normal, caught.normal);
                    returns = [...returns, ...caught.returns];
                }
                // An outer `try` may catch a later throw: its join must see what this one's paths left.
                if (normal !== undefined) this.#effect(normal);
                return { normal, returns };
            }
            default:
                return refuse(`a ${node.type}, which the evaluation doesn't follow`, node);
        }
    }

    /** Under a `guard` fact, `undefined` is that global's value as read: the getter hands that out. */
    #underFacts(values: Values, state: State): Values {
        if (state.facts.size !== 1) return values;
        const [name] = state.facts;
        return values.map((value) => (value.k === "prim" && value.v === undefined && name !== undefined ? { k: "host", name } : value));
    }

    /** Whether `test` may be truthy, and falsy. */
    #truths(test: Values): { truthy: boolean; falsy: boolean } {
        let truthy = false;
        let falsy = false;
        for (const value of test) {
            if (value.k === "prim") {
                if (value.v) truthy = true;
                else falsy = true;
            } else if (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage") truthy = true;
            else {
                if (value.k !== "guard" && this.#mode.accessor) refuse("it branches on its receiver, its arguments or a live global");
                truthy = true;
                falsy = true;
            }
        }
        return { truthy, falsy };
    }

    /** The branches a test may take, each with its own state (and a `guard`'s fact on the branch where it holds). */
    #branches(test: Values, state: State): [boolean, State][] {
        const { truthy, falsy } = this.#truths(test);
        if (!truthy || !falsy) return truthy ? [[true, state]] : falsy ? [[false, state]] : [];
        const guard = test.length === 1 && test[0]?.k === "guard" ? test[0] : undefined;
        const other = state.clone();
        if (guard !== undefined) {
            const holds = guard.when ? state : other;
            holds.facts = new Set([...holds.facts, guard.name]);
        }
        return [
            [true, state],
            [false, other],
        ];
    }

    // ------------------------------------------------------------ expressions

    /** What `node` may evaluate to; an empty list when every path throws. `declarator`: the `var` it initialises. */
    #eval(node: Node, frame: number, state: State, declarator?: Node & { type: "VariableDeclarator" }): Values {
        this.#step(node);
        switch (node.type) {
            case "Literal":
                if (typeof node.value === "object" && node.value !== null) return refuse("a regular expression or bigint literal", node);
                return [prim(node.value as Value)];
            case "TemplateLiteral":
                if (node.expressions.length > 0) return refuse("a template with substitutions", node);
                return [prim(node.quasis[0]?.value.cooked ?? undefined)];
            case "ParenthesizedExpression":
                return this.#eval(node.expression, frame, state);
            case "Identifier":
                return this.#identifier(node, frame, state);
            case "ThisExpression":
                if (this.#setup) return [UNKNOWN];
                this.usesThis = true;
                return [ARG];
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return [{ k: "fn", node, env: frame }];
            case "ArrayExpression": {
                const props = new Map<string, Values>();
                for (const [i, element] of node.elements.entries()) {
                    if (element === null) continue;
                    if (element.type === "SpreadElement") return refuse("a spread in an array", element);
                    const values = this.#eval(element, frame, state);
                    if (values.length === 0) return [];
                    props.set(String(i), values);
                }
                const id = this.#nextId++;
                const holder = declarator?.id.type === "Identifier" ? this.#cx.scopes.variableOf(declarator.id) : undefined;
                state.heap.set(id, holder === undefined ? { kind: "array", props } : { kind: "array", props, holder });
                return [{ k: "obj", id }];
            }
            case "ObjectExpression": {
                const props = new Map<string, Values>();
                for (const property of node.properties) {
                    if (property.type !== "Property" || property.kind !== "init" || property.method || property.computed) return refuse("an object literal with more than plain keys", property);
                    const key = property.key.type === "Identifier" ? property.key.name : property.key.type === "Literal" ? String(property.key.value) : refuse("an object literal key", property);
                    const values = this.#eval(property.value, frame, state);
                    if (values.length === 0) return [];
                    props.set(key, values);
                }
                const id = this.#nextId++;
                state.heap.set(id, { kind: "object", props });
                return [{ k: "obj", id }];
            }
            case "SequenceExpression": {
                let values: Values = [];
                for (const expression of node.expressions) {
                    values = this.#eval(expression, frame, state);
                    if (values.length === 0) return [];
                }
                return values;
            }
            case "MemberExpression": {
                if (node.optional) return refuse("an optional chain", node);
                const objects = this.#eval(node.object, frame, state);
                const keys = this.#key(node, frame, state);
                return this.#member(objects, keys, node, state);
            }
            case "AssignmentExpression":
                return this.#assignment(node, frame, state);
            case "UpdateExpression": {
                const old = this.#eval(node.argument, frame, state);
                const values = this.#binary(node.operator === "++" ? "+" : "-", this.#unary("+", old, node), [prim(1)], node);
                if (values.length === 0) return [];
                this.#write(node.argument, values, frame, state);
                return node.prefix ? values : this.#unary("+", old, node);
            }
            case "UnaryExpression": {
                if (node.operator === "delete") return refuse("a delete", node);
                return this.#unary(node.operator, this.#eval(node.argument, frame, state), node);
            }
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier") return refuse("a private name", node);
                const guard = this.#guard(node, frame, state);
                if (guard !== undefined) return guard;
                const left = this.#eval(node.left, frame, state);
                const right = this.#eval(node.right, frame, state);
                return left.length === 0 || right.length === 0 ? [] : this.#binary(node.operator, left, right, node);
            }
            case "LogicalExpression": {
                if (node.operator === "??") return refuse("a ?? operator", node);
                const left = this.#eval(node.left, frame, state);
                const kept: AV[] = [];
                const goOn: AV[] = [];
                for (const value of left) {
                    const { truthy, falsy } = this.#truths([value]);
                    // `&&` goes on where the left side is truthy, `||` where it is falsy.
                    if (node.operator === "&&" ? falsy : truthy) kept.push(value);
                    if (node.operator === "&&" ? truthy : falsy) goOn.push(value);
                }
                if (goOn.length === 0) return kept;
                if (kept.length === 0) return this.#eval(node.right, frame, state);
                const other = state.clone();
                const right = this.#eval(node.right, frame, other);
                const joined = State.join(state, right.length === 0 ? undefined : other);
                if (joined !== undefined) state.set(joined);
                return union(kept, right);
            }
            case "ConditionalExpression": {
                const test = this.#eval(node.test, frame, state);
                let joined: State | undefined;
                let values: Values = [];
                for (const [taken, branchState] of this.#branches(test, state)) {
                    const result = this.#eval(taken ? node.consequent : node.alternate, frame, branchState);
                    if (result.length === 0) continue;
                    values = union(values, this.#underFacts(result, branchState));
                    joined = State.join(joined, branchState);
                }
                if (joined !== undefined) state.set(joined);
                return values;
            }
            case "CallExpression":
                return this.#callExpression(node, frame, state);
            default:
                return refuse(`a ${node.type}, which the evaluation doesn't follow`, node);
        }
    }

    #key(node: Node & { type: "MemberExpression" }, frame: number, state: State): Values {
        if (node.property.type === "PrivateIdentifier") return refuse("a private name", node);
        if (!node.computed) return [prim(node.property.type === "Identifier" ? node.property.name : "")];
        return this.#eval(node.property, frame, state);
    }

    /** `typeof host(name) == "undefined"` (`===`, `!=`, `!==` too, either side). */
    #guard(node: Node & { type: "BinaryExpression" }, frame: number, state: State): Values | undefined {
        const positive = node.operator === "==" || node.operator === "===";
        if (!positive && node.operator !== "!=" && node.operator !== "!==") return undefined;
        const [typeOf, other] = node.left.type === "UnaryExpression" && node.left.operator === "typeof" ? [node.left, node.right] : [node.right, node.left];
        if (typeOf.type !== "UnaryExpression" || typeOf.operator !== "typeof" || this.#setup) return undefined;
        const read = this.#eval(typeOf.argument, frame, state);
        if (read.length !== 1 || read[0]?.k !== "host") {
            const compared = this.#eval(other, frame, state);
            return this.#binary(node.operator, this.#unary("typeof", read, typeOf), compared, node);
        }
        const compared = this.#eval(other, frame, state);
        if (compared.length !== 1 || compared[0]?.k !== "prim" || compared[0].v !== "undefined") return refuse("a host global's type compared with something else", node);
        return [{ k: "guard", name: read[0].name, when: positive }];
    }

    #unary(operator: string, values: Values, node: Node): Values {
        let out: Values = [];
        for (const value of values) {
            let result: AV;
            if (value.k === "prim") {
                const evaluated = unary(operator, value.v);
                if (!evaluated.ok) return refuse(`the operator ${operator}`, node);
                result = prim(evaluated.value);
            } else if (operator === "void") result = UNDEFINED;
            else if (operator === "!" && value.k === "guard") result = { ...value, when: !value.when };
            else if (operator === "!" && (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage")) result = prim(false);
            else if (operator === "typeof" && (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage"))
                result = prim(value.k === "builtin" ? value.type : value.k === "obj" ? "object" : "function");
            else if ((value.k === "arg" || value.k === "args") && (!this.#mode.accessor || operator === "typeof" || operator === "!" || operator === "void")) result = ARG;
            else if (value.k === "unknown") result = UNKNOWN;
            else return refuse(`the operator ${operator} on ${value.k === "host" ? "a host global" : "a value it can't tell"}`, node);
            out = union(out, [result]);
        }
        return out;
    }

    #binary(operator: string, left: Values, right: Values, node: Node): Values {
        let out: Values = [];
        for (const l of left) {
            for (const r of right) {
                let result: AV;
                if (l.k === "prim" && r.k === "prim") {
                    const evaluated = binary(operator, l.v, r.v);
                    if (!evaluated.ok) return refuse(`the operator ${operator}`, node);
                    result = typeof evaluated.value === "string" && evaluated.value.length > MAX_STRING ? UNKNOWN : prim(evaluated.value);
                } else if (l.k === "arg" || r.k === "arg" || l.k === "args" || r.k === "args") {
                    // A conversion of a per-call object runs its code.
                    if (this.#mode.accessor && operator !== "===" && operator !== "!==") return refuse(`the operator ${operator} on its receiver or arguments`, node);
                    result = ARG;
                } else if (l.k === "unknown" || r.k === "unknown") result = UNKNOWN;
                else if (this.#setup && operator !== "===" && operator !== "!==" && (this.#added.accessors.has("valueOf") || this.#added.accessors.has("toString")))
                    return refuse(`the operator ${operator} converts an object, which may run a method the program added`, node);
                else if ((operator === "===" || operator === "!==") && l.k !== "host" && r.k !== "host" && l.k !== "guard" && r.k !== "guard") {
                    // Identity: equal values are one object; distinct objects the evaluation made differ, an object is no
                    // primitive. Two builtin paths or closures may still be one object: unknown.
                    const same = sameValue(l, r) ? true : l.k === "prim" || r.k === "prim" || (l.k === "obj" && r.k === "obj") ? false : undefined;
                    result = same === undefined ? (this.#setup ? UNKNOWN : ARG) : prim(operator === "===" ? same : !same);
                } else return refuse(`the operator ${operator} on objects or host globals`, node);
                out = union(out, [result]);
            }
        }
        return out;
    }

    #assignment(node: Node & { type: "AssignmentExpression" }, frame: number, state: State): Values {
        if (node.left.type !== "Identifier" && node.left.type !== "MemberExpression") return refuse("a destructuring assignment", node);
        let values: Values;
        if (node.operator === "=") values = this.#eval(node.right, frame, state);
        else if (node.operator === "+=") {
            const old = this.#eval(node.left, frame, state);
            const right = this.#eval(node.right, frame, state);
            values = old.length === 0 || right.length === 0 ? [] : this.#binary("+", old, right, node);
        } else return refuse(`the operator ${node.operator}`, node);
        if (values.length === 0) return [];
        this.#write(node.left, values, frame, state);
        return values;
    }

    // ------------------------------------------------------------ bindings

    /** The frame of function `fn` on `frame`'s lexical chain. */
    #frameOf(fn: Node, frame: number, state: State, node: Node): number {
        for (let id: number | undefined = frame; id !== undefined; id = state.heap.get(id)?.parent) if (state.heap.get(id)?.fn === fn) return id;
        return refuse("a binding of a function whose frame the evaluation didn't make", node);
    }

    #identifier(node: Node & { type: "Identifier" }, frame: number, state: State): Values {
        const { scopes } = this.#cx;
        const variable = scopes.staticVariableOf(node);
        if (variable === undefined) {
            if (scopes.globalReferences(node.name) === undefined) return refuse(`${node.name} may be a property of a with object`, node);
            if (node.name === "undefined") return [UNDEFINED];
            return this.#resolve([], node.name, node, state);
        }
        const block = variable.scope.block as unknown as Node;
        if (variable.scope.type === "global" || this.#cx.rootBlocks.has(block)) return this.#rootBinding(variable, node);
        if (variable.scope.type !== "function") return refuse(`${node.name} is a ${variable.scope.type} binding`, node);
        const id = this.#frameOf(block, frame, state, node);
        if (!this.#own(id) && !this.#fixedVariable(variable)) return refuse(`${node.name} is written by code that may run later`, node);
        return state.heap.get(id)?.props.get(node.name) ?? refuse(`${node.name} has no value in its frame`, node);
    }

    /**
     * The storage object; a root function declaration never written; anything else at the root may change later (or
     * hold anything already).
     */
    #rootBinding(variable: Variable, node: Node): Values {
        const declaration = variable.defs.length === 1 ? (variable.defs[0]?.node as unknown as Node | undefined) : undefined;
        if (declaration?.type === "FunctionDeclaration" && this.#cx.scopes.staticReferences(variable).every((reference) => !reference.isWrite())) {
            if (variable.name === this.#cx.storage) return this.#setup ? [{ k: "storage" }] : refuse("it reads the storage object", node);
            return [{ k: "fn", node: declaration, env: ROOT }];
        }
        return this.#unknown(`it reads ${variable.name}, a root binding other code may change`, node);
    }

    #writeVariable(node: Node & { type: "Identifier" }, values: Values, frame: number, state: State): void {
        const variable = this.#cx.scopes.staticVariableOf(node);
        if (variable === undefined || variable.scope.type !== "function" || this.#cx.rootBlocks.has(variable.scope.block as unknown as Node))
            return void refuse(`it writes ${node.name}, which isn't a function's own`, node);
        const id = this.#frameOf(variable.scope.block as unknown as Node, frame, state, node);
        if (!this.#own(id)) refuse(`it writes ${node.name}, which outlives the call`, node);
        if (!this.#setup && variable.defs.some((def) => def.type === "Parameter")) refuse(`it writes the parameter ${node.name}`, node);
        state.writable(id).props.set(node.name, values);
        this.#effectWrites(state, [[id, node.name]]);
    }

    #write(target: Node, values: Values, frame: number, state: State): void {
        if (target.type === "Identifier") return this.#writeVariable(target, values, frame, state);
        if (target.type !== "MemberExpression" || target.optional) return void refuse("a write to something other than a name or member", target);
        const objects = this.#eval(target.object, frame, state);
        const keys = this.#key(target, frame, state);
        const written: [number, string][] = [];
        for (const object of objects) {
            for (const key of keys) {
                if (key.k !== "prim" || typeof key.v === "symbol") return void refuse("a write under a key it can't tell", target);
                const name = String(key.v);
                if (object.k === "obj" && this.#own(object.id) && state.heap.get(object.id)?.kind !== "arguments" && state.heap.get(object.id)?.kind !== "frame") {
                    const writable = state.writable(object.id);
                    // A write through a choice of objects or keys may miss this one: it keeps its old value too.
                    writable.props.set(name, objects.length * keys.length === 1 ? values : union(writable.props.get(name) ?? [UNDEFINED], values));
                    written.push([object.id, name]);
                } else if (object.k === "builtin" && this.#setup) {
                    const owner = this.#cx.owners.findIndex((path) => samePath(path, object.path));
                    if (owner === -1 || this.#cx.before[owner]?.has(name) !== false) return void refuse(`it writes ${pathName(object.path)}.${name}`, target);
                    this.#unreached(name, state, target);
                    state.added = new Set([...state.added, name]);
                } else if (object.k === "builtin" && object.path.length === 0 && this.#mode.forwards === name && !this.#cx.before[0]?.has(name)) {
                    if (values.length !== 1 || values[0]?.k !== "arg" || values[0].index !== 0) return void refuse("the setter writes something other than its argument", target);
                    if (state.hostWrites !== -1) state.hostWrites++;
                } else if (object.k === "prim" && (object.v === undefined || object.v === null)) continue;
                else return void refuse(object.k === "obj" ? "it writes an object that outlives the call" : "it writes a property of something other than its own objects", target);
            }
        }
        this.#effectWrites(state, written);
    }

    // ------------------------------------------------------------ properties

    #member(objects: Values, keys: Values, node: Node, state: State): Values {
        let out: Values = [];
        for (const object of objects) {
            for (const key of keys) {
                if (key.k === "arg" || key.k === "args") {
                    if (object.k !== "arg" && object.k !== "args") return refuse("a per-call key on a value that outlives the call", node);
                    out = union(out, [ARG]);
                    continue;
                }
                if (key.k !== "prim") {
                    out = union(out, this.#unknown("a key it can't tell", node));
                    continue;
                }
                out = union(out, this.#property(object, String(key.v), node, state));
            }
        }
        return out;
    }

    #property(object: AV, key: string, node: Node, state: State): Values {
        switch (object.k) {
            case "prim":
                if (object.v === undefined || object.v === null) return [];
                if (typeof object.v === "string" && key === "length") return [prim(object.v.length)];
                if (typeof object.v === "string" && isIndexKey(key)) return [prim(object.v[Number(key)])];
                if (this.#setup) this.#unreached(key, state, node);
                return this.#unknown("a property of a primitive", node);
            case "builtin":
                return this.#resolve(object.path, key, node, state);
            case "obj":
                return this.#objectProperty(object.id, key, node, state);
            case "arg":
                return this.#mode.accessor ? refuse("it reads a property of its receiver or arguments", node) : [ARG];
            case "args":
                if (key === "length") return this.#mode.zero ? [prim(0)] : [ARG];
                if (isIndexKey(key)) return this.#mode.zero ? [UNDEFINED] : [{ k: "arg", index: Number(key) }];
                return [ARG];
            default:
                // In the setup too: a getter there may be one it installed, answering from frames still running.
                return refuse(
                    `it reads a property of ${object.k === "host" ? "a host global" : object.k === "storage" ? "the storage object" : object.k === "unknown" ? "a value it can't tell" : "a function"}`,
                    node
                );
        }
    }

    #objectProperty(id: number, key: string, node: Node, state: State): Values {
        const object = state.heap.get(id);
        if (object === undefined) return refuse("an object the evaluation lost", node);
        if (!this.#own(id)) {
            if (object.kind === "array" && object.holder !== undefined && !this.#fixedSlots(object.holder))
                return refuse(`${object.holder.name} is handed on, or its slots are written by code that may run later`, node);
            if (object.kind === "array" && object.holder === undefined) return refuse("it reads an array the setup made that no local holds for itself", node);
            if (object.kind === "arguments" && (object.frame === undefined || !this.#fixedArgumentsOf(state.heap.get(object.frame)?.fn)))
                return refuse("it reads an arguments object other code may get hold of", node);
            if (object.kind !== "array" && object.kind !== "arguments") return refuse("it reads an object the setup made that other code may change", node);
        }
        if (object.kind === "arguments") {
            if (key === "length") return [prim(object.argc ?? 0)];
            if (!isIndexKey(key)) {
                if (this.#setup) this.#unreached(key, state, node);
                return this.#unknown("a property of an arguments object", node);
            }
            const index = Number(key);
            if (index >= (object.argc ?? 0)) return [UNDEFINED];
            const param = object.params?.[index];
            if (param === undefined) return object.props.get(key) ?? [UNDEFINED];
            const frame = object.frame === undefined ? undefined : state.heap.get(object.frame);
            const fn = frame?.fn;
            if (fn === undefined || !this.#paramUnwritten(fn, index)) return refuse("an argument whose parameter is written", node);
            return frame?.props.get(param) ?? refuse("a parameter with no value", node);
        }
        if (object.kind === "frame") return refuse("a frame read as an object", node);
        const known = object.props.get(key);
        if (known !== undefined) return known;
        // Model 7: Array.prototype and Object.prototype have no index properties.
        if (this.#setup && isIndexKey(key)) return this.#missing(key, state, node);
        if (this.#setup) this.#unreached(key, state, node);
        return isIndexKey(key) ? [UNDEFINED] : this.#unknown(`${key} of an object the evaluation made`, node);
    }

    /** Phase "setup": a lookup of `key` that misses the objects it knows reaches builtins; no accessor of the program's may be there. */
    #unreached(key: string, state: State, node: Node): void {
        if (this.#added.accessors.has(key) || state.added.has(key)) refuse(`it may reach ${key}, which the program added to a builtin (an accessor would run before the setup finishes)`, node);
    }

    /** Phase "setup": what a lookup reaching builtins gives for a key they didn't have (`#unreached` first). */
    #missing(key: string, state: State, node: Node): Values {
        this.#unreached(key, state, node);
        return this.#added.names.has(key) ? [UNKNOWN] : [UNDEFINED];
    }

    /**
     * `path.key` on a builtin, as the guest finds it: a builtin or primitive where the holder had the key before the
     * program ran; absent stays absent (model 7). On the global object, any other key is a global the program or the
     * host may set at any time: a live read (phase "call"). In phase "setup" the guest's answer is from after the
     * setup: a key the program hadn't added yet (`#unreached`) was absent then, or a host global.
     */
    #resolve(path: PropertyPath, key: string, node: Node, state: State): Values {
        const { owners, before, lookups } = this.#cx;
        const cacheKey = JSON.stringify([path, key]);
        let found = lookups.get(cacheKey);
        if (!lookups.has(cacheKey)) {
            found = this.#cx.guest.lookup(path, key);
            lookups.set(cacheKey, found);
        }
        const original = (found?.kind === "data" || found?.kind === "accessor") && found.holder >= 0 && before[found.holder]?.has(key) === true;
        if (!original) {
            if (this.#setup) {
                const value = this.#missing(key, state, node);
                return path.length === 0 || found === undefined || found.kind === "base" ? [UNKNOWN] : value;
            }
            if (path.length === 0) {
                this.hostReads.add(key);
                return [this.#mode.opaqueGlobals ? ARG : { k: "host", name: key }];
            }
            if (found?.kind === "absent") return [UNDEFINED];
            return refuse(`${pathName(path)}.${key} isn't a builtin's own`, node);
        }
        if (found?.kind !== "data") return this.#unknown(`${pathName(path)}.${key} is an accessor`, node);
        if (found.owner >= 0) return [{ k: "builtin", path: owners[found.owner] ?? refuse("an owner the guest doesn't list", node), type: found.type }];
        if (found.type === "object" || found.type === "function") return [{ k: "builtin", path: [...(owners[found.holder] ?? []), key], type: found.type }];
        if (found.type === "symbol" || found.type === "bigint") return this.#unknown(`${pathName(path)}.${key} is a ${found.type}`, node);
        return [prim(found.value)];
    }

    // ------------------------------------------------------------ calls

    #callExpression(node: Node & { type: "CallExpression" }, frame: number, state: State): Values {
        if (node.optional) return refuse("an optional call", node);
        let self: Values = [UNDEFINED];
        let callees: Values;
        const callee = node.callee;
        if (callee.type === "MemberExpression") {
            if (callee.optional) return refuse("an optional chain", callee);
            self = this.#eval(callee.object, frame, state);
            callees = this.#member(self, this.#key(callee, frame, state), callee, state);
        } else callees = this.#eval(callee, frame, state);
        if (callees.length === 0) return [];
        let spread = false;
        const args: Values[] = [];
        for (const arg of node.arguments) {
            if (arg.type === "SpreadElement") {
                if (this.#setup) return refuse("a spread argument", arg);
                const spreadValues = this.#eval(arg.argument, frame, state);
                this.#handOn(spreadValues, arg);
                spread = true;
                continue;
            }
            const values = this.#eval(arg, frame, state);
            if (values.length === 0) return [];
            args.push(values);
        }
        return this.#apply(callees, self, spread ? undefined : args, node, state);
    }

    /** Values a call hands to code the evaluation doesn't follow: per call, the call's own objects, builtins, primitives. */
    #handOn(values: Values, node: Node): void {
        for (const value of values) {
            if (value.k === "fn") refuse("it hands a function of the program to code it doesn't follow", node);
            if (value.k === "obj" && (this.#setup || !this.#own(value.id))) refuse("it hands an object the setup made to code it doesn't follow", node);
            if (value.k === "host" || value.k === "guard" || value.k === "unknown" || value.k === "storage") refuse("it hands a value it can't tell to code it doesn't follow", node);
            if ((value.k === "arg" || value.k === "args") && this.#mode.accessor) refuse("it hands its receiver or arguments to code it doesn't follow", node);
        }
    }

    /** `args` undefined: a list known only per call (a spread, `apply` with `arguments`). */
    #apply(callees: Values, self: Values, args: readonly Values[] | undefined, node: Node, state: State): Values {
        let out: Values = [];
        for (const callee of callees) {
            if (callee.k === "prim") continue; // Not callable: this path throws.
            if (callee.k === "fn") {
                if (!this.#setup && (this.#mode.root === undefined || !isWithin(callee.node, this.#mode.root))) return refuse("it calls a function defined elsewhere", node);
                if (args === undefined) return refuse("a call of a program function with arguments it can't tell", node);
                const branch = callees.length === 1 ? state : state.clone();
                out = union(out, this.#invoke(callee, args, branch));
                if (branch !== state) state.set(State.join(state, branch) as State);
                continue;
            }
            if (callee.k === "builtin" && (samePath(callee.path, FUNCTION_CALL) || samePath(callee.path, FUNCTION_APPLY))) {
                // `f.call(t, ...a)` / `f.apply(t, a)` (model 7: these are the builtins): a call of `f`.
                const [thisArg = [UNDEFINED], list] = args ?? [];
                let rest: readonly Values[] | undefined;
                if (args === undefined) rest = undefined;
                else if (samePath(callee.path, FUNCTION_CALL)) rest = args.slice(1);
                else if (list === undefined || list.every((value) => value.k === "prim" && (value.v === undefined || value.v === null))) rest = [];
                else {
                    this.#handOn(list, node);
                    rest = undefined;
                }
                out = union(out, this.#apply(self, thisArg, rest, node, state));
                continue;
            }
            if (callee.k === "builtin" && samePath(callee.path, DEFINE_PROPERTY) && this.#setup) {
                out = union(out, this.#defineProperty(args, node, state));
                continue;
            }
            if (callee.k === "builtin" && this.#setup && !samePath(callee.path, HAS_OWN_PROPERTY))
                return refuse(`it calls ${pathName(callee.path)}, which the evaluation doesn't model (it may run program code)`, node);
            if (callee.k === "builtin" || (callee.k === "arg" && !this.#setup && !this.#mode.accessor)) {
                // A builtin (model 7) or a per-call function: what it does is the alias's meaning, not the getter's state.
                this.#handOn(self, node);
                for (const values of args ?? []) this.#handOn(values, node);
                out = union(out, this.#setup ? [UNKNOWN] : [ARG]);
                continue;
            }
            return refuse("it calls a value it can't tell", node);
        }
        return out;
    }

    #defineProperty(args: readonly Values[] | undefined, node: Node, state: State): Values {
        const [targets = [UNDEFINED], keys = [UNDEFINED], descriptors = [UNDEFINED]] = args ?? refuse("defineProperty with arguments it can't tell", node);
        let getters: Values = [];
        let setters: Values = [];
        // The descriptor's fields are looked up on it, then on Object.prototype.
        for (const field of ["get", "set", "value", "writable", "enumerable", "configurable"]) this.#unreached(field, state, node);
        for (const descriptor of descriptors) {
            const object = descriptor.k === "obj" ? state.heap.get(descriptor.id) : undefined;
            if (object?.kind !== "object") return refuse("defineProperty with a descriptor it can't tell", node);
            getters = union(getters, object.props.get("get") ?? [UNDEFINED]);
            setters = union(setters, object.props.get("set") ?? [UNDEFINED]);
        }
        const added = new Set(state.added);
        for (const target of targets) {
            if (target.k === "storage") continue;
            if (target.k !== "builtin") return refuse("defineProperty on something other than a builtin or the storage object", node);
            for (const key of keys) {
                if (key.k !== "prim") return refuse("defineProperty under a key it can't tell", node);
                added.add(String(key.v));
            }
        }
        state.added = added;
        this.installations.push({ targets, keys, getters, setters });
        return targets;
    }

    // ------------------------------------------------------------ what stays as the setup left it

    /** Written only by its own function's body (which finished before any later call): it keeps its last value. */
    #fixedVariable(variable: Variable): boolean {
        let fixed = this.#fixedVariables.get(variable);
        if (fixed === undefined) {
            const block = variable.scope.block as unknown as FunctionLike;
            const references = this.#cx.scopes.references(variable);
            fixed =
                !block.async &&
                !(block.type !== "ArrowFunctionExpression" && block.generator) &&
                references !== undefined &&
                references.every((reference) => !reference.isWrite() || reference.from.variableScope.block === variable.scope.block);
            this.#fixedVariables.set(variable, fixed);
        }
        return fixed;
    }

    /**
     * A local array never handed on (every use `S[index]`, not as a callee's object, which would pass it as `this`),
     * assigned only by its declaration, its slots written only by its own function's body.
     */
    #fixedSlots(variable: Variable): boolean {
        let fixed = this.#slotsMemo.get(variable);
        if (fixed === undefined) {
            const references = this.#cx.scopes.references(variable);
            const block = variable.scope.block as unknown as Node;
            fixed =
                this.#fixedVariable(variable) &&
                references !== undefined &&
                references.every((reference) => {
                    if (reference.isWrite()) return reference.init === true;
                    const identifier = reference.identifier as unknown as Node;
                    const member = this.#parentOf(identifier, block);
                    if (member?.type !== "MemberExpression" || member.object !== identifier || !isIndexKey(propertyKey(member) ?? "")) return false;
                    const use = this.#parentOf(member, block);
                    if (use?.type === "CallExpression" && use.callee === member) return false;
                    return !isWritten(member, use) || reference.from.variableScope.block === variable.scope.block;
                });
            this.#slotsMemo.set(variable, fixed);
        }
        return fixed;
    }

    /** A node's parent, from a walk of `block` only (a variable's references are all inside its scope's block). */
    #parentOf(node: Node, block: Node): Node | undefined {
        let parents = this.#parents.get(block);
        if (parents === undefined) {
            parents = parentsWithin(block);
            this.#parents.set(block, parents);
        }
        return parents.get(node);
    }

    /**
     * `fn`'s `arguments` used only as `var S = [arguments]`, `S` a fixed local array whose element is only read by
     * index (`S[j][i]`, never written, never a callee's object): no code gets hold of the object to change it.
     */
    #fixedArgumentsOf(fn: Node | undefined): boolean {
        if (fn === undefined) return false;
        let fixed = this.#fixedArguments.get(fn);
        if (fixed === undefined) {
            fixed = this.#argumentsKeptToItself(fn);
            this.#fixedArguments.set(fn, fixed);
        }
        return fixed;
    }

    #argumentsKeptToItself(fn: Node): boolean {
        const { scopes } = this.#cx;
        const variable = scopes.scopeOf(fn)?.set.get("arguments");
        const references = variable === undefined ? undefined : scopes.references(variable);
        if (references === undefined) return false;
        return references.every((reference) => {
            const identifier = reference.identifier as unknown as Node;
            const array = this.#parentOf(identifier, fn);
            const declarator = array === undefined ? undefined : this.#parentOf(array, fn);
            if (array?.type !== "ArrayExpression" || declarator?.type !== "VariableDeclarator" || declarator.init !== array || declarator.id.type !== "Identifier") return false;
            const slots = scopes.variableOf(declarator.id);
            const index = String(array.elements.indexOf(identifier as never));
            const slotReferences = slots === undefined ? undefined : scopes.references(slots);
            if (slots === undefined || slotReferences === undefined || !this.#fixedSlots(slots)) return false;
            return slotReferences.every((slotReference) => {
                if (slotReference.init === true) return true;
                const element = this.#parentOf(slotReference.identifier as unknown as Node, fn);
                if (element?.type !== "MemberExpression" || propertyKey(element) !== index) return true;
                const read = this.#parentOf(element, fn);
                if (read?.type !== "MemberExpression" || read.object !== element || !isIndexKey(propertyKey(read) ?? "")) return false;
                const use = this.#parentOf(read, fn);
                return !isWritten(read, use) && !(use?.type === "CallExpression" && use.callee === read);
            });
        });
    }

    /** No write to parameter `index` of `fn` (so `arguments[index]` keeps the value passed). */
    #paramUnwritten(fn: FunctionLike, index: number): boolean {
        const param = fn.params[index];
        if (param?.type !== "Identifier") return false;
        const variable = this.#cx.scopes.variableOf(param);
        const references = variable === undefined ? undefined : this.#cx.scopes.references(variable);
        return references !== undefined && references.every((reference) => !reference.isWrite());
    }
}

const isWritten = (member: Node, use: Node | undefined): boolean =>
    (use?.type === "AssignmentExpression" && use.left === member) || (use?.type === "UpdateExpression" && use.argument === member) || (use?.type === "UnaryExpression" && use.operator === "delete");

// ------------------------------------------------------------ the proofs

/** Where the statement that installed an accessor left it, as the guest saw right after it ran. */
export interface Installed {
    readonly statement: Statement;
    readonly accessor: AccessorFunctions;
}

/** What the program added to builtins before a setup call: names (on any owner), and those that are accessors. */
export interface AddedNames {
    readonly names: ReadonlySet<string>;
    readonly accessors: ReadonlySet<string>;
}

export interface ProofContext extends Omit<EvaluatorContext, "lookups"> {
    /** What the guest ran, by file index (`program-<index>.js`): each statement as printed, with its functions' starts. */
    readonly files: readonly PrintedFunctions[];
    /** Arguments of root calls that held the global object right before their statement ran. */
    readonly globalArgs: ReadonlySet<Node>;
    /** Per setup call: what the program had added to builtins before it. */
    readonly added: ReadonlyMap<Statement, AddedNames>;
}

/** What a getter must be: see `GetterProofs`. */
type Claim =
    { readonly kind: "fixed" } | { readonly kind: "calls" } | { readonly kind: "forwards"; readonly name: string } | { readonly kind: "reads"; readonly name: string } | { readonly kind: "thisFree" };

/** The accessor at a place as the statements left it: `null` none, `undefined` the guest didn't tell. */
export type Current = AccessorFunctions | null | undefined;

/** Why an accessor's getter can't stand for what the probes saw, or `undefined` when it provably does. */
export type ProofFailure = { readonly reason: string; readonly node: Node | undefined } | undefined;

/** The proofs for one emulation: each setup statement is evaluated once. */
export class GetterProofs {
    readonly #cx: ProofContext & Pick<EvaluatorContext, "lookups">;
    readonly #setups = new Map<Statement, { evaluator: Evaluator; state: State } | Refusal>();

    constructor(cx: ProofContext) {
        this.#cx = { ...cx, lookups: new Map() };
    }

    /** An owner alias: every later read of `owner.alias` gives the value the probe saw. */
    alias(owner: PropertyPath, alias: string, installed: Installed | undefined, now: Current): ProofFailure {
        return this.#prove(owner, alias, installed, now, { kind: "fixed" });
    }

    /** A call alias on the storage object: the getter hands out the same function (or value), calls of which keep no state. */
    callAlias(key: string, installed: Installed | undefined, now: Current): ProofFailure {
        return this.#prove(null, key, installed, now, { kind: "calls" });
    }

    /** A global accessor forwarding the global `name`: the getter reads it and the setter writes it, every time. */
    hostAlias(alias: string, name: string, installed: Installed | undefined, now: Current): ProofFailure {
        return this.#prove([], alias, installed, now, { kind: "forwards", name });
    }

    /** `G.key()`: the getter hands out a function whose call with no arguments reads the global `name`, and does nothing else. */
    globalRead(key: string, name: string, installed: Installed | undefined, now: Current): ProofFailure {
        return this.#prove(null, key, installed, now, { kind: "reads", name });
    }

    /**
     * `G.key(...)` never uses its `this` (`G`): the getter, which runs with it, doesn't read `this`, and hands out only
     * functions whose calls don't (a builtin would run with `G` as `this`), or primitives (whose call throws first).
     */
    thisFree(key: string, installed: Installed | undefined, now: Current): ProofFailure {
        return this.#prove(null, key, installed, now, { kind: "thisFree" });
    }

    #prove(path: PropertyPath | null, key: string, installed: Installed | undefined, now: Current, claim: Claim): ProofFailure {
        const where = `${path === null ? this.#cx.storage : pathName(path)}.${key}`;
        if (installed === undefined) return { reason: `no setup call installed the accessor ${where}`, node: undefined };
        const getter = now?.get;
        if (now === null || now === undefined || getter === undefined) return { reason: `${where} is no accessor with a getter now`, node: installed.statement };
        if (getter.id !== installed.accessor.get?.id || (claim.kind === "forwards" && now.set?.id !== installed.accessor.set?.id))
            return { reason: `${where} was redefined after the setup call that installed it`, node: installed.statement };
        const getterNode = this.#locate(getter.site);
        if (typeof getterNode === "string") return { reason: `its getter's code: ${getterNode}`, node: installed.statement };
        const setterNode = claim.kind === "forwards" ? this.#locate(now.set?.site) : undefined;
        if (typeof setterNode === "string") return { reason: `its setter's code: ${setterNode}`, node: installed.statement };
        const setup = this.#setup(installed.statement);
        if (setup instanceof Refusal) return { reason: `the setup call can't be evaluated: ${setup.reason}`, node: setup.node ?? installed.statement };
        const { evaluator, state } = setup;
        const candidates = this.#installed(evaluator, path, key);
        if (candidates.length === 0) return { reason: `the setup call's evaluation installs no accessor at ${where}`, node: getterNode };
        for (const { getter: getterValue, setter } of candidates) {
            if (getterValue.k !== "fn" || getterValue.node !== getterNode) return { reason: "the setup call may install another getter there", node: getterNode };
            if (claim.kind === "forwards" && (setter.k !== "fn" || setter.node !== setterNode)) return { reason: "the setup call may install another setter there", node: getterNode };
            const failure = this.#check(evaluator, state, getterValue, setter, claim);
            if (failure !== undefined) return failure;
        }
        return undefined;
    }

    /** The getter's calls, then (for `calls` and `reads`) the calls of each function it hands out. */
    #check(evaluator: Evaluator, after: State, getter: AV, setter: AV, claim: Claim): ProofFailure {
        const got = evaluator.call(getter, after, { zero: true, accessor: true });
        if (got instanceof Refusal) return { reason: `its getter: ${got.reason}`, node: got.node };
        const reads = [...evaluator.hostReads];
        switch (claim.kind) {
            case "fixed":
                if (reads.length > 0) return { reason: `its getter reads globalThis.${reads[0]}, which may change`, node: undefined };
                if (got.values.some((value) => value.k !== "prim" && value.k !== "builtin")) return { reason: "its getter may hand out a value that changes", node: undefined };
                return undefined;
            case "forwards": {
                if (reads.some((name) => name !== claim.name)) return { reason: `its getter reads another global, globalThis.${reads.find((name) => name !== claim.name)}`, node: undefined };
                if (!got.values.every((value) => value.k === "host" && value.name === claim.name))
                    return { reason: `its getter may hand out something other than globalThis.${claim.name}`, node: undefined };
                const set = evaluator.call(setter, after, { zero: false, accessor: true, forwards: claim.name });
                if (set instanceof Refusal) return { reason: `its setter: ${set.reason}`, node: set.node };
                if (evaluator.hostReads.size > 0) return { reason: "its setter reads a global", node: undefined };
                if (set.state.hostWrites !== 1) return { reason: `its setter may not write globalThis.${claim.name} exactly once`, node: undefined };
                return undefined;
            }
            case "calls":
            case "reads": {
                if (reads.length > 0) return { reason: `its getter reads globalThis.${reads[0]}, which may change`, node: undefined };
                for (const value of got.values) {
                    if (value.k === "prim" || value.k === "builtin") continue;
                    if (value.k !== "fn") return { reason: "its getter may hand out a value that changes", node: undefined };
                    // `G.key(...)` passes its arguments on (the alias's meaning); `G.key()` must only read the global.
                    const called = evaluator.call(value, got.state, { zero: claim.kind === "reads", accessor: claim.kind === "reads" });
                    if (called instanceof Refusal) return { reason: `the function its getter hands out: ${called.reason}`, node: called.node };
                    const calledReads = [...evaluator.hostReads];
                    if (claim.kind === "calls" && calledReads.length > 0) return { reason: `the function its getter hands out reads globalThis.${calledReads[0]}, which may change`, node: undefined };
                    if (claim.kind === "reads" && (calledReads.some((name) => name !== claim.name) || !called.values.every((v) => v.k === "host" && v.name === claim.name)))
                        return { reason: `the function its getter hands out may do more than read globalThis.${claim.name}`, node: undefined };
                }
                if (claim.kind === "reads" && !got.values.some((value) => value.k === "fn")) return { reason: "its getter hands out no function", node: undefined };
                return undefined;
            }
            case "thisFree": {
                if (evaluator.usesThis) return { reason: "its getter reads this", node: undefined };
                for (const value of got.values) {
                    if (value.k === "prim") continue;
                    if (value.k !== "fn") return { reason: "its getter may hand out a function that runs with this", node: undefined };
                    const called = evaluator.call(value, got.state, { zero: false, accessor: false, opaqueGlobals: true });
                    if (called instanceof Refusal) return { reason: `the function its getter hands out: ${called.reason}`, node: called.node };
                    if (evaluator.usesThis) return { reason: "the function its getter hands out reads this", node: undefined };
                }
                return undefined;
            }
        }
    }

    /** The getters (and setters) the setup's `defineProperty` calls may install at `path.key` (`null`: the storage object). */
    #installed(evaluator: Evaluator, path: PropertyPath | null, key: string): { getter: AV; setter: AV }[] {
        const found: { getter: AV; setter: AV }[] = [];
        for (const installation of evaluator.installations) {
            const targets = installation.targets.filter((target) => target.k === "unknown" || (path === null ? target.k === "storage" : target.k === "builtin" && samePath(target.path, path)));
            const keys = installation.keys.filter((k) => k.k === "unknown" || (k.k === "prim" && String(k.v) === key));
            if (targets.length === 0 || keys.length === 0) continue;
            for (const getter of installation.getters) for (const setter of installation.setters) found.push({ getter, setter });
        }
        return found;
    }

    #setup(statement: Statement): { evaluator: Evaluator; state: State } | Refusal {
        let known = this.#setups.get(statement);
        if (known === undefined) {
            const evaluator = new Evaluator(this.#cx);
            const added = this.#cx.added.get(statement);
            const state = added === undefined ? new Refusal("what the program added to builtins before it isn't known", statement) : evaluator.runSetup(statement, this.#cx.globalArgs, added);
            known = state instanceof Refusal ? state : { evaluator, state };
            this.#setups.set(statement, known);
        }
        return known;
    }

    /** The function node starting where the guest says, in the printed statement its run's file ran; or why not. */
    #locate(site: FunctionSite | undefined): Node | string {
        if (site === undefined) return "it isn't a function the program's source made";
        const match = /^program-(\d+)\.js$/.exec(site.file);
        const printed = match === null ? undefined : this.#cx.files[Number(match[1])];
        if (printed === undefined) return `it comes from ${site.file}, no statement the emulation ran`;
        const offset = offsetOf(printed.source, site.line, site.column);
        const node = offset === undefined ? undefined : printed.functions.get(offset);
        return node ?? `no function starts at line ${site.line}, column ${site.column} of its statement`;
    }
}

/** QuickJS's line (1-based, lines end at `\n`) and column (1-based, in code points) as a UTF-16 offset in `source`. */
const offsetOf = (source: string, line: number, column: number): number | undefined => {
    // Other line terminators would count as line ends for some engines and not others.
    if (/[\r\u2028\u2029]/.test(source)) return undefined;
    let offset = 0;
    for (let l = 1; l < line; l++) {
        const end = source.indexOf("\n", offset);
        if (end === -1) return undefined;
        offset = end + 1;
    }
    for (let c = 1; c < column; c++) {
        const code = source.codePointAt(offset);
        if (code === undefined || code === 0x0a) return undefined;
        offset += code > 0xffff ? 2 : 1;
    }
    return offset;
};
