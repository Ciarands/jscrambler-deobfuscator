import type { CallExpression, Function as FunctionNode, FunctionLike, Node, Statement } from "../../core/ast.js";
import { isIndexKey, propertyKey } from "../../core/ast.js";
import { binary, unary } from "../../core/evaluate.js";
import type { Value } from "../../core/evaluate.js";
import { hoistedDeclarations } from "../../core/hoisting.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { parentsWithin } from "./builders.js";
import type { PropertyPath, Alias, CallAlias, CallStyle } from "./model.js";
import { pathName } from "./model.js";
import type { Realm } from "./realm.js";

/**
 * The setup calls, evaluated without running them (user decision 2026-11-02: a static proof, or no fact): what they add
 * to builtins and install on the storage object, and what each such property stands for.
 *
 * 1. A setup statement (`f(args)`, `f` a root function or a function expression) is evaluated abstractly (`Evaluator`,
 *    phase "setup"): its frames, their variables and local arrays, and the properties its writes to builtins and its
 *    `Object.defineProperty` calls may leave (`Descriptor`s, with the closures their accessors are). A value is a
 *    primitive, a builtin (a path from the global object through properties the builtins have before the program runs,
 *    found by reflection on the host's own: `realm.ts`, model 7), the storage object, a closure, an object the
 *    evaluation made, or unknown; sets of them where paths join. A `try`'s catch block starts from the states at the
 *    points where something may throw. No accessor the program added may run before the statement finishes (it may be
 *    one the statement installed, answering from frames still running): the evaluation refuses any lookup that may
 *    reach one. The setups run in root order, each from where the last left the builtins.
 * 2. The properties the setups leave are then called (phase "call"): a getter (a setter, the function a storage getter
 *    hands out) may write only what its own call makes, and read only its own values, its arguments and `this` (per
 *    call), builtins (model 7: builtins intact; the program adds nothing to them but what the setups add, which this
 *    follows), and what enclosing frames left behind where nothing but their own body writes it (they finished before
 *    the getter could run; locals and local arrays never handed on). A global the builtins lack is a live read
 *    (`host`). The same calls tell whether `G.key(...)` uses `G` (its `this`) at all.
 * 3. What each property stands for (`SetupAnalysis`): an alias (reads as one builtin property every time), a host
 *    alias (forwards a host global, model 10), a call alias (hands out a function calling a builtin in one
 *    `CallStyle`), a global read (`G.key()` is a host global), or nothing known.
 *
 * Model 7 as this reads it: the builtins are the host's, and the program adds to them only through the setup calls the
 * evaluation follows; a root call it can't follow adds nothing. Globals a setup adds weren't there before the program
 * ran: no other script made them (model 2), and they are jscrambler's own names (model 9).
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
    /** Phase "call": a value the call's arguments or `this` give (another each call); `index` for `arguments[index]`, `present` when not `null` or `undefined`. */
    | { readonly k: "arg"; readonly index?: number; readonly present?: true }
    /** Phase "call": the analysed call's `arguments`, from `from` on (`Array.prototype.slice.call(arguments, from)`). */
    | { readonly k: "args"; readonly from: number; readonly array?: true }
    /** Phase "call": `arguments.length` of a call with at least one argument. */
    | { readonly k: "argc" }
    /** Phase "call": `arguments[index][key]`. */
    | { readonly k: "method"; readonly index: number; readonly key: string }
    /** Phase "call": what the analysed call's `call`-th call of code outside the program (`Evaluator.calls`) returned. */
    | { readonly k: "result"; readonly call: number }
    /** Phase "call": the global property `name` the builtins lack, as read now (it may change). */
    | { readonly k: "host"; readonly name: string }
    /** Phase "call": `typeof host(name) == "undefined"` (`when` true), or its negation. */
    | { readonly k: "guard"; readonly name: string; readonly when: boolean }
    | { readonly k: "unknown" };

type Values = readonly AV[];

/** Per call: whatever its arguments and `this` give. */
type PerCall = AV & { readonly k: "arg" | "args" | "argc" | "method" | "result" };

const UNKNOWN: AV = { k: "unknown" };
const ARG: AV = { k: "arg" };
const ARGC: AV = { k: "argc" };
const UNDEFINED: AV = { k: "prim", v: undefined };
const prim = (v: Value): AV => ({ k: "prim", v });
const BOOLEAN: Values = [prim(true), prim(false)];

const MAX_VALUES = 8;
const MAX_STEPS = 2_000_000;
const MAX_DEPTH = 64;
const MAX_STRING = 1 << 16;
/** The frame of the program's top level (or its lone IIFE): its bindings are resolved by `#rootBinding`. */
const ROOT = 0;

const FUNCTION_CALL: PropertyPath = ["Function", "prototype", "call"];
const FUNCTION_APPLY: PropertyPath = ["Function", "prototype", "apply"];
const ARRAY_SLICE: PropertyPath = ["Array", "prototype", "slice"];
const DEFINE_PROPERTY: PropertyPath = ["Object", "defineProperty"];
/** The only other builtin the setup phase calls: it reads no property, so it runs no program code. */
const HAS_OWN_PROPERTY: PropertyPath = ["Object", "prototype", "hasOwnProperty"];
/** A function's own properties `Object.defineProperty` can't redefine (the storage object may be one). */
const FIXED_FUNCTION_PROPERTIES: ReadonlySet<string> = new Set(["prototype", "arguments", "caller"]);

const samePath = (a: PropertyPath, b: PropertyPath): boolean => a.length === b.length && a.every((key, i) => key === b[i]);

const isPerCall = (value: AV): value is PerCall => value.k === "arg" || value.k === "args" || value.k === "argc" || value.k === "method" || value.k === "result";

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
            return b.k === "arg" && a.index === b.index && a.present === b.present;
        case "args":
            return b.k === "args" && a.from === b.from && a.array === b.array;
        case "method":
            return b.k === "method" && a.index === b.index && a.key === b.key;
        case "result":
            return b.k === "result" && a.call === b.call;
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

const sameValues = (a: Values, b: Values): boolean => a.length === b.length && a.every((value) => b.some((other) => sameValue(value, other)));

/**
 * What a property the setups may add or define is: not there (as before the program ran), a data property, or an
 * accessor. `configurable` and `writable` are `undefined` where paths disagree; `writable` also where a definition
 * leaves it out on a property that may be there already (which keeps its own).
 */
type Descriptor =
    | { readonly kind: "absent" }
    | { readonly kind: "data"; readonly values: Values; readonly configurable: boolean | undefined; readonly writable: boolean | undefined }
    | { readonly kind: "accessor"; readonly get: Values; readonly set: Values; readonly configurable: boolean | undefined };

type Descriptors = readonly Descriptor[];

const ABSENT: Descriptor = { kind: "absent" };

const sameDescriptor = (a: Descriptor, b: Descriptor): boolean => {
    if (a.kind === "absent" || b.kind === "absent") return a.kind === b.kind;
    if (a.kind === "data") return b.kind === "data" && a.configurable === b.configurable && a.writable === b.writable && sameValues(a.values, b.values);
    return b.kind === "accessor" && a.configurable === b.configurable && sameValues(a.get, b.get) && sameValues(a.set, b.set);
};

const unionDescriptors = (a: Descriptors, b: Descriptors): Descriptors => {
    const out = [...a];
    for (const descriptor of b) if (!out.some((known) => sameDescriptor(known, descriptor))) out.push(descriptor);
    return out;
};

/** For log lines: what the property may be. */
const described = (descriptors: Descriptors): string => {
    const kinds = descriptors.map((descriptor) => {
        if (descriptor.kind !== "data") return descriptor.kind === "absent" ? "nothing" : "an accessor";
        return descriptor.writable === undefined ? "a data property" : `a ${descriptor.writable ? "writable" : "read-only"} data property`;
    });
    return [...new Set(kinds)].join(" or ");
};

/** What a function inherits from (the storage object is a root function declaration). */
const INHERITED: readonly PropertyPath[] = [
    ["Function", "prototype"],
    ["Object", "prototype"],
];

/** A property's place: an owner's path, or `null` for the storage object. */
const placeId = (path: PropertyPath | null, key: string): string => JSON.stringify([path, key]);

const placeOf = (id: string): { path: PropertyPath | null; key: string } => {
    const [path, key] = JSON.parse(id) as [PropertyPath | null, string];
    return { path, key };
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

/** Own objects a heap may gather before cloning folds them into a new shared base. */
const FOLD = 64;

/**
 * A state's objects by id: those it shares with the states it was cloned from or joined with (`base`, never written)
 * and those it wrote since (`own`). Cloning copies the own ones; joining two states of one base looks at theirs only.
 */
class Heap {
    #base: ReadonlyMap<number, HeapObject>;
    #own: Map<number, HeapObject>;

    constructor(base: ReadonlyMap<number, HeapObject>, own: Map<number, HeapObject> = new Map()) {
        this.#base = base;
        this.#own = own;
    }

    get(id: number): HeapObject | undefined {
        return this.#own.get(id) ?? this.#base.get(id);
    }

    has(id: number): boolean {
        return this.#own.has(id) || this.#base.has(id);
    }

    set(id: number, object: HeapObject): void {
        this.#own.set(id, object);
    }

    /** A heap with the same objects that changes independently. */
    clone(): Heap {
        if (this.#own.size > FOLD) {
            this.#base = this.#entries();
            this.#own = new Map();
        }
        return new Heap(this.#base, new Map(this.#own));
    }

    #entries(): Map<number, HeapObject> {
        const all = new Map(this.#base);
        for (const [id, object] of this.#own) all.set(id, object);
        return all;
    }

    /** `a`'s objects, and `b`'s: those only `b` has, and `merge` of the two where they differ. */
    static join(a: Heap, b: Heap, merge: (mine: HeapObject, other: HeapObject) => HeapObject): Heap {
        if (a.#base !== b.#base) {
            const heap = a.#entries();
            for (const [id, other] of b.#entries()) {
                const mine = heap.get(id);
                if (mine === undefined) heap.set(id, other);
                else if (mine !== other) heap.set(id, merge(mine, other));
            }
            return new Heap(heap);
        }
        // Objects neither wrote are the base's in both.
        const own = new Map(a.#own);
        for (const [id, other] of b.#own) {
            const mine = a.get(id);
            if (mine === undefined) own.set(id, other);
            else if (mine !== other) own.set(id, merge(mine, other));
        }
        for (const [id, mine] of a.#own) {
            if (b.#own.has(id)) continue;
            const other = a.#base.get(id);
            if (other !== undefined && mine !== other) own.set(id, merge(mine, other));
        }
        return new Heap(a.#base, own);
    }
}

class State {
    constructor(
        public heap: Heap,
        /** Host globals this path found undefined (`guard`). */
        public facts: ReadonlySet<string>,
        /** Phase "call" on a setter: its writes of the forwarded global so far; -1 when paths disagree. */
        public hostWrites: number,
        /** Phase "setup": names the statement may have added to builtins so far (an accessor may sit there). */
        public added: ReadonlySet<string>,
        /** The properties the setups may have left, by `placeId`; a place not here is as before the program ran. */
        public places: Map<string, Descriptors>
    ) {}

    /** Objects only this state holds: written in place. Any sharing (`clone`, `join`, a catcher) ends it. */
    owned = new Set<HeapObject>();

    clone(): State {
        this.owned = new Set();
        return new State(this.heap.clone(), this.facts, this.hostWrites, this.added, new Map(this.places));
    }

    set(other: State): void {
        this.heap = other.heap;
        this.facts = other.facts;
        this.hostWrites = other.hostWrites;
        this.added = other.added;
        this.places = other.places;
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
        const heap = Heap.join(a.heap, b.heap, (mine, other) => {
            const props = new Map(mine.props);
            for (const [key, values] of other.props) props.set(key, union(props.get(key) ?? [UNDEFINED], values));
            for (const [key, values] of mine.props) if (!other.props.has(key)) props.set(key, union(values, [UNDEFINED]));
            return { ...mine, props };
        });
        const facts = new Set([...a.facts].filter((name) => b.facts.has(name)));
        const added = a.added === b.added ? a.added : new Set([...a.added, ...b.added]);
        const places = new Map(a.places);
        for (const [id, descriptors] of b.places) {
            const mine = places.get(id);
            if (mine !== descriptors) places.set(id, unionDescriptors(mine ?? [ABSENT], descriptors));
        }
        for (const [id, descriptors] of a.places) if (!b.places.has(id)) places.set(id, unionDescriptors(descriptors, [ABSENT]));
        return new State(heap, facts, a.hostWrites === b.hostWrites ? a.hostWrites : -1, added, places);
    }
}

interface Flow {
    readonly normal: State | undefined;
    readonly returns: readonly { readonly values: Values; readonly state: State }[];
}

/**
 * A `try` being evaluated: the join of the states where its block may throw (`undefined`: nowhere yet), and what its
 * block wrote so far (by object, and places), which a later throw sees as the state then has it.
 */
interface Catcher {
    state: State | undefined;
    readonly writes: Map<number, Set<string>>;
    readonly places: Set<string>;
}

/** What the analysed call's arguments are, per run (phase "call"). */
type Arguments = "any" | "none" | "present" | "null" | "undefined";

interface Mode {
    readonly phase: "setup" | "call";
    /** Phase "call": what `arguments` holds; past the first, any value. */
    readonly args: Arguments;
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

const SETUP: Mode = { phase: "setup", args: "any", forwards: undefined, watermark: 0, root: undefined, accessor: false, opaqueGlobals: false };

const isWithin = (node: Node, root: Node): boolean => node.start >= root.start && node.end <= root.end;

/** What the program added to builtins before a statement (or, in phase "call", at all): names, and those that are accessors. */
interface AddedNames {
    readonly names: ReadonlySet<string>;
    readonly accessors: ReadonlySet<string>;
}

const addedNames = (places: ReadonlyMap<string, Descriptors>): AddedNames => {
    const names = new Set<string>();
    const accessors = new Set<string>();
    for (const [id, descriptors] of places) {
        const { path, key } = placeOf(id);
        if (path === null) continue;
        if (descriptors.some((descriptor) => descriptor.kind !== "absent")) names.add(key);
        if (descriptors.some((descriptor) => descriptor.kind === "accessor")) accessors.add(key);
    }
    return { names, accessors };
};

/** What the evaluator needs from the runtime pass. */
export interface EvaluatorContext {
    readonly scopes: ScopeInfo;
    readonly realm: Realm;
    readonly storage: string;
    /** The program and its lone root IIFE: their bindings are the program's own (`#rootBinding`). */
    readonly rootBlocks: ReadonlySet<Node>;
}

/** A call the analysed call made of code outside the program (a builtin, or a value from its arguments): `args` as a list, or `arguments` from `from` on. */
interface OutsideCall {
    readonly callee: AV;
    readonly self: Values;
    readonly args: readonly Values[] | { readonly from: number } | undefined;
}

type CallArgs = readonly Values[] | { readonly from: number } | undefined;

/** Abstract evaluation of setup statements, then of calls of what they installed (see the module comment). */
class Evaluator {
    readonly #cx: EvaluatorContext;
    readonly #fixedVariables = new Map<Variable, boolean>();
    readonly #slotsMemo = new Map<Variable, boolean>();
    readonly #parents = new Map<Node, Map<Node, Node>>();
    readonly #fixedArguments = new Map<Node, boolean>();
    #nextId = ROOT + 1;
    #steps = 0;
    #depth = 0;
    #mode: Mode = SETUP;
    /** Phase "setup": what the program added to builtins before the statement; phase "call": what the setups added. */
    #added: AddedNames = { names: new Set(), accessors: new Set() };
    /**
     * Phase "setup": names the statement defines (on builtins or the storage object), taken to be no property of the
     * global object before the program ran (see the module comment); `#asked`: whether it asked the global object about
     * a name the builtins lack.
     */
    #ownNames: ReadonlySet<string> = new Set();
    #asked = false;
    /** For each `try` being evaluated (innermost last). */
    readonly #catchers: Catcher[] = [];
    /** Phase "call": the globals the builtins lack that the call read. */
    readonly hostReads = new Set<string>();
    /** Phase "call": whether the call read `this`. */
    usesThis = false;
    /** Phase "call": the calls of code outside the program it made, in order (`result` values index them). */
    readonly calls: OutsideCall[] = [];

    constructor(cx: EvaluatorContext) {
        this.#cx = cx;
    }

    /** The state before any setup: nothing added. */
    static initial(): State {
        return new State(new Heap(new Map([[ROOT, { kind: "frame", props: new Map() }]])), new Set(), 0, new Set(), new Map());
    }

    /**
     * The setup statement `f(args)` (`f` a root function declaration, or a function expression), from `start` (what
     * earlier setups left): its final state, or why it can't be told. `globalArgs`: arguments that hold the global
     * object when it runs. `ownNames`: see `#ownNames`; `asked` says whether the evaluation needed them.
     */
    runSetup(statement: Statement, start: State, globalArgs: ReadonlySet<Node>, ownNames: ReadonlySet<string>): { state: State; asked: boolean } | Refusal {
        try {
            this.#mode = SETUP;
            this.#added = addedNames(start.places);
            this.#ownNames = ownNames;
            this.#asked = false;
            const state = start.clone();
            state.added = new Set();
            const call = statement.type === "ExpressionStatement" && statement.expression.type === "CallExpression" ? statement.expression : undefined;
            const callee = call?.callee;
            if (call === undefined || (callee?.type !== "Identifier" && callee?.type !== "FunctionExpression" && callee?.type !== "ArrowFunctionExpression"))
                return refuse("the statement isn't a call of a root function or a function expression", statement);
            const args = call.arguments.map((arg): Values => {
                if (arg.type === "SpreadElement") return refuse("it spreads arguments", arg);
                return globalArgs.has(arg) ? [{ k: "builtin", path: [], type: "object" }] : this.#eval(arg, ROOT, state);
            });
            const [fn, ...others] = this.#eval(callee, ROOT, state);
            if (fn?.k !== "fn" || others.length > 0) return refuse("the statement calls something other than one function of the program", call);
            this.#invoke(fn, args, state);
            return { state, asked: this.#asked };
        } catch (error) {
            if (error instanceof Refusal) return error;
            throw error;
        }
    }

    /**
     * What the root-level `expression` may evaluate to, from `start`, and whether it may change a builtin or the storage
     * object (it writes neither otherwise: the evaluation refuses such writes); or why it can't be told.
     */
    evaluate(expression: Node, start: State): { values: Values; changes: boolean } | Refusal {
        try {
            this.#mode = SETUP;
            this.#added = addedNames(start.places);
            this.#ownNames = new Set();
            const state = start.clone();
            state.added = new Set();
            const values = this.#eval(expression, ROOT, state);
            return { values, changes: state.added.size > 0 || [...state.places].some(([id, descriptors]) => start.places.get(id) !== descriptors) };
        } catch (error) {
            if (error instanceof Refusal) return error;
            throw error;
        }
    }

    /**
     * One call of `fn` (a closure of the setups' final state `after`), from outside: its `this` per call, its arguments
     * as `args` says. `forwards`: a setter, which must write that global once on every path. Returns what it may return
     * (`[]`: every path throws), or why it isn't a call whose answers stay what they were.
     */
    call(fn: AV, after: State, options: { args: Arguments; accessor: boolean; forwards?: string; opaqueGlobals?: boolean }): { values: Values; state: State } | Refusal {
        try {
            if (fn.k !== "fn") return refuse("it isn't a function of the setup");
            this.#mode = {
                phase: "call",
                args: options.args,
                forwards: options.forwards,
                watermark: this.#nextId,
                root: fn.node,
                accessor: options.accessor,
                opaqueGlobals: options.opaqueGlobals ?? false,
            };
            this.#added = addedNames(after.places);
            this.hostReads.clear();
            this.usesThis = false;
            this.calls.length = 0;
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

    // ------------------------------------------------------------ throws

    /** Something may throw here: the innermost `try`'s catch block may start from this state. */
    #mayThrow(state: State): void {
        const catcher = this.#catchers.at(-1);
        if (catcher === undefined) return;
        if (catcher.state === undefined) {
            catcher.state = state.clone();
            return;
        }
        const target = catcher.state;
        for (const [id, keys] of catcher.writes) {
            const object = state.heap.get(id);
            if (object === undefined) continue;
            this.#ensure(target, state, id);
            const written = target.writable(id);
            for (const key of keys) {
                const values = object.props.get(key) ?? [UNDEFINED];
                written.props.set(key, union(written.props.get(key) ?? [UNDEFINED], values));
                for (const value of values) this.#ensureValue(target, state, value);
            }
        }
        if (state.added !== target.added) target.added = new Set([...target.added, ...state.added]);
        for (const id of catcher.places) {
            const descriptors = state.places.get(id) ?? [ABSENT];
            target.places.set(id, unionDescriptors(target.places.get(id) ?? [ABSENT], descriptors));
            for (const descriptor of descriptors) {
                const values = descriptor.kind === "data" ? descriptor.values : descriptor.kind === "accessor" ? [...descriptor.get, ...descriptor.set] : [];
                for (const value of values) this.#ensureValue(target, state, value);
            }
        }
    }

    /** A write a later throw in the innermost `try` sees. */
    #wrote(id: number, key: string): void {
        const catcher = this.#catchers.at(-1);
        if (catcher === undefined) return;
        const keys = catcher.writes.get(id);
        if (keys === undefined) catcher.writes.set(id, new Set([key]));
        else keys.add(key);
    }

    #placed(id: string): void {
        this.#catchers.at(-1)?.places.add(id);
    }

    /** Object `id` (made since the catcher's state was taken) in it, with the objects it reaches. */
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
            if (body.type !== "BlockStatement") return this.#eval(body, frame, state);
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

    /** `arguments[index]` of the analysed call. */
    #argument(index: number): AV {
        const { args } = this.#mode;
        if (args === "none") return UNDEFINED;
        if (index !== 0 || args === "any") return { k: "arg", index };
        return args === "present" ? { k: "arg", index, present: true } : prim(args === "null" ? null : undefined);
    }

    #enterFrame(fn: FunctionLike, env: number, args: readonly Values[] | undefined, state: State): number {
        const id = this.#nextId++;
        const props = new Map<string, Values>();
        const params: string[] = [];
        for (const [i, param] of fn.params.entries()) {
            if (param.type === "Identifier") {
                params.push(param.name);
                props.set(param.name, args === undefined ? [this.#argument(i)] : (args[i] ?? [UNDEFINED]));
            } else if (param.type === "RestElement" && param.argument.type === "Identifier" && args === undefined) {
                props.set(param.argument.name, [{ k: "args", from: i, array: true }]);
            } else return refuse("a destructuring, default or rest parameter", param);
        }
        state.heap.set(id, { kind: "frame", props, fn, parent: env });
        if (fn.type !== "ArrowFunctionExpression") {
            if (args === undefined) props.set("arguments", [{ k: "args", from: 0 }]);
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
                if (this.#eval(node.argument, frame, state).length > 0) this.#mayThrow(state);
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
            case "TryStatement":
                return this.#try(node, frame, state);
            default:
                return refuse(`a ${node.type}, which the evaluation doesn't follow`, node);
        }
    }

    #try(node: Node & { type: "TryStatement" }, frame: number, state: State): Flow {
        if (!this.#setup) return refuse("a try statement", node);
        if (node.finalizer !== null) return refuse("a finally block", node);
        const catcher: Catcher = { state: undefined, writes: new Map(), places: new Set() };
        this.#catchers.push(catcher);
        let flow: Flow;
        try {
            flow = this.#statement(node.block, frame, state);
        } finally {
            this.#catchers.pop();
        }
        // An outer `try` sees this block's writes at its own throws, the catch block's included.
        const outer = this.#catchers.at(-1);
        if (outer !== undefined) {
            for (const [id, keys] of catcher.writes) for (const key of keys) this.#wrote(id, key);
            for (const id of catcher.places) outer.places.add(id);
        }
        // The catch parameter is never read (`#identifier` refuses catch bindings).
        if (node.handler === null || catcher.state === undefined) return flow;
        const caught = this.#statement(node.handler.body, frame, catcher.state);
        return { normal: State.join(flow.normal, caught.normal), returns: [...flow.returns, ...caught.returns] };
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
            } else if (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage" || value.k === "argc") truthy = true;
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
                    if (key === "__proto__" && property.key.type !== "Identifier") return refuse("an object literal setting its prototype", property);
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
                const values = this.#binary(node.operator === "++" ? "+" : "-", this.#unary("+", old, node, state), [prim(1)], node, state);
                if (values.length === 0) return [];
                this.#write(node.argument, values, frame, state);
                return node.prefix ? values : this.#unary("+", old, node, state);
            }
            case "UnaryExpression": {
                if (node.operator === "delete") return refuse("a delete", node);
                return this.#unary(node.operator, this.#eval(node.argument, frame, state), node, state);
            }
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier") return refuse("a private name", node);
                const guard = this.#guard(node, frame, state);
                if (guard !== undefined) return guard;
                const left = this.#eval(node.left, frame, state);
                const right = this.#eval(node.right, frame, state);
                return left.length === 0 || right.length === 0 ? [] : this.#binary(node.operator, left, right, node, state);
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
            return this.#binary(node.operator, this.#unary("typeof", read, typeOf, state), compared, node, state);
        }
        const compared = this.#eval(other, frame, state);
        if (compared.length !== 1 || compared[0]?.k !== "prim" || compared[0].v !== "undefined") return refuse("a host global's type compared with something else", node);
        return [{ k: "guard", name: read[0].name, when: positive }];
    }

    #unary(operator: string, values: Values, node: Node, state: State): Values {
        let out: Values = [];
        for (const value of values) {
            let result: AV;
            if (value.k === "prim") {
                const evaluated = unary(operator, value.v);
                if (!evaluated.ok) return refuse(`the operator ${operator}`, node);
                result = prim(evaluated.value);
            } else if (operator === "void") result = UNDEFINED;
            else if (operator === "!" && value.k === "guard") result = { ...value, when: !value.when };
            else if (operator === "!" && (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage" || value.k === "argc")) result = prim(false);
            else if (operator === "typeof" && (value.k === "builtin" || value.k === "fn" || value.k === "obj" || value.k === "storage"))
                result = prim(value.k === "builtin" ? value.type : value.k === "obj" ? "object" : "function");
            else if (operator === "typeof" && value.k === "argc") result = prim("number");
            else if (value.k === "argc") result = ARG;
            else if (isPerCall(value) && (!this.#mode.accessor || operator === "typeof" || operator === "!" || operator === "void")) result = ARG;
            else if (value.k === "unknown") {
                // A conversion of an unknown value may run code that throws.
                if (operator !== "typeof" && operator !== "!") this.#mayThrow(state);
                result = UNKNOWN;
            } else return refuse(`the operator ${operator} on ${value.k === "host" ? "a host global" : "a value it can't tell"}`, node);
            out = union(out, [result]);
        }
        return out;
    }

    /** `argc` (at least 1) compared with the number `n`: decided where it can be. */
    #count(operator: string, n: number, countFirst: boolean): AV {
        const op = countFirst ? operator : (({ "<": ">", ">": "<", "<=": ">=", ">=": "<=" } as Record<string, string>)[operator] ?? operator);
        const below = n < 1 || !Number.isInteger(n);
        switch (op) {
            case ">":
                return n < 1 ? prim(true) : ARG;
            case ">=":
                return n <= 1 ? prim(true) : ARG;
            case "<":
                return n <= 1 ? prim(false) : ARG;
            case "<=":
                return n < 1 ? prim(false) : ARG;
            case "===":
            case "==":
                return below ? prim(false) : ARG;
            case "!==":
            case "!=":
                return below ? prim(true) : ARG;
            default:
                return ARG;
        }
    }

    #binary(operator: string, left: Values, right: Values, node: Node, state: State): Values {
        let out: Values = [];
        for (const l of left) {
            for (const r of right) {
                let result: AV;
                if (l.k === "prim" && r.k === "prim") {
                    const evaluated = binary(operator, l.v, r.v);
                    if (!evaluated.ok) return refuse(`the operator ${operator}`, node);
                    result = typeof evaluated.value === "string" && evaluated.value.length > MAX_STRING ? UNKNOWN : prim(evaluated.value);
                } else if ((l.k === "argc" && r.k === "prim" && typeof r.v === "number") || (r.k === "argc" && l.k === "prim" && typeof l.v === "number")) {
                    result = this.#count(operator, (l.k === "prim" ? l.v : r.k === "prim" ? r.v : 0) as number, l.k === "argc");
                } else if (
                    (operator === "===" || operator === "!==") &&
                    ((l.k === "arg" && l.present === true && r.k === "prim" && (r.v === null || r.v === undefined)) ||
                        (r.k === "arg" && r.present === true && l.k === "prim" && (l.v === null || l.v === undefined)))
                ) {
                    // An argument that is neither `null` nor `undefined`.
                    result = prim(operator === "!==");
                } else if (isPerCall(l) || isPerCall(r)) {
                    // A conversion of a per-call object runs its code.
                    if (this.#mode.accessor && operator !== "===" && operator !== "!==") return refuse(`the operator ${operator} on its receiver or arguments`, node);
                    result = ARG;
                } else if (l.k === "unknown" || r.k === "unknown") {
                    if (operator !== "===" && operator !== "!==") this.#mayThrow(state);
                    result = UNKNOWN;
                } else if (this.#setup && operator !== "===" && operator !== "!==" && (this.#added.accessors.has("valueOf") || this.#added.accessors.has("toString")))
                    return refuse(`the operator ${operator} converts an object, which may run a method the program added`, node);
                else if ((operator === "===" || operator === "!==") && l.k !== "host" && r.k !== "host" && l.k !== "guard" && r.k !== "guard") {
                    // Identity: equal values are one object; distinct objects the evaluation made differ, an object is no
                    // primitive; two builtin paths are one object where the realm finds one there (model 7).
                    const same = sameValue(l, r)
                        ? true
                        : l.k === "prim" || r.k === "prim" || (l.k === "obj" && r.k === "obj")
                          ? false
                          : l.k === "builtin" && r.k === "builtin"
                            ? this.#cx.realm.same(l.path, r.path)
                            : undefined;
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
            values = old.length === 0 || right.length === 0 ? [] : this.#binary("+", old, right, node, state);
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
            return this.#resolve([], node.name, node, state, true);
        }
        const block = variable.scope.block as unknown as Node;
        if (variable.scope.type === "global" || this.#cx.rootBlocks.has(block)) return this.#rootBinding(variable, node, state);
        if (variable.scope.type !== "function") return refuse(`${node.name} is a ${variable.scope.type} binding`, node);
        const id = this.#frameOf(block, frame, state, node);
        if (!this.#own(id) && !this.#fixedVariable(variable)) return refuse(`${node.name} is written by code that may run later`, node);
        return state.heap.get(id)?.props.get(node.name) ?? refuse(`${node.name} has no value in its frame`, node);
    }

    /**
     * The storage object; a root function declaration never written; anything else at the root may change later (or
     * hold anything already, or not be initialised yet).
     */
    #rootBinding(variable: Variable, node: Node, state: State): Values {
        const declaration = variable.defs.length === 1 ? (variable.defs[0]?.node as unknown as Node | undefined) : undefined;
        if (declaration?.type === "FunctionDeclaration" && this.#cx.scopes.staticReferences(variable).every((reference) => !reference.isWrite())) {
            if (variable.name === this.#cx.storage) return this.#setup ? [{ k: "storage" }] : refuse("it reads the storage object", node);
            return [{ k: "fn", node: declaration, env: ROOT }];
        }
        if (this.#setup) this.#mayThrow(state);
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
        this.#wrote(id, node.name);
    }

    #write(target: Node, values: Values, frame: number, state: State): void {
        if (target.type === "Identifier") return this.#writeVariable(target, values, frame, state);
        if (target.type !== "MemberExpression" || target.optional) return void refuse("a write to something other than a name or member", target);
        const objects = this.#eval(target.object, frame, state);
        const keys = this.#key(target, frame, state);
        const single = objects.length * keys.length === 1;
        for (const object of objects) {
            for (const key of keys) {
                if (key.k !== "prim" || typeof key.v === "symbol") return void refuse("a write under a key it can't tell", target);
                const name = String(key.v);
                if (object.k === "obj" && this.#own(object.id) && state.heap.get(object.id)?.kind !== "arguments" && state.heap.get(object.id)?.kind !== "frame") {
                    if (name === "__proto__") return void refuse("a write of an object's prototype", target);
                    const writable = state.writable(object.id);
                    // A write through a choice of objects or keys may miss this one: it keeps its old value too.
                    writable.props.set(name, single ? values : union(writable.props.get(name) ?? [UNDEFINED], values));
                    this.#wrote(object.id, name);
                } else if (object.k === "builtin" && this.#setup) this.#writeBuiltin(object.path, name, values, single, target, state);
                else if (object.k === "builtin" && object.path.length === 0 && this.#mode.forwards === name && !this.#cx.realm.before[0]?.has(name)) {
                    if (values.length !== 1 || values[0]?.k !== "arg" || values[0].index !== 0) return void refuse("the setter writes something other than its argument", target);
                    if (state.hostWrites !== -1) state.hostWrites++;
                } else if (object.k === "prim" && (object.v === undefined || object.v === null)) this.#mayThrow(state);
                else return void refuse(object.k === "obj" ? "it writes an object that outlives the call" : "it writes a property of something other than its own objects", target);
            }
        }
    }

    /** Phase "setup": `path.name = values`, a name the builtin didn't have (model 7: nothing on its prototypes intercepts it). */
    #writeBuiltin(path: PropertyPath, name: string, values: Values, single: boolean, target: Node, state: State): void {
        const { realm } = this.#cx;
        const owner = realm.owners.findIndex((known) => samePath(known, path));
        if (owner === -1 || realm.before[owner]?.has(name) !== false) return void refuse(`it writes ${pathName(path)}.${name}`, target);
        this.#unreached(name, state, target);
        const inherited = realm.lookup(path, name);
        if (inherited.kind === "accessor" || (inherited.kind === "data" && !inherited.writable))
            return void refuse(`it writes ${pathName(path)}.${name}, which it inherits as more than a writable value`, target);
        const id = placeId(path, name);
        const descriptor: Descriptor = { kind: "data", values, configurable: true, writable: true };
        state.places.set(id, single ? [descriptor] : unionDescriptors(state.places.get(id) ?? [ABSENT], [descriptor]));
        state.added = new Set([...state.added, name]);
        this.#placed(id);
    }

    // ------------------------------------------------------------ properties

    #member(objects: Values, keys: Values, node: Node, state: State): Values {
        let out: Values = [];
        for (const object of objects) {
            for (const key of keys) {
                if (isPerCall(key)) {
                    if (!isPerCall(object)) return refuse("a per-call key on a value that outlives the call", node);
                    out = union(out, [ARG]);
                    continue;
                }
                if (key.k !== "prim") {
                    if (this.#setup) this.#mayThrow(state);
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
                if (object.v === undefined || object.v === null) {
                    this.#mayThrow(state);
                    return [];
                }
                if (typeof object.v === "string" && key === "length") return [prim(object.v.length)];
                if (typeof object.v === "string" && isIndexKey(key)) return [prim(object.v[Number(key)])];
                if (this.#setup) this.#unreached(key, state, node);
                return this.#unknown("a property of a primitive", node);
            case "builtin":
                return this.#resolve(object.path, key, node, state);
            case "obj":
                return this.#objectProperty(object.id, key, node, state);
            case "arg":
                if (this.#mode.accessor) return refuse("it reads a property of its receiver or arguments", node);
                return object.index === undefined ? [ARG] : [{ k: "method", index: object.index, key }];
            case "method":
                // Model 7: the method's `apply` and `call` are Function.prototype's (a value without them throws either way).
                if (key === "apply") return [{ k: "builtin", path: FUNCTION_APPLY, type: "function" }];
                if (key === "call") return [{ k: "builtin", path: FUNCTION_CALL, type: "function" }];
                return [ARG];
            case "result":
            case "argc":
                return [ARG];
            case "args":
                if (key === "length") return this.#mode.args === "none" ? [prim(0)] : object.from === 0 && this.#mode.args !== "any" ? [ARGC] : [ARG];
                if (isIndexKey(key)) return [this.#argument(object.from + Number(key))];
                // Model 7: a rest parameter's array has Array.prototype's methods.
                return object.array === true ? this.#resolve(["Array", "prototype"], key, node, state) : [ARG];
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
     * `path.key` on a builtin, as the realm has it: a builtin or primitive where the builtins have the key (model 7); a
     * name the program added may hold anything; absent stays absent. On the global object, any other key is a global
     * the host or the program may set at any time: a live read (phase "call"), or unknown (phase "setup"). Reading it
     * runs no code that throws (model 10: the host's globals answer); as a `reference` it throws when absent.
     */
    #resolve(path: PropertyPath, key: string, node: Node, state: State, reference = false): Values {
        const { realm } = this.#cx;
        const found = this.#added.names.has(key) || state.added.has(key) ? undefined : realm.lookup(path, key);
        if (found === undefined || found.kind === "absent" || found.kind === "base") {
            if (this.#setup) {
                const value = this.#missing(key, state, node);
                if (path.length > 0 && found !== undefined && found.kind !== "base") return value;
                if (reference) this.#mayThrow(state);
                return [UNKNOWN];
            }
            if (path.length === 0) {
                this.hostReads.add(key);
                return [this.#mode.opaqueGlobals ? ARG : { k: "host", name: key }];
            }
            if (found?.kind === "absent") return [UNDEFINED];
            return refuse(`${pathName(path)}.${key} may be a property the program added`, node);
        }
        if (found.kind === "accessor") {
            if (this.#setup) this.#mayThrow(state);
            return this.#unknown(`${pathName(path)}.${key} is an accessor`, node);
        }
        if (found.owner >= 0) return [{ k: "builtin", path: realm.owners[found.owner] ?? refuse("an owner the realm doesn't list", node), type: found.type }];
        if (found.type === "object" || found.type === "function") {
            const holder = found.holder >= 0 ? realm.owners[found.holder] : path;
            return [{ k: "builtin", path: [...(holder ?? path), key], type: found.type }];
        }
        if (found.type === "symbol" || found.type === "bigint") return this.#unknown(`${pathName(path)}.${key} is a ${found.type}`, node);
        return [prim(found.value as Value)];
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
        let spread: CallArgs | "unknown";
        const args: Values[] = [];
        for (const arg of node.arguments) {
            if (arg.type === "SpreadElement") {
                if (this.#setup) return refuse("a spread argument", arg);
                const spreadValues = this.#eval(arg.argument, frame, state);
                this.#handOn(spreadValues, arg);
                // `f(...arguments)` (or a slice of it, a rest parameter): the call's arguments from `from` on.
                const [only] = spreadValues;
                spread = node.arguments.length === 1 && spreadValues.length === 1 && only?.k === "args" ? { from: only.from } : "unknown";
                continue;
            }
            const values = this.#eval(arg, frame, state);
            if (values.length === 0) return [];
            args.push(values);
        }
        return this.#apply(callees, self, spread === "unknown" ? undefined : (spread ?? args), node, state);
    }

    /** Values a call hands to code the evaluation doesn't follow: per call, the call's own objects, builtins, primitives. */
    #handOn(values: Values, node: Node): void {
        for (const value of values) {
            if (value.k === "fn") refuse("it hands a function of the program to code it doesn't follow", node);
            if (value.k === "obj" && (this.#setup || !this.#own(value.id))) refuse("it hands an object the setup made to code it doesn't follow", node);
            if (value.k === "host" || value.k === "guard" || value.k === "unknown" || value.k === "storage") refuse("it hands a value it can't tell to code it doesn't follow", node);
            if (isPerCall(value) && this.#mode.accessor) refuse("it hands its receiver or arguments to code it doesn't follow", node);
        }
    }

    /** `args` undefined: a list known only per call (a spread, `apply` with an unknown list). */
    #apply(callees: Values, self: Values, args: CallArgs, node: Node, state: State): Values {
        let out: Values = [];
        for (const callee of callees) {
            if (callee.k === "prim") {
                // Not callable: this path throws.
                this.#mayThrow(state);
                continue;
            }
            if (callee.k === "fn") {
                if (!this.#setup && (this.#mode.root === undefined || !isWithin(callee.node, this.#mode.root))) return refuse("it calls a function defined elsewhere", node);
                if (!Array.isArray(args)) return refuse("a call of a program function with arguments it can't tell", node);
                const branch = callees.length === 1 ? state : state.clone();
                out = union(out, this.#invoke(callee, args as readonly Values[], branch));
                if (branch !== state) state.set(State.join(state, branch) as State);
                continue;
            }
            if (callee.k === "builtin" && (samePath(callee.path, FUNCTION_CALL) || samePath(callee.path, FUNCTION_APPLY))) {
                // `f.call(t, ...a)` / `f.apply(t, a)` (model 7: these are the builtins): a call of `f`.
                out = union(out, this.#apply(self, ...this.#passedOn(callee.path, args, node, state), node, state));
                continue;
            }
            if (callee.k === "builtin" && samePath(callee.path, DEFINE_PROPERTY) && this.#setup) {
                out = union(out, this.#defineProperty(args, node, state));
                continue;
            }
            if (callee.k === "builtin" && samePath(callee.path, HAS_OWN_PROPERTY) && this.#setup) {
                out = union(out, this.#hasOwnProperty(self, args, node, state));
                continue;
            }
            if (callee.k === "builtin" && this.#setup) return refuse(`it calls ${pathName(callee.path)}, which the evaluation doesn't model (it may run program code)`, node);
            if (callee.k === "builtin" && samePath(callee.path, ARRAY_SLICE) && this.#sliced(self, args) !== undefined) {
                out = union(out, [this.#sliced(self, args) as AV]);
                continue;
            }
            if (callee.k === "builtin" || (isPerCall(callee) && !this.#setup && !this.#mode.accessor)) {
                // A builtin (model 7) or a per-call function: what it does is the alias's meaning, not the getter's state.
                this.#handOn(self, node);
                if (Array.isArray(args)) for (const values of args as readonly Values[]) this.#handOn(values, node);
                else if (args !== undefined && this.#mode.accessor) refuse("it hands its arguments to code it doesn't follow", node);
                const call = this.calls.push({ callee, self, args }) - 1;
                out = union(out, [{ k: "result", call }]);
                continue;
            }
            return refuse("it calls a value it can't tell", node);
        }
        return out;
    }

    /** The `this` and arguments `f.call(t, ...a)` / `f.apply(t, a)` give `f`. */
    #passedOn(path: PropertyPath, args: CallArgs, node: Node, state: State): [Values, CallArgs] {
        if (!Array.isArray(args)) return [[ARG], undefined];
        const list = args as readonly Values[];
        const [thisArg = [UNDEFINED], passed] = list;
        if (samePath(path, FUNCTION_CALL)) return [thisArg, list.slice(1)];
        if (passed === undefined || passed.every((value) => value.k === "prim" && (value.v === undefined || value.v === null))) return [thisArg, []];
        const [only] = passed;
        if (passed.length === 1 && only?.k === "args") return [thisArg, { from: only.from }];
        // A primitive list throws; anything else is a list known only per call.
        if (passed.some((value) => value.k === "prim")) this.#mayThrow(state);
        this.#handOn(passed, node);
        return [thisArg, undefined];
    }

    /** `Array.prototype.slice.call(arguments, n)` (model 7) as an array of the arguments from `n` on; `undefined` for any other slice. */
    #sliced(self: Values, args: CallArgs): AV | undefined {
        const [only] = self;
        if (self.length !== 1 || only?.k !== "args" || !Array.isArray(args)) return undefined;
        const [start = [prim(0)], end] = args as readonly Values[];
        const [first] = start;
        if (end !== undefined || start.length !== 1 || first?.k !== "prim" || typeof first.v !== "number" || !Number.isSafeInteger(first.v) || first.v < 0) return undefined;
        return { k: "args", from: only.from + first.v, array: true };
    }

    /** Phase "setup": `Object.prototype.hasOwnProperty` on builtins, as the realm and the setups' places tell (see `#ownProperty`). */
    #hasOwnProperty(self: Values, args: CallArgs, node: Node, state: State): Values {
        if (!Array.isArray(args)) return refuse("hasOwnProperty with arguments it can't tell", node);
        const [keys = [UNDEFINED]] = args as readonly Values[];
        this.#handOn(keys, node);
        let out: Values = [];
        for (const object of self) {
            if (object.k === "prim" && (object.v === undefined || object.v === null)) {
                this.#mayThrow(state);
                continue;
            }
            for (const key of keys) {
                const own = object.k === "builtin" && key.k === "prim" && typeof key.v !== "symbol" ? this.#ownProperty(object.path, String(key.v), state) : undefined;
                out = union(out, own === undefined ? BOOLEAN : [prim(own)]);
            }
        }
        return out;
    }

    /**
     * Whether the builtin at `path` has `key` as its own property: as the realm has it (model 7), but for what the setups
     * added. A global the builtins lack may be the host's (model 10), but for names the statement defines (`#ownNames`).
     */
    #ownProperty(path: PropertyPath, key: string, state: State): boolean | undefined {
        const descriptors = state.places.get(placeId(path, key));
        if (descriptors !== undefined) {
            const present = descriptors.some((descriptor) => descriptor.kind !== "absent");
            const absent = descriptors.some((descriptor) => descriptor.kind === "absent");
            return present && absent ? undefined : present;
        }
        if (this.#cx.realm.ownNames(path)?.has(key) === true) return true;
        if (path.length > 0) return false;
        this.#asked = true;
        return this.#ownNames.has(key) ? false : undefined;
    }

    /**
     * `Object.defineProperty(target, key, descriptor)` on a builtin (a name it doesn't have) or the storage object, with a
     * descriptor object the evaluation made. It throws only where the property may be there already and not
     * configurable (model 7: builtins are extensible; `FIXED_FUNCTION_PROPERTIES` for the storage object).
     */
    #defineProperty(args: CallArgs, node: Node, state: State): Values {
        if (!Array.isArray(args)) return refuse("defineProperty with arguments it can't tell", node);
        const [targets = [UNDEFINED], keys = [UNDEFINED], objects = [UNDEFINED]] = args as readonly Values[];
        // The descriptor's fields are looked up on it, then on Object.prototype.
        for (const field of ["get", "set", "value", "writable", "enumerable", "configurable"]) this.#unreached(field, state, node);
        const descriptors: Descriptor[] = [];
        /** Data descriptors that leave `writable` out: `false` on a new property, the old one's on one there already. */
        const unsaid = new Set<Descriptor>();
        for (const object of objects) {
            const fields = object.k === "obj" ? state.heap.get(object.id) : undefined;
            if (fields?.kind !== "object") return refuse("defineProperty with a descriptor it can't tell", node);
            const { props } = fields;
            const configurable = props.has("configurable") ? this.#boolean(props.get("configurable") ?? []) : false;
            if (props.has("get") || props.has("set")) {
                if (props.has("value") || props.has("writable")) return refuse("a descriptor with both accessors and a value (it throws)", node);
                const get = props.get("get") ?? [UNDEFINED];
                const set = props.get("set") ?? [UNDEFINED];
                if ([...get, ...set].some((fn) => fn.k !== "fn" && !(fn.k === "prim" && fn.v === undefined))) return refuse("an accessor that may not be a function (it throws)", node);
                descriptors.push({ kind: "accessor", get, set, configurable });
            } else {
                const descriptor: Descriptor = {
                    kind: "data",
                    values: props.get("value") ?? [UNDEFINED],
                    configurable,
                    writable: props.has("writable") ? this.#boolean(props.get("writable") ?? []) : false,
                };
                if (!props.has("writable")) unsaid.add(descriptor);
                descriptors.push(descriptor);
            }
        }
        const { realm } = this.#cx;
        const places: string[] = [];
        let mayThrow = false;
        const added = new Set(state.added);
        for (const target of targets) {
            for (const key of keys) {
                if (key.k !== "prim" || typeof key.v === "symbol") return refuse("defineProperty under a key it can't tell", node);
                const name = String(key.v);
                let id: string;
                if (target.k === "storage") {
                    id = placeId(null, name);
                    if (FIXED_FUNCTION_PROPERTIES.has(name)) mayThrow = true;
                } else if (target.k === "builtin") {
                    const owner = realm.owners.findIndex((path) => samePath(path, target.path));
                    if (owner === -1) return refuse(`defineProperty on ${pathName(target.path)}, which isn't a builtin a name reaches`, node);
                    if (realm.before[owner]?.has(name) !== false) return refuse(`it redefines ${pathName(target.path)}.${name}`, node);
                    id = placeId(target.path, name);
                    added.add(name);
                } else return refuse("defineProperty on something other than a builtin or the storage object", node);
                if ((state.places.get(id) ?? []).some((descriptor) => descriptor.kind !== "absent" && descriptor.configurable !== true)) mayThrow = true;
                places.push(id);
            }
        }
        if (mayThrow) this.#mayThrow(state);
        const single = places.length * descriptors.length === 1;
        for (const id of places) {
            // The storage object may have the property from code other than the setups.
            const there = placeOf(id).path === null || (state.places.get(id) ?? []).some((descriptor) => descriptor.kind !== "absent");
            const placed =
                there && unsaid.size > 0
                    ? descriptors.map((descriptor): Descriptor => (unsaid.has(descriptor) && descriptor.kind === "data" ? { ...descriptor, writable: undefined } : descriptor))
                    : descriptors;
            state.places.set(id, single ? placed : unionDescriptors(state.places.get(id) ?? [ABSENT], placed));
            this.#placed(id);
        }
        state.added = added;
        return targets;
    }

    /** `true`/`false` where every value converts alike; `undefined` otherwise. */
    #boolean(values: Values): boolean | undefined {
        const { truthy, falsy } = this.#truths(values);
        return truthy === falsy ? undefined : truthy;
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

// ------------------------------------------------------------ the analysis

/** Why a property can't stand for what it seems to. */
interface Failure {
    readonly reason: string;
    readonly node: Node | undefined;
}

const failure = (refusal: Refusal, what: string): Failure => ({ reason: `${what}: ${refusal.reason}`, node: refusal.node });

const isFailure = (value: object): value is Failure => "reason" in value;

export interface SetupFacts {
    /** Root `G.k = (function () {...})()` statements whose function provably returns the global object, by key. */
    readonly globalSlots: ReadonlyMap<string, Statement>;
    /** Root `G.k = ...` statements whose right side the evaluator shows changes no builtin, global or storage property. */
    readonly local: ReadonlySet<Statement>;
    readonly setup: ReadonlySet<Statement>;
    /** Storage keys the setup calls define, whatever the property (`SetupAnalysis.#facts`). */
    readonly setupKeys: ReadonlySet<string>;
    /** Keys the setup calls add to what a function inherits (`Function.prototype`, `Object.prototype`), whatever the property. */
    readonly inheritedKeys: ReadonlySet<string>;
    readonly setupGlobals: ReadonlySet<string>;
    readonly aliases: readonly Alias[];
    readonly unprovenAliases: ReadonlySet<string>;
    readonly callAliases: ReadonlyMap<string, CallAlias>;
    readonly globalReads: ReadonlyMap<string, string>;
    readonly hostAliases: ReadonlyMap<string, string>;
    readonly thisFreeKeys: ReadonlySet<string>;
}

export interface SetupContext extends EvaluatorContext {
    readonly log: PassLog;
}

/** `G.k = <call of a function expression with no arguments>`. */
const slotAssignment = (statement: Statement, storage: string): { key: string; call: CallExpression } | undefined => {
    if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return undefined;
    const { left, right } = statement.expression;
    if (left.type !== "MemberExpression" || left.object.type !== "Identifier" || left.object.name !== storage || right.type !== "CallExpression") return undefined;
    const key = propertyKey(left);
    return key === undefined || (right.callee.type !== "FunctionExpression" && right.callee.type !== "ArrowFunctionExpression") || right.arguments.length > 0 ? undefined : { key, call: right };
};

/** `G.k`. */
const slotRead = (node: Node, storage: string): string | undefined =>
    node.type === "MemberExpression" && node.object.type === "Identifier" && node.object.name === storage ? propertyKey(node) : undefined;

/** A root call of a function expression, or of a root function declaration. */
const isSetupCandidate = (statement: Statement, cx: EvaluatorContext): boolean => {
    if (statement.type !== "ExpressionStatement" || statement.expression.type !== "CallExpression") return false;
    const { callee } = statement.expression;
    if (callee.type === "FunctionExpression" || callee.type === "ArrowFunctionExpression") return true;
    const variable = callee.type === "Identifier" ? cx.scopes.staticVariableOf(callee) : undefined;
    const definition = variable?.defs.length === 1 ? (variable.defs[0]?.node as unknown as Node | undefined) : undefined;
    return variable !== undefined && definition?.type === "FunctionDeclaration" && cx.rootBlocks.has(variable.scope.block as unknown as Node);
};

/**
 * The setup calls among the root statements, in order, and what the properties they leave stand for (see the module
 * comment). A statement that asks the global object about a name the builtins lack is evaluated again, taking the names
 * it defines to be none of the global object's before the program ran (models 2, 9); it must then define the same.
 */
export class SetupAnalysis {
    readonly #cx: SetupContext;
    readonly #evaluator: Evaluator;
    /** What the setups so far left. */
    #state = Evaluator.initial();
    /** By place: the setup statement that last changed it. */
    readonly #changedBy = new Map<string, Statement>();
    readonly #globalSlots = new Map<string, Statement>();
    /** Root `G.k = ...` statements whose right side changes no builtin, global or storage property (the evaluator's word). */
    readonly #local = new Set<Statement>();
    readonly #setups: Statement[] = [];
    /** By setup statement: the places it changed. */
    readonly #changed = new Map<Statement, readonly string[]>();
    /** By root statement walked so far: the storage keys it may write (`undefined`: any, or it may run code that does). */
    readonly #writes = new Map<Statement, ReadonlySet<string> | undefined>();

    constructor(cx: SetupContext) {
        this.#cx = cx;
        this.#evaluator = new Evaluator(cx);
    }

    run(body: readonly Statement[]): SetupFacts {
        for (const [index, statement] of body.entries()) {
            const slot = slotAssignment(statement, this.#cx.storage);
            let writes: ReadonlySet<string> | undefined;
            if (slot !== undefined) writes = this.#slot(slot.key, slot.call, statement);
            else if (isSetupCandidate(statement, this.#cx)) writes = this.#candidate(statement, this.#globalArgs(statement, body, index));
            else writes = this.#storageWrites(statement);
            this.#writes.set(statement, writes);
        }
        return this.#facts();
    }

    /** `G.k = (function () {...})()`: whether it stores the global object (models 7, 10). Returns what it writes. */
    #slot(key: string, call: CallExpression, statement: Statement): ReadonlySet<string> | undefined {
        this.#globalSlots.delete(key);
        if (this.#state.places.has(placeId(null, key))) {
            this.#cx.log.debug(`${this.#cx.storage}.${key} is a property a setup call defined: not taken as holding the global object`, statement);
            return undefined;
        }
        const evaluated = this.#evaluator.evaluate(call, this.#state);
        if (evaluated instanceof Refusal || evaluated.changes) return undefined;
        this.#local.add(statement);
        const [only, ...others] = evaluated.values;
        if (others.length === 0 && only?.k === "builtin" && only.path.length === 0) this.#globalSlots.set(key, statement);
        return new Set([key]);
    }

    /**
     * What a root statement other than a slot or a setup call may write on the storage object: nothing for a function
     * declaration; `G.other = <expression>` (no accessor of the setups' there), whose evaluation writes no builtin and
     * no storage property (the evaluation refuses any other way), only `G.other`; anything else, anything.
     */
    #storageWrites(statement: Statement): ReadonlySet<string> | undefined {
        if (statement.type === "FunctionDeclaration" || statement.type === "EmptyStatement") return new Set();
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return undefined;
        const { left, right } = statement.expression;
        const written = slotRead(left, this.#cx.storage);
        if (written === undefined || this.#state.places.has(placeId(null, written))) return undefined;
        const evaluated = this.#evaluator.evaluate(right, this.#state);
        if (evaluated instanceof Refusal || evaluated.changes) return undefined;
        this.#local.add(statement);
        return new Set([written]);
    }

    /**
     * The call's arguments `G.k` holding the global object when it runs: `G.k` a global slot whose statement came before,
     * and no root statement between them may write it (model 3: `G` changes only through its paths).
     */
    #globalArgs(statement: Statement, body: readonly Statement[], index: number): Set<Node> {
        const held = new Set<Node>();
        const call = statement.type === "ExpressionStatement" && statement.expression.type === "CallExpression" ? statement.expression : undefined;
        for (const arg of call?.arguments ?? []) {
            const key = slotRead(arg, this.#cx.storage);
            const slot = key === undefined ? undefined : this.#globalSlots.get(key);
            if (key === undefined || slot === undefined) continue;
            const unsafe = body.slice(body.indexOf(slot) + 1, index).find((other) => this.#writes.get(other)?.has(key) !== false);
            if (unsafe === undefined) held.add(arg);
            else this.#cx.log.debug(`${this.#cx.storage}.${key} may change before the call: not taken as the global object there`, unsafe);
        }
        return held;
    }

    /** A setup call: evaluated, and its places taken on when it changes any. Returns the storage keys it may define. */
    #candidate(statement: Statement, globalArgs: ReadonlySet<Node>): ReadonlySet<string> | undefined {
        const log = this.#cx.log;
        let run = this.#evaluator.runSetup(statement, this.#state, globalArgs, new Set());
        if (run instanceof Refusal) return void log.debug(`not taken as a setup call: ${run.reason}`, run.node ?? statement);
        const names = this.#defined(run.state);
        if (run.asked && names.size > 0) {
            run = this.#evaluator.runSetup(statement, this.#state, globalArgs, names);
            if (run instanceof Refusal) return void log.debug(`not taken as a setup call: taking the names it defines as new, ${run.reason}`, run.node ?? statement);
            const again = this.#defined(run.state);
            if (again.size !== names.size) return void log.debug("not taken as a setup call: which names it defines depends on which the global object has", statement);
        }
        const { state } = run;
        const changed = [...state.places].filter(([id, descriptors]) => this.#state.places.get(id) !== descriptors).map(([id]) => id);
        if (changed.length > 0) {
            this.#state = state;
            for (const id of changed) this.#changedBy.set(id, statement);
            this.#setups.push(statement);
            this.#changed.set(statement, changed);
        }
        return new Set(changed.flatMap((id) => (placeOf(id).path === null ? [placeOf(id).key] : [])));
    }

    /** The names of the properties `state` may hold that the setups before it didn't define. */
    #defined(state: State): Set<string> {
        const names = new Set<string>();
        for (const [id, descriptors] of state.places) {
            if (this.#state.places.get(id) === descriptors || !descriptors.some((descriptor) => descriptor.kind !== "absent")) continue;
            names.add(placeOf(id).key);
        }
        return names;
    }

    #facts(): SetupFacts {
        const { log, storage } = this.#cx;
        const facts = {
            setupKeys: new Set<string>(),
            inheritedKeys: new Set<string>(),
            setupGlobals: new Set<string>(),
            aliases: [] as Alias[],
            unprovenAliases: new Set<string>(),
            callAliases: new Map<string, CallAlias>(),
            globalReads: new Map<string, string>(),
            hostAliases: new Map<string, string>(),
            thisFreeKeys: new Set<string>(),
        };
        // A setup call after a slot's statement may redefine the slot.
        for (const [key, statement] of this.#globalSlots) {
            if (!this.#state.places.has(placeId(null, key))) continue;
            this.#globalSlots.delete(key);
            log.debug(`${storage}.${key} is a property a setup call defines: not taken as holding the global object`, statement);
        }
        /** Statements that added a property to a builtin (not the global object) that reads as no builtin property. */
        const unexpected = new Map<Statement, string>();
        for (const [id, descriptors] of this.#state.places) {
            const { path, key } = placeOf(id);
            const statement = this.#changedBy.get(id);
            // Whatever the property: a read of it, or a write to it, depends on the setup call.
            if (path === null) {
                facts.setupKeys.add(key);
                continue;
            }
            if (INHERITED.some((owner) => samePath(owner, path))) facts.inheritedKeys.add(key);
            if (path.length === 0) facts.setupGlobals.add(key);
            const read = this.#reads(descriptors);
            if (read !== undefined && isFailure(read)) {
                if (path.length > 0) {
                    facts.unprovenAliases.add(key);
                    log.debug(`alias ${pathName(path)}.${key}: not taken, ${read.reason}`, read.node ?? statement);
                } else this.#hostAlias(key, descriptors, read, facts.hostAliases, statement);
                continue;
            }
            const original = read === undefined ? undefined : this.#cx.realm.nameOf(path, read.k === "builtin" ? { path: read.path } : { primitive: read.v });
            if (original !== undefined) {
                facts.aliases.push({ owner: path, alias: key, original });
                log.debug(`alias ${pathName(path)}.${key} = ${pathName(path)}.${original}`, statement);
            } else if (path.length > 0 && statement !== undefined && !unexpected.has(statement)) unexpected.set(statement, `${pathName(path)}.${key} added as ${described(descriptors)}`);
        }
        const setup = new Set(this.#setups.filter((statement) => !unexpected.has(statement)));
        for (const [statement, what] of unexpected) log.debug(`not a setup call: ${what}`, statement);
        for (const statement of setup) {
            const names = (this.#changed.get(statement) ?? []).map((id) => {
                const { path, key } = placeOf(id);
                return `${path === null ? storage : pathName(path)}.${key}`;
            });
            log.debug(`setup call: defines ${names.join(", ")}`, statement);
        }
        for (const key of facts.setupKeys) {
            const id = placeId(null, key);
            const statement = this.#changedBy.get(id);
            const getter = this.#getter(this.#state.places.get(id) ?? []);
            const called = this.#callAlias(key, getter, statement);
            if (called !== undefined) facts.callAliases.set(key, called);
            else {
                const name = this.#globalRead(getter);
                if (name !== undefined) {
                    facts.globalReads.set(key, name);
                    log.debug(`global read ${storage}.${key}() = globalThis.${name}`, statement);
                }
            }
            const thisFree = this.#thisFree(getter);
            if (thisFree === undefined) facts.thisFreeKeys.add(key);
            else log.debug(`${storage}.${key}(...) may use ${storage} as this: ${thisFree.reason}`, thisFree.node ?? statement);
        }
        return { globalSlots: this.#globalSlots, local: this.#local, setup, ...facts };
    }

    /**
     * What a builtin property the setups left reads as, every time: one builtin or primitive (`undefined` for the value
     * `undefined`), or why it can't be told.
     */
    #reads(descriptors: Descriptors): (AV & { k: "builtin" | "prim" }) | Failure | undefined {
        let values: Values = [];
        for (const descriptor of descriptors) {
            if (descriptor.kind === "absent") return { reason: "the setup may not add it", node: undefined };
            if (descriptor.kind === "data") values = union(values, descriptor.values);
            else {
                const fixed = this.#fixed(descriptor.get);
                if (isFailure(fixed)) return fixed;
                values = union(values, fixed);
            }
        }
        const [only] = values;
        if (values.length !== 1 || (only?.k !== "builtin" && only?.k !== "prim")) return { reason: "it may read as more than one value, or one that changes", node: undefined };
        return only.k === "prim" && only.v === undefined ? undefined : only;
    }

    /** A getter's answers: the same builtins or primitives every time, or why not. */
    #fixed(getters: Values): Values | Failure {
        let values: Values = [];
        for (const getter of getters) {
            if (getter.k === "prim") {
                values = union(values, [UNDEFINED]);
                continue;
            }
            const got = this.#evaluator.call(getter, this.#state, { args: "none", accessor: true });
            if (got instanceof Refusal) return failure(got, "its getter");
            const [read] = this.#evaluator.hostReads;
            if (read !== undefined) return { reason: `its getter reads globalThis.${read}, which may change`, node: undefined };
            if (got.values.some((value) => value.k !== "prim" && value.k !== "builtin")) return { reason: "its getter may hand out a value that changes", node: undefined };
            values = union(values, got.values);
        }
        return values;
    }

    /** A global accessor forwarding the host global its getter reads: the getter reads it and the setter writes it, every time. */
    #hostAlias(alias: string, descriptors: Descriptors, notAlias: Failure, hostAliases: Map<string, string>, statement: Statement | undefined): void {
        const log = this.#cx.log;
        const [only] = descriptors;
        if (descriptors.length !== 1 || only?.kind !== "accessor") return void log.debug(`alias globalThis.${alias}: not taken, ${notAlias.reason}`, notAlias.node ?? statement);
        const proof = this.#forwards(only.get, only.set);
        if (typeof proof === "string") {
            hostAliases.set(alias, proof);
            log.debug(`host alias ${alias} = globalThis.${proof}`, statement);
        } else log.debug(`host alias ${alias}: not taken, ${proof.reason}`, proof.node ?? statement);
    }

    /** The host global a getter reads and hands out, and its setter writes once, every time; or why not. */
    #forwards(getters: Values, setters: Values): string | Failure {
        const [getter] = getters;
        const [setter] = setters;
        if (getters.length !== 1 || getter === undefined || setters.length !== 1 || setter === undefined) return { reason: "it may have more than one getter or setter", node: undefined };
        const got = this.#evaluator.call(getter, this.#state, { args: "none", accessor: true });
        if (got instanceof Refusal) return failure(got, "its getter");
        const reads = [...this.#evaluator.hostReads];
        const [name] = reads;
        if (name === undefined || reads.length > 1)
            return { reason: reads.length === 0 ? "its getter reads no host global" : `its getter reads globalThis.${reads.join(" and globalThis.")}`, node: undefined };
        if (!got.values.every((value) => value.k === "host" && value.name === name)) return { reason: `its getter may hand out something other than globalThis.${name}`, node: undefined };
        const set = this.#evaluator.call(setter, this.#state, { args: "any", accessor: true, forwards: name });
        if (set instanceof Refusal) return failure(set, "its setter");
        if (this.#evaluator.hostReads.size > 0) return { reason: "its setter reads a global", node: undefined };
        if (set.state.hostWrites !== 1) return { reason: `its setter may not write globalThis.${name} exactly once`, node: undefined };
        return name;
    }

    /** The one getter of a storage property the setups left (always installed, one function), or why there is none. */
    #getter(descriptors: Descriptors): AV | Failure {
        const [only] = descriptors;
        if (descriptors.length !== 1 || only?.kind !== "accessor") return { reason: "the setup may leave it other than as one accessor", node: undefined };
        const [getter] = only.get;
        return only.get.length === 1 && getter?.k === "fn" ? getter : { reason: "it may have no getter, or more than one", node: undefined };
    }

    /** The function a storage getter hands out, every time (`G.key` reads as it), with the state its call left; or why not. */
    #handedOut(getter: AV | Failure): { fn: AV; state: State } | Failure {
        if (isFailure(getter)) return getter;
        const got = this.#evaluator.call(getter, this.#state, { args: "none", accessor: true });
        if (got instanceof Refusal) return failure(got, "its getter");
        const [read] = this.#evaluator.hostReads;
        if (read !== undefined) return { reason: `its getter reads globalThis.${read}, which may change`, node: undefined };
        const [only] = got.values;
        return got.values.length === 1 && only?.k === "fn" ? { fn: only, state: got.state } : { reason: "its getter may hand out something other than one function", node: undefined };
    }

    /**
     * `G.key(...)` calls a builtin `B` (found under an owner `O` as `original`): with no arguments it is `B` itself;
     * otherwise per `CallStyle`, for an argument list of any length whose first is `null`, `undefined` or anything else:
     * "static" calls `B` with `this` `O` and every argument; "call" with `this` the first and the rest; "method" calls
     * the first's `original` (dispatching on it) with the rest, and where the first is `null` or `undefined` throws or
     * (`nullishCalls`) does whatever else. In each the one call is all it does, and what it returns is the answer. The
     * function keeps no state between calls, and reads no global that may change.
     */
    #callAlias(key: string, getter: AV | Failure, statement: Statement | undefined): CallAlias | undefined {
        const log = this.#cx.log;
        const { storage, realm } = this.#cx;
        const handed = this.#handedOut(getter);
        if (isFailure(handed)) return void log.debug(`call alias ${storage}.${key}: not taken, ${handed.reason}`, handed.node ?? statement);
        const { fn, state } = handed;
        const bare = this.#evaluator.call(fn, state, { args: "none", accessor: true });
        if (bare instanceof Refusal) return void log.debug(`call alias ${storage}.${key}: not taken, the function its getter hands out: ${bare.reason}`, bare.node ?? statement);
        const [builtin] = bare.values;
        if (bare.values.length !== 1 || builtin?.k !== "builtin" || this.#evaluator.hostReads.size > 0) return undefined;
        const found = realm.holderOf(builtin.path);
        if (found === undefined) return undefined;
        const { owner, name: original } = found;
        const runs: { first: AV; values: Values; made: readonly OutsideCall[] }[] = [];
        for (const args of ["present", "null", "undefined"] as const) {
            const run = this.#evaluator.call(fn, state, { args, accessor: false });
            if (run instanceof Refusal) return void log.debug(`call alias ${storage}.${key}: not taken, the function its getter hands out: ${run.reason}`, run.node ?? statement);
            const [read] = this.#evaluator.hostReads;
            if (read !== undefined) return void log.debug(`call alias ${storage}.${key}: not taken, the function its getter hands out reads globalThis.${read}, which may change`, statement);
            const first: AV = args === "present" ? { k: "arg", index: 0, present: true } : prim(args === "null" ? null : undefined);
            runs.push({ first, values: run.values, made: [...this.#evaluator.calls] });
        }
        /** The run's one call is `expected`, and it returns that call's result. */
        const calls = ({ values, made }: (typeof runs)[number], expected: { callee: AV; self: AV; from: number }): boolean => {
            const [call] = made;
            const [self] = call?.self ?? [];
            const [returned] = values;
            const passed = call?.args;
            return (
                made.length === 1 &&
                call !== undefined &&
                sameValue(call.callee, expected.callee) &&
                call.self.length === 1 &&
                self !== undefined &&
                sameValue(self, expected.self) &&
                passed !== undefined &&
                "from" in passed &&
                passed.from === expected.from &&
                values.length === 1 &&
                returned !== undefined &&
                sameValue(returned, { k: "result", call: 0 })
            );
        };
        const throws = (run: (typeof runs)[number]): boolean => run.values.length === 0 && run.made.length === 0;
        // A builtin that is no function: `O.original(...)` throws (a TypeError) where the function throws.
        const callable = builtin.type === "function";
        const holds: Record<CallStyle, boolean> = {
            static: runs.every((run) => (callable ? calls(run, { callee: builtin, self: { k: "builtin", path: owner, type: "object" }, from: 0 }) : throws(run))),
            call: callable && runs.every((run) => calls(run, { callee: builtin, self: run.first, from: 1 })),
            method: runs.every((run) => run.first.k !== "arg" || calls(run, { callee: { k: "method", index: 0, key: original }, self: run.first, from: 1 })),
        };
        const styles = (Object.keys(holds) as CallStyle[]).filter((style) => holds[style]);
        const [style] = styles;
        if (styles.length !== 1 || style === undefined) {
            log.debug(`call alias ${storage}.${key}(...) hands out ${pathName(owner)}.${original}, but passes arguments on in neither known way; left`, statement);
            return undefined;
        }
        const nullishCalls = style === "method" && !runs.every((run) => run.first.k === "arg" || throws(run));
        const shape = style === "method" ? `x.${original}(...)${nullishCalls ? " where x is neither null nor undefined" : ""}` : `${pathName(owner)}.${original}(...)`;
        log.debug(`call alias ${storage}.${key}(...) = ${shape}`, statement);
        return { key, owner, original, style, nullishCalls };
    }

    /** `G.key()`: the getter hands out a function whose call with no arguments reads one host global and does nothing else. */
    #globalRead(getter: AV | Failure): string | undefined {
        const handed = this.#handedOut(getter);
        if (isFailure(handed)) return undefined;
        const called = this.#evaluator.call(handed.fn, handed.state, { args: "none", accessor: true });
        if (called instanceof Refusal) return undefined;
        const reads = [...this.#evaluator.hostReads];
        const [name] = reads;
        return reads.length === 1 && name !== undefined && called.values.length > 0 && called.values.every((value) => value.k === "host" && value.name === name) ? name : undefined;
    }

    /**
     * `G.key(...)` never uses its `this` (`G`): the getter, which runs with it, doesn't read `this`, and hands out only
     * functions whose calls don't (a builtin would run with `G` as `this`), or primitives (whose call throws first).
     */
    #thisFree(getter: AV | Failure): Failure | undefined {
        if (isFailure(getter)) return getter;
        const got = this.#evaluator.call(getter, this.#state, { args: "none", accessor: true });
        if (got instanceof Refusal) return failure(got, "its getter");
        if (this.#evaluator.usesThis) return { reason: "its getter reads this", node: undefined };
        for (const value of got.values) {
            if (value.k === "prim") continue;
            if (value.k !== "fn") return { reason: "its getter may hand out a function that runs with this", node: undefined };
            const called = this.#evaluator.call(value, got.state, { args: "any", accessor: false, opaqueGlobals: true });
            if (called instanceof Refusal) return failure(called, "the function its getter hands out");
            if (this.#evaluator.usesThis) return { reason: "the function its getter hands out reads this", node: undefined };
        }
        return undefined;
    }
}
