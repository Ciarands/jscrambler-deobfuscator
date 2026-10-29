import type { ArrowFunctionExpression, Function as FunctionNode, Node } from "../core/ast.js";
import { propertyKey } from "../core/ast.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import type { Slot } from "./emulate/builders.js";
import { sameSlot, slotOf, slotsOnly } from "./emulate/builders.js";

/** Something a function may do outside its own objects, and where. */
export interface Effect {
    readonly reason: string;
    readonly node: Node;
}

// What a value may be. Objects the function creates are their allocation sites instead of one bit: the scoring code
// keys records by strings it read out of its own arrays, and only per-site fields keep those keys exact.
/** Non-string primitives: numbers, booleans, null, undefined, bigints, symbols the function makes. */
const OTHER = 1;
/** Strings not known exactly. */
const STRING = 2;
/** Intrinsics (builtin prototypes, their methods, constructors): writing to them is an effect. */
const BUILTIN = 8;
/** Anything from outside the function: globals, outer variables, its own arguments and `this`, caught exceptions. */
const OUTSIDE = 16;
/** A symbol that may be a well-known one (`Symbol.iterator`): as a key it may name an intrinsic. */
const SYMBOL = 32;
/** Exact strings kept per value before they become `STRING`. */
const STRING_LIMIT = 32;
/** Fixpoint rounds before the analysis gives up. */
const MAX_ROUNDS = 32;

/** Field buckets: one per exact key, one for keys a number (or boolean, null, undefined) gives, one for unknown keys. */
const INDEX = "\u0000index";
const UNKNOWN = "\u0000unknown";

class Kinds {
    bits = 0;
    /** Exact strings, while `STRING` is unset. */
    strings: Set<string> | undefined;
    /** Own objects, by allocation site (a node, or a function's prototype object). */
    sites: Set<object> | undefined;
    /** The `arguments` objects of these functions. */
    args: Set<Node> | undefined;

    /** Add `other`'s values; whether anything was new. */
    add(other: Kinds): boolean {
        let grew = this.addBits(other.bits);
        if (other.strings !== undefined) for (const value of other.strings) grew = this.addString(value) || grew;
        if (other.sites !== undefined) for (const site of other.sites) grew = this.addSite(site) || grew;
        if (other.args !== undefined) for (const fn of other.args) grew = this.addArgs(fn) || grew;
        return grew;
    }

    addBits(bits: number): boolean {
        const before = this.bits;
        this.bits |= bits;
        if ((this.bits & STRING) !== 0) this.strings = undefined;
        return this.bits !== before;
    }

    addString(value: string): boolean {
        if ((this.bits & STRING) !== 0) return false;
        this.strings ??= new Set();
        if (this.strings.has(value)) return false;
        if (this.strings.size === STRING_LIMIT) return this.addBits(STRING);
        this.strings.add(value);
        return true;
    }

    addSite(site: object): boolean {
        this.sites ??= new Set();
        if (this.sites.has(site)) return false;
        this.sites.add(site);
        return true;
    }

    addArgs(fn: Node): boolean {
        this.args ??= new Set();
        if (this.args.has(fn)) return false;
        this.args.add(fn);
        return true;
    }
}

const kinds = (bits: number): Kinds => {
    const result = new Kinds();
    result.bits = bits;
    return result;
};

const exact = (value: string): Kinds => {
    const result = new Kinds();
    result.addString(value);
    return result;
};

const siteKinds = (site: object): Kinds => {
    const result = new Kinds();
    result.addSite(site);
    return result;
};

const union = (values: readonly Kinds[]): Kinds => {
    const result = new Kinds();
    for (const value of values) result.add(value);
    return result;
};

const NOTHING = new Kinds();
const OTHER_KINDS = kinds(OTHER);
const PRIMITIVE_KINDS = kinds(OTHER | STRING);
const OUTSIDE_KINDS = kinds(OUTSIDE);

/** Whether a value has objects the function didn't create (from outside, or intrinsics). */
const foreign = (value: Kinds): number => value.bits & (OUTSIDE | BUILTIN);

/** Whether a key may be any string: one the function doesn't know exactly, or an object's or a symbol's. */
const unknownKey = (key: Kinds): boolean => (key.bits & (STRING | SYMBOL | BUILTIN | OUTSIDE)) !== 0 || key.sites !== undefined || key.args !== undefined;

const mayBe = (key: Kinds, name: string): boolean => unknownKey(key) || key.strings?.has(name) === true;

const mayName = (key: Kinds, names: ReadonlySet<string>): boolean => unknownKey(key) || (key.strings !== undefined && [...key.strings].some((name) => names.has(name)));

/** The key a number, boolean, null or undefined converts to (`"1.5"`, `"true"`): all share one bucket. */
const isPrimitiveKey = (key: string): boolean => key === "true" || key === "false" || key === "null" || key === "undefined" || String(Number(key)) === key;

const bucketOf = (key: string): string => (isPrimitiveKey(key) ? INDEX : key);

/** The buckets a write with `key` may go to. */
const writeBuckets = (key: Kinds): string[] => {
    const buckets = [...(key.strings ?? [])].map(bucketOf);
    if ((key.bits & OTHER) !== 0) buckets.push(INDEX);
    if (unknownKey(key)) buckets.push(UNKNOWN);
    return buckets;
};

// Property names of the intrinsic prototypes, from the host. Accessors count as functions: reading one may give an
// intrinsic (`__proto__`). Relies on model 7: builtins intact (the program's own run has the host's prototypes).
const INTRINSIC_FUNCTIONS = new Set<string>();
const INTRINSIC_VALUES = new Set<string>(["length", "name", "message", "stack", "lastIndex", "source", "flags", "prototype", "callee"]);
for (const constructor of [Object, Function, Array, String, Number, Boolean, Symbol, BigInt, RegExp, Error, Date]) {
    const prototype = constructor.prototype as object;
    for (const name of Object.getOwnPropertyNames(prototype)) {
        const descriptor = Object.getOwnPropertyDescriptor(prototype, name);
        if (descriptor?.get !== undefined || descriptor?.set !== undefined || typeof descriptor?.value === "function") INTRINSIC_FUNCTIONS.add(name);
        else INTRINSIC_VALUES.add(name);
    }
}

/** Host functions that only read their arguments (converting them, which only reads) and give primitives. Relies on model 7: builtins intact. */
const PURE_FUNCTIONS: ReadonlyMap<string, Kinds> = new Map([
    ...["escape", "unescape", "encodeURI", "decodeURI", "encodeURIComponent", "decodeURIComponent", "atob", "btoa", "String"].map((name) => [name, kinds(STRING)] as const),
    ...["isNaN", "isFinite", "parseInt", "parseFloat", "Number", "Boolean", "Symbol", "BigInt"].map((name) => [name, OTHER_KINDS] as const),
]);

/** What a pure static method gives: a primitive, a fresh array of strings, or a prototype. */
type StaticResult = "other" | "string" | "keys" | "prototype";

const mathFunctions = Object.getOwnPropertyNames(Math).filter((name) => typeof (Math as unknown as Record<string, unknown>)[name] === "function");

/** Static methods that only read their arguments. Relies on model 7: builtins intact. */
const PURE_STATICS: ReadonlyMap<string, ReadonlyMap<string, StaticResult>> = new Map([
    ["Math", new Map<string, StaticResult>(mathFunctions.map((name) => [name, "other"]))],
    [
        "String",
        new Map<string, StaticResult>([
            ["fromCharCode", "string"],
            ["fromCodePoint", "string"],
        ]),
    ],
    [
        "Object",
        new Map<string, StaticResult>([
            ["keys", "keys"],
            ["getOwnPropertyNames", "keys"],
            ["getPrototypeOf", "prototype"],
            ["is", "other"],
        ]),
    ],
    ["Array", new Map<string, StaticResult>([["isArray", "other"]])],
    [
        "Number",
        new Map<string, StaticResult>([
            ["isInteger", "other"],
            ["isFinite", "other"],
            ["isNaN", "other"],
            ["isSafeInteger", "other"],
        ]),
    ],
    ["Date", new Map<string, StaticResult>([["now", "other"]])],
]);

/** Host constructors `new` may call: they make a fresh object holding (only) their arguments. Relies on model 7: builtins intact. */
const PURE_CONSTRUCTORS: ReadonlySet<string> = new Set([
    "Array",
    "RegExp",
    "Date",
    "Error",
    "EvalError",
    "RangeError",
    "ReferenceError",
    "SyntaxError",
    "TypeError",
    "URIError",
    "String",
    "Number",
    "Boolean",
]);

/** Builtin methods with an exact model: `push`/`unshift` (only `Array.prototype` has them) store their arguments. Relies on model 7: builtins intact. */
const STORING_METHODS: ReadonlySet<string> = new Set(["push", "unshift"]);

/** Builtin methods that would install accessors, whose calls on reads and writes the analysis doesn't follow. */
const ACCESSOR_METHODS: ReadonlySet<string> = new Set(["__defineGetter__", "__defineSetter__"]);

type Eval = () => Kinds;
type CallNode = Node & { type: "CallExpression" | "NewExpression" };

class Refusal {
    constructor(readonly effect: Effect) {}
}

const refuse = (reason: string, node: Node): never => {
    throw new Refusal({ reason, node });
};

/** A function whose value nothing can get hold of: anonymous, or a name nothing uses. Invoked where written, it runs only there. */
const isAnonymousFunction = (node: Node, scopes: ScopeInfo): boolean => {
    if (node.type === "ArrowFunctionExpression") return true;
    if (node.type !== "FunctionExpression") return false;
    if (node.id === null) return true;
    return (scopes.variableOf(node.id)?.references.length ?? 1) === 0;
};

/** The property name a non-computed object-literal key gives. */
const literalKey = (key: Node): string | undefined => {
    if (key.type === "Identifier") return key.name;
    if (key.type === "Literal" && (typeof key.value === "string" || typeof key.value === "number")) return String(key.value);
    return undefined;
};

/** Whether a scope sits inside a `with` statement's body. */
const insideWith = (scope: Scope | null): boolean => {
    for (let s = scope; s !== null; s = s.upper) if (s.type === "with") return true;
    return false;
};

const argsKinds = (fn: Node): Kinds => {
    const result = new Kinds();
    result.addArgs(fn);
    return result;
};

class Analysis {
    readonly #fn: Node;
    readonly #allowed: Slot;
    readonly #scopes: ScopeInfo;
    readonly #parents: ReadonlyMap<Node, Node>;
    readonly #isGlobalRead: (call: Node) => boolean;
    readonly #fnScope: Scope | null;
    readonly #within = new Map<Scope, boolean>();
    /** Collected once; each run joins what its code may put where. */
    readonly #facts: (() => void)[] = [];
    #changed = false;

    readonly #variables = new Map<Variable, Kinds>();
    /** Slot arrays, by variable: their slots by index; `undefined` for variables found not to be one. */
    readonly #slots = new Map<Variable, Map<string, Kinds> | undefined>();
    readonly #slotSites = new Map<object, Variable>();
    readonly #slotInits = new Map<Variable, Node>();
    readonly #fields = new Map<object, Map<string, Kinds>>();
    /** Prototypes of own objects that are own objects too (`new f()`, `o.__proto__ = p`). */
    readonly #links = new Map<object, Kinds>();
    readonly #prototypes = new Map<Node, object>();
    readonly #functions = new Set<object>();
    /**
     * Functions that may run: the function itself, ones a call may reach, and ones stored in a field (host code may call
     * those: a `valueOf` an operator converts with). A function only held in variables and turned into its source text
     * (the checks' probes) never runs, so its body's facts don't count.
     */
    readonly #live = new Set<Node>();
    readonly #argKinds = new Map<Node, Kinds>();
    readonly #thisKinds = new Map<Node, Kinds>();
    readonly #returns = new Map<Node, Kinds>();
    /** Every own object but the slot arrays: what `this` may be when host code calls an own function implicitly. */
    readonly #allSites = new Kinds();

    /** The function `this` and `arguments` belong to at the code being compiled, and the one its returns leave. */
    #thisOwner: Node;
    #returnOwner: Node;

    constructor(fn: Node, allowed: Slot, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, isGlobalRead: (call: Node) => boolean) {
        this.#fn = fn;
        this.#allowed = allowed;
        this.#scopes = scopes;
        this.#parents = parents;
        this.#isGlobalRead = isGlobalRead;
        this.#fnScope = scopes.scopeOf(fn);
        this.#thisOwner = fn;
        this.#returnOwner = fn;
    }

    run(): Effect | undefined {
        try {
            this.#live.add(this.#fn);
            this.#compileFunction(this.#fn);
            // Host code may call an own function on any own object (a `valueOf` an operator converts with).
            for (const fn of this.#functions) this.#location(this.#thisKinds, fn as Node).add(union([this.#allSites, PRIMITIVE_KINDS]));
            for (let round = 0; ; round++) {
                if (round === MAX_ROUNDS) return { reason: `the analysis didn't settle in ${MAX_ROUNDS} rounds`, node: this.#fn };
                this.#changed = false;
                for (const fact of this.#facts) fact();
                if (!this.#changed) return undefined;
            }
        } catch (error) {
            if (error instanceof Refusal) return error.effect;
            throw error;
        }
    }

    #grow(target: Kinds, value: Kinds): void {
        if (target.add(value)) this.#changed = true;
    }

    /** Store `value` in a field: functions in it may now be called by host code. */
    #growField(site: object, bucket: string, value: Kinds): void {
        this.#markLive(value);
        this.#grow(this.#field(site, bucket), value);
    }

    #markLive(value: Kinds): void {
        for (const site of value.sites ?? []) {
            if (!this.#functions.has(site) || this.#live.has(site as Node)) continue;
            this.#live.add(site as Node);
            this.#changed = true;
        }
    }

    #location<K>(map: Map<K, Kinds>, key: K): Kinds {
        let location = map.get(key);
        if (location === undefined) {
            location = new Kinds();
            map.set(key, location);
        }
        return location;
    }

    #isWithin(scope: Scope): boolean {
        let known = this.#within.get(scope);
        if (known === undefined) {
            known = scope === this.#fnScope || (scope.upper !== null && this.#isWithin(scope.upper));
            this.#within.set(scope, known);
        }
        return known;
    }

    /** A host global (no declaration in the program, no `with` around the reference) of one of these names. */
    #hostGlobal(node: Node): string | undefined {
        if (node.type !== "Identifier") return undefined;
        const reference = this.#scopes.referenceOf(node);
        if (reference === undefined || this.#scopes.staticVariableOf(node) !== undefined || insideWith(reference.from)) return undefined;
        return node.name;
    }

    /**
     * A variable of the function declared once as an array whose every use is `S[index]` (never handed on, so its
     * slots hold only what is written to them): tracked per slot. Decided on first sight, so code compiled before the
     * declaration (a hoisted function) sees it too.
     */
    #slotVariable(node: Node): Variable | undefined {
        if (node.type !== "Identifier") return undefined;
        const variable = this.#scopes.staticVariableOf(node);
        if (variable === undefined) return undefined;
        if (!this.#slots.has(variable)) {
            const [def] = variable.defs;
            const declarator = def?.node as unknown as Node | undefined;
            const init = declarator?.type === "VariableDeclarator" && declarator.init?.type === "ArrayExpression" ? declarator.init : undefined;
            const isSlotArray = def?.type === "Variable" && init !== undefined && this.#isWithin(variable.scope) && slotsOnly(variable, this.#parents);
            this.#slots.set(variable, isSlotArray ? new Map() : undefined);
            if (isSlotArray) {
                this.#slotSites.set(init, variable);
                this.#slotInits.set(variable, init);
            }
        }
        return this.#slots.get(variable) === undefined ? undefined : variable;
    }

    #argsOf(fn: Node): Kinds {
        return fn === this.#fn ? OUTSIDE_KINDS : this.#location(this.#argKinds, fn);
    }

    #thisOf(fn: Node): Kinds {
        return fn === this.#fn ? OUTSIDE_KINDS : this.#location(this.#thisKinds, fn);
    }

    #field(site: object, bucket: string): Kinds {
        let buckets = this.#fields.get(site);
        if (buckets === undefined) {
            buckets = new Map();
            this.#fields.set(site, buckets);
        }
        return this.#location(buckets, bucket);
    }

    // ---- values ----

    /** What reading `key` of `receiver` may give. Reads (host getters included) have no effects. */
    #read(receiver: Kinds, key: Kinds): Kinds {
        const out = new Kinds();
        if ((receiver.bits & OUTSIDE) !== 0) out.addBits(OUTSIDE);
        if ((receiver.bits & BUILTIN) !== 0) out.addBits(OTHER | STRING | BUILTIN | SYMBOL);
        const namesFunction = mayName(key, INTRINSIC_FUNCTIONS);
        const namesValue = mayName(key, INTRINSIC_VALUES);
        // A string's properties are characters and its length; other primitives have only their prototype's (an
        // accessor there, like a symbol's `description`, gives a string).
        if ((receiver.bits & STRING) !== 0 || receiver.strings !== undefined) out.addBits(OTHER | STRING);
        if ((receiver.bits & (OTHER | STRING | SYMBOL)) !== 0 || receiver.strings !== undefined) out.addBits(OTHER | (namesFunction ? BUILTIN | STRING : 0) | (namesValue ? OTHER | STRING : 0));
        const own = receiver.sites !== undefined || receiver.args !== undefined;
        if (own) out.addBits(OTHER | (namesFunction ? BUILTIN : 0) | (namesValue ? OTHER | STRING : 0));
        if (receiver.sites !== undefined) {
            const seen = new Set<object>();
            for (const site of receiver.sites) this.#collectFields(site, key, out, seen);
            if (mayBe(key, "prototype")) for (const site of receiver.sites) if (this.#functions.has(site)) out.addSite(this.#prototypes.get(site as Node) as object);
        }
        for (const fn of receiver.args ?? []) {
            out.add(this.#argsOf(fn));
            if (mayBe(key, "callee")) out.add(fn === this.#fn ? OUTSIDE_KINDS : siteKinds(fn));
        }
        return out;
    }

    /** The fields `key` may name on `site` and the own objects it inherits from. */
    #collectFields(site: object, key: Kinds, out: Kinds, seen: Set<object>): void {
        if (seen.has(site)) return;
        seen.add(site);
        const slotArray = this.#slotSites.get(site);
        if (slotArray !== undefined) {
            for (const slot of this.#slots.get(slotArray)?.values() ?? []) out.add(slot);
            return;
        }
        const buckets = this.#fields.get(site);
        if (buckets !== undefined) {
            if (unknownKey(key)) {
                for (const bucket of buckets.values()) out.add(bucket);
            } else {
                for (const name of key.strings ?? []) out.add(buckets.get(bucketOf(name)) ?? NOTHING);
                if ((key.bits & OTHER) !== 0) out.add(buckets.get(INDEX) ?? NOTHING);
                out.add(buckets.get(UNKNOWN) ?? NOTHING);
            }
        }
        const links = this.#links.get(site);
        if (links === undefined) return;
        if (mayBe(key, "__proto__")) out.add(links);
        for (const parent of links.sites ?? []) this.#collectFields(parent, key, out, seen);
    }

    /** Everything reachable from `value` through own objects' fields and `arguments` objects (`value` included). */
    #reach(value: Kinds): Kinds {
        const out = union([value]);
        const seen = new Set<object>();
        const seenArgs = new Set<Node>();
        const work = [value];
        for (let next = work.pop(); next !== undefined; next = work.pop()) {
            for (const site of next.sites ?? []) {
                if (seen.has(site)) continue;
                seen.add(site);
                const found = new Kinds();
                this.#collectFields(site, kinds(STRING), found, new Set());
                found.add(this.#links.get(site) ?? NOTHING);
                out.add(found);
                work.push(found);
            }
            for (const fn of next.args ?? []) {
                if (seenArgs.has(fn)) continue;
                seenArgs.add(fn);
                const found = this.#argsOf(fn);
                out.add(found);
                work.push(found);
            }
        }
        return out;
    }

    // ---- writes ----

    /** Put `value` under `key` of `receiver`: allowed on own objects only. */
    #write(receiver: Kinds, key: Kinds, value: Kinds, node: Node): void {
        if ((receiver.bits & OUTSIDE) !== 0) refuse("writes a property of an object from outside", node);
        if ((receiver.bits & BUILTIN) !== 0) refuse("writes a property of a builtin object", node);
        for (const site of receiver.sites ?? []) this.#store(site, key, value, node);
        for (const fn of receiver.args ?? []) {
            if (mayBe(key, "__proto__")) refuse("may set the prototype of an arguments object", node);
            if (fn !== this.#fn) this.#grow(this.#location(this.#argKinds, fn), value);
        }
    }

    #store(site: object, key: Kinds, value: Kinds, node: Node): void {
        if (this.#slotSites.has(site)) refuse("writes a slot array through another reference", node);
        if (mayBe(key, "__proto__") && (value.sites !== undefined || value.args !== undefined || (value.bits & OUTSIDE) !== 0)) {
            if ((value.bits & OUTSIDE) !== 0) refuse("may set an own object's prototype to an object from outside", node);
            if (value.args !== undefined) refuse("may set an own object's prototype to an arguments object", node);
            const links = this.#location(this.#links, site);
            for (const parent of value.sites ?? []) if (links.addSite(parent)) this.#changed = true;
        }
        for (const bucket of writeBuckets(key)) this.#growField(site, bucket, value);
    }

    /** Compile a write of `value` to `target`; the result gives what the assignment evaluates to. */
    #compileWrite(target: Node, value: Eval): Eval {
        if (target.type === "Identifier") {
            const variable = this.#scopes.staticVariableOf(target);
            if (variable === undefined || !this.#isWithin(variable.scope)) refuse(`writes ${target.name}, which isn't its own variable`, target);
            const location = this.#location(this.#variables, variable as Variable);
            return () => {
                const result = value();
                this.#grow(location, result);
                return result;
            };
        }
        if (target.type !== "MemberExpression") return refuse(`writes a ${target.type}`, target);
        if (sameSlot(this.#allowed, slotOf(target, this.#scopes))) return value;
        const slotArray = this.#slotVariable(target.object);
        const index = propertyKey(target);
        if (slotArray !== undefined && index !== undefined) {
            const location = this.#location(this.#slots.get(slotArray) as Map<string, Kinds>, index);
            return () => {
                const result = value();
                this.#grow(location, result);
                return result;
            };
        }
        const receiver = this.#compile(target.object);
        const key = this.#compileKey(target);
        return () => {
            const result = value();
            this.#write(receiver(), key(), result, target);
            return result;
        };
    }

    // ---- calls ----

    /** Calls of own functions: `this` and arguments flow to them, their returns come back. */
    #callOwn(callee: Kinds, self: Kinds, args: Kinds, node: CallNode): Kinds {
        const out = new Kinds();
        this.#markLive(callee);
        for (const site of callee.sites ?? []) {
            if (!this.#functions.has(site)) continue; // calling an object throws
            const fn = site as Node;
            if (node.type === "NewExpression") {
                this.#grow(this.#location(this.#links, node), siteKinds(this.#prototypes.get(fn) as object));
                this.#grow(this.#thisOf(fn), siteKinds(node));
                out.addSite(node);
            } else {
                this.#grow(this.#thisOf(fn), self);
            }
            this.#grow(this.#argsOf(fn), args);
            out.add(this.#location(this.#returns, fn));
        }
        return out;
    }

    /**
     * A builtin method called on `self`. Allowed with nothing from outside or intrinsic in `self` and `args`: it then
     * only touches what they reach (writing anything reachable into any object reachable, calling any own function
     * reachable), or exactly as modeled (`push`).
     */
    #callBuiltin(self: Kinds, method: Kinds, args: Kinds, node: CallNode): Kinds {
        if (node.type === "NewExpression") refuse("constructs with a builtin it can't tell", node);
        if ((self.bits & OUTSIDE) !== 0) refuse("calls a builtin method on an object from outside", node);
        if ((self.bits & BUILTIN) !== 0) refuse("calls a builtin method on a builtin object", node);
        if (foreign(args) !== 0) refuse("passes an object from outside or a builtin to a builtin method", node);
        if (mayName(method, ACCESSOR_METHODS)) refuse("may define an accessor", node);
        const name = !unknownKey(method) && (method.bits & OTHER) === 0 && method.strings?.size === 1 ? [...method.strings][0] : undefined;
        if (name !== undefined && STORING_METHODS.has(name) && self.args === undefined) {
            for (const site of self.sites ?? []) this.#store(site, OTHER_KINDS, args, node);
            return OTHER_KINDS;
        }
        // RegExp.prototype.test calls the receiver's `exec`: exact only for regexes with no fields written. Relies on
        // model 7: builtins intact.
        if (name === "test" && [...(self.sites ?? [])].every((site) => !this.#fields.has(site))) return OTHER_KINDS;
        const reached = this.#reach(union([self, args]));
        this.#markLive(reached);
        for (const site of reached.sites ?? []) if (this.#slotSites.has(site)) refuse("hands a slot array to a builtin method", node);
        const returned = new Kinds();
        for (const site of reached.sites ?? []) {
            if (!this.#functions.has(site)) continue;
            this.#grow(this.#thisOf(site as Node), reached);
            this.#grow(this.#argsOf(site as Node), reached);
            returned.add(this.#location(this.#returns, site as Node));
        }
        const stored = union([reached, returned]);
        for (const site of reached.sites ?? []) this.#growField(site, UNKNOWN, stored);
        for (const fn of reached.args ?? []) if (fn !== this.#fn) this.#grow(this.#location(this.#argKinds, fn), stored);
        this.#growField(node, UNKNOWN, stored);
        return union([siteKinds(node), stored, kinds(OTHER | STRING | BUILTIN)]);
    }

    #invoke(callee: Kinds, self: Kinds, method: Kinds, args: Kinds, node: CallNode): Kinds {
        if ((callee.bits & OUTSIDE) !== 0) refuse("calls a function from outside", node);
        const out = this.#callOwn(callee, self, args, node);
        if ((callee.bits & BUILTIN) !== 0) out.add(this.#callBuiltin(self, method, args, node));
        return out;
    }

    #compileArguments(node: CallNode): Eval {
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        return () => union(parts.map((part) => part()));
    }

    /** The elements of an own iterable (for-of, spread): its fields, or characters of a string. */
    #compileSpread(node: Node): Eval {
        const value = this.#compile(node);
        return () => {
            const iterable = value();
            if (foreign(iterable) !== 0) refuse("iterates an object from outside or a builtin", node);
            return union([this.#read(iterable, kinds(STRING)), PRIMITIVE_KINDS]);
        };
    }

    /** `(function () {...})(...)`, `.call`/`.apply` of one, `new function () {...}`: its `this` and arguments are exact. */
    #compileInPlace(node: CallNode): Eval | undefined {
        const callee = node.callee;
        const direct = isAnonymousFunction(callee, this.#scopes);
        const method = callee.type === "MemberExpression" && node.type === "CallExpression" && isAnonymousFunction(callee.object, this.#scopes) ? propertyKey(callee) : undefined;
        if (!direct && method !== "call" && method !== "apply") return undefined;
        const fn = (direct ? callee : (callee as Node & { type: "MemberExpression" }).object) as Node;
        this.#compileFunction(fn);
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        const returns = this.#location(this.#returns, fn);
        return () => {
            const values = parts.map((part) => part());
            let self: Kinds;
            let args: Kinds;
            if (direct) {
                self = node.type === "NewExpression" ? siteKinds(node) : OUTSIDE_KINDS; // sloppy `this` is the global object
                args = union(values);
            } else {
                const [first = OTHER_KINDS, ...rest] = values;
                // A `this` of undefined or null is the global object in sloppy code.
                self = (first.bits & OTHER) !== 0 ? union([first, OUTSIDE_KINDS]) : first;
                args = method === "call" ? union(rest) : this.#read(rest[0] ?? OTHER_KINDS, OTHER_KINDS);
            }
            this.#grow(this.#thisOf(fn), self);
            this.#grow(this.#argsOf(fn), args);
            this.#markLive(siteKinds(fn));
            if (node.type === "NewExpression") {
                this.#grow(this.#location(this.#links, node), siteKinds(this.#prototypes.get(fn) as object));
                return union([self, returns]);
            }
            return union([returns, OTHER_KINDS]);
        };
    }

    #compileCall(node: CallNode): Eval {
        // A call the caller proved to read a global property (a setup getter's): a read, giving a value from outside.
        if (this.#isGlobalRead(node)) return () => OUTSIDE_KINDS;
        const inPlace = this.#compileInPlace(node);
        if (inPlace !== undefined) return inPlace;
        const callee = node.callee;
        const args = this.#compileArguments(node);
        const isNew = node.type === "NewExpression";

        const global = this.#hostGlobal(callee);
        if (global !== undefined && !isNew && PURE_FUNCTIONS.has(global)) {
            const result = PURE_FUNCTIONS.get(global) as Kinds;
            return () => {
                args();
                return result;
            };
        }
        if (global !== undefined && isNew && PURE_CONSTRUCTORS.has(global)) {
            return () => {
                this.#growField(node, UNKNOWN, args());
                return siteKinds(node);
            };
        }
        if (callee.type === "MemberExpression" && !isNew) {
            const owner = this.#hostGlobal(callee.object);
            const name = propertyKey(callee);
            const result = owner === undefined || name === undefined ? undefined : PURE_STATICS.get(owner)?.get(name);
            if (result !== undefined) return this.#compileStatic(result, args, node);
        }
        if (callee.type !== "MemberExpression") {
            const value = this.#compile(callee);
            return () => this.#invoke(value(), OUTSIDE_KINDS, NOTHING, args(), node);
        }
        const slotArray = this.#slotVariable(callee.object);
        const init = slotArray === undefined ? undefined : this.#slotInits.get(slotArray);
        const receiver = init !== undefined ? () => siteKinds(init) : this.#compile(callee.object);
        const value = this.#compileMember(callee);
        const key = this.#compileKey(callee);
        return () => this.#invoke(value(), receiver(), key(), args(), node);
    }

    #compileStatic(result: StaticResult, args: Eval, node: CallNode): Eval {
        return () => {
            const values = args();
            switch (result) {
                case "other":
                    return OTHER_KINDS;
                case "string":
                    return kinds(STRING);
                case "keys":
                    this.#growField(node, INDEX, kinds(STRING));
                    return siteKinds(node);
                case "prototype": {
                    const out = kinds(OTHER | BUILTIN | (values.bits & OUTSIDE));
                    for (const site of values.sites ?? []) out.add(this.#links.get(site) ?? NOTHING);
                    return out;
                }
            }
        };
    }

    // ---- expressions ----

    #compileKey(node: Node & { type: "MemberExpression" }): Eval {
        if (node.property.type === "PrivateIdentifier") return refuse("uses a private name", node);
        if (!node.computed) {
            const key = exact(node.property.type === "Identifier" ? node.property.name : "");
            return () => key;
        }
        return this.#compile(node.property);
    }

    #compileMember(node: Node & { type: "MemberExpression" }): Eval {
        if (node.property.type === "PrivateIdentifier") return refuse("uses a private name", node);
        const slotArray = this.#slotVariable(node.object);
        const index = propertyKey(node);
        if (slotArray !== undefined && index !== undefined) {
            const location = this.#location(this.#slots.get(slotArray) as Map<string, Kinds>, index);
            return () => union([location, OTHER_KINDS]);
        }
        const receiver = this.#compile(node.object);
        const key = this.#compileKey(node);
        return () => this.#read(receiver(), key());
    }

    #compileIdentifier(node: Node & { type: "Identifier" }): Eval {
        const variable = this.#scopes.staticVariableOf(node);
        if (variable === undefined) {
            const global = this.#hostGlobal(node);
            const constant = global === "undefined" || global === "NaN" || global === "Infinity";
            return () => (constant ? OTHER_KINDS : OUTSIDE_KINDS);
        }
        if (!this.#isWithin(variable.scope)) return () => OUTSIDE_KINDS;
        if (this.#slotVariable(node) !== undefined) return refuse(`uses the slot array ${node.name} as a value`, node);
        const location = this.#location(this.#variables, variable);
        const parts: Kinds[] = [location, OTHER_KINDS];
        if (variable.defs.length === 0) parts.push(argsKinds(variable.scope.block as unknown as Node)); // `arguments`
        for (const def of variable.defs) {
            if (def.type === "Parameter") parts.push(this.#argsOf(def.node as unknown as Node));
            else if (def.type === "FunctionName") parts.push(siteKinds(def.node as unknown as object));
            else if (def.type === "CatchClause") parts.push(OUTSIDE_KINDS);
            else if (def.type !== "Variable") refuse(`uses a ${def.type} binding`, node);
        }
        return () => union(parts);
    }

    #compileFunctionValue(node: Node): Eval {
        this.#compileFunction(node);
        return () => siteKinds(node);
    }

    /**
     * Register an own function (its object, prototype, and body's facts). What its code can't do counts only once it
     * may run: a refusal while compiling it is deferred to a fact that refuses when the function is live.
     */
    #compileFunction(node: Node): void {
        if (node.type !== "FunctionExpression" && node.type !== "FunctionDeclaration" && node.type !== "ArrowFunctionExpression") return void refuse(`unsupported function ${node.type}`, node);
        if (this.#functions.has(node)) return;
        if (node !== this.#fn) {
            this.#functions.add(node);
            this.#allSites.addSite(node);
            const prototype = {};
            this.#prototypes.set(node, prototype);
            this.#allSites.addSite(prototype);
            this.#field(prototype, "constructor").addSite(node);
        }
        const [thisOwner, returnOwner] = [this.#thisOwner, this.#returnOwner];
        if (node.type !== "ArrowFunctionExpression") this.#thisOwner = node;
        this.#returnOwner = node;
        let body: () => void;
        try {
            body = this.#compileBody(node);
        } catch (error) {
            if (!(error instanceof Refusal) || node === this.#fn) throw error;
            body = () => {
                throw error;
            };
        }
        this.#facts.push(() => {
            if (this.#live.has(node)) body();
        });
        this.#thisOwner = thisOwner;
        this.#returnOwner = returnOwner;
    }

    #compileBody(node: FunctionNode | ArrowFunctionExpression): () => void {
        if (node.async || (node.type !== "ArrowFunctionExpression" && node.generator)) refuse("has an async or generator function", node);
        for (const param of node.params) if (param.type !== "Identifier") refuse("has a destructuring, default or rest parameter", param);
        const body = node.body;
        if (body === null) return refuse("has a function without a body", node);
        if (body.type === "BlockStatement") return this.#compileStatements(body.body);
        const value = this.#compile(body);
        const returns = this.#location(this.#returns, node);
        return () => this.#grow(returns, value());
    }

    #compileObject(node: Node & { type: "ObjectExpression" }): Eval {
        const parts = node.properties.map((property): (() => void) => {
            if (property.type === "SpreadElement") {
                const elements = this.#compileSpread(property.argument);
                return () => this.#store(node, kinds(STRING), elements(), property);
            }
            if (property.kind !== "init") return refuse("defines an accessor", property);
            const value =
                property.value.type === "FunctionExpression" || property.value.type === "ArrowFunctionExpression" ? this.#compileFunctionValue(property.value) : this.#compile(property.value);
            const name = property.computed ? undefined : literalKey(property.key);
            const key = property.computed ? this.#compile(property.key) : () => exact(name ?? "");
            // `{ __proto__: v }` sets the prototype; a computed `["__proto__"]` defines a field.
            const setsPrototype = !property.computed && !property.shorthand && !property.method && name === "__proto__";
            return () => {
                const keyKinds = key();
                const result = value();
                if (setsPrototype) this.#store(node, keyKinds, result, property);
                else for (const bucket of writeBuckets(keyKinds)) this.#growField(node, bucket, result);
            };
        });
        this.#allSites.addSite(node);
        return () => {
            for (const part of parts) part();
            return siteKinds(node);
        };
    }

    #compileArray(node: Node & { type: "ArrayExpression" }): Eval {
        const parts = node.elements.flatMap((element) => (element === null ? [] : [element.type === "SpreadElement" ? this.#compileSpread(element.argument) : this.#compile(element)]));
        this.#allSites.addSite(node);
        return () => {
            this.#growField(node, INDEX, union(parts.map((part) => part())));
            return siteKinds(node);
        };
    }

    #compileAssignment(node: Node & { type: "AssignmentExpression" }): Eval {
        const right = this.#compile(node.right);
        const operator = node.operator;
        if (operator === "=") return this.#compileWrite(node.left, right);
        if (node.left.type !== "Identifier" && node.left.type !== "MemberExpression") return refuse("writes a destructuring target", node.left);
        const old = this.#compile(node.left);
        const value: Eval =
            operator === "||=" || operator === "&&=" || operator === "??="
                ? () => union([old(), right()])
                : () => {
                      old();
                      right();
                      return operator === "+=" ? PRIMITIVE_KINDS : OTHER_KINDS;
                  };
        return this.#compileWrite(node.left, value);
    }

    #compileDelete(node: Node & { type: "UnaryExpression" }): Eval {
        const target = node.argument;
        if (target.type === "Identifier") {
            const variable = this.#scopes.staticVariableOf(target);
            if (variable === undefined || !this.#isWithin(variable.scope)) refuse(`deletes ${target.name}, which isn't its own variable`, target);
            return () => OTHER_KINDS;
        }
        if (target.type !== "MemberExpression") {
            const value = this.#compile(target);
            return () => {
                value();
                return OTHER_KINDS;
            };
        }
        if (this.#slotVariable(target.object) !== undefined) return refuse("deletes a slot", target);
        const receiver = this.#compile(target.object);
        const key = this.#compileKey(target);
        return () => {
            this.#write(receiver(), key(), NOTHING, target);
            return OTHER_KINDS;
        };
    }

    #compile(node: Node): Eval {
        switch (node.type) {
            case "Literal": {
                if ("regex" in node && node.regex !== undefined && node.regex !== null) {
                    this.#allSites.addSite(node);
                    return () => siteKinds(node);
                }
                const value = typeof node.value === "string" ? exact(node.value) : OTHER_KINDS;
                return () => value;
            }
            case "Identifier":
                return this.#compileIdentifier(node);
            case "ThisExpression": {
                const owner = this.#thisOwner;
                return () => this.#thisOf(owner);
            }
            case "ArrayExpression":
                return this.#compileArray(node);
            case "ObjectExpression":
                return this.#compileObject(node);
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return this.#compileFunctionValue(node);
            case "TemplateLiteral": {
                const parts = node.expressions.map((expression) => this.#compile(expression));
                return () => {
                    for (const part of parts) part();
                    return kinds(STRING);
                };
            }
            case "UnaryExpression": {
                if (node.operator === "delete") return this.#compileDelete(node);
                const argument = this.#compile(node.argument);
                const result = node.operator === "typeof" ? kinds(STRING) : OTHER_KINDS;
                return () => {
                    argument();
                    return result;
                };
            }
            case "UpdateExpression":
                if (node.argument.type !== "Identifier" && node.argument.type !== "MemberExpression") return refuse(`updates a ${node.argument.type}`, node);
                return this.#compileWrite(node.argument, this.#sequence([this.#compile(node.argument)], OTHER_KINDS));
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier") return refuse("uses a private name", node);
                const result = node.operator === "+" ? PRIMITIVE_KINDS : OTHER_KINDS;
                return this.#sequence([this.#compile(node.left), this.#compile(node.right)], result);
            }
            case "LogicalExpression": {
                const [left, right] = [this.#compile(node.left), this.#compile(node.right)];
                return () => union([left(), right()]);
            }
            case "ConditionalExpression": {
                const [test, consequent, alternate] = [this.#compile(node.test), this.#compile(node.consequent), this.#compile(node.alternate)];
                return () => {
                    test();
                    return union([consequent(), alternate()]);
                };
            }
            case "SequenceExpression": {
                const parts = node.expressions.map((expression) => this.#compile(expression));
                return () => {
                    let last = OTHER_KINDS;
                    for (const part of parts) last = part();
                    return last;
                };
            }
            case "AssignmentExpression":
                return this.#compileAssignment(node);
            case "MemberExpression":
                return this.#compileMember(node);
            case "ChainExpression": {
                const expression = this.#compile(node.expression);
                return () => union([expression(), OTHER_KINDS]);
            }
            case "CallExpression":
            case "NewExpression":
                if (node.callee.type === "Super") return refuse("calls super", node);
                return this.#compileCall(node);
            case "MetaProperty":
                return () => OUTSIDE_KINDS;
            default:
                return refuse(`has a ${node.type}, which the analysis doesn't follow`, node);
        }
    }

    /** Evaluate `parts` for their effects; give `result`. */
    #sequence(parts: readonly Eval[], result: Kinds): Eval {
        return () => {
            for (const part of parts) part();
            return result;
        };
    }

    // ---- statements ----

    #compileStatements(statements: readonly Node[]): () => void {
        const parts = statements.map((statement) => this.#compileStatement(statement));
        return () => {
            for (const part of parts) part();
        };
    }

    #compileDeclaration(node: Node & { type: "VariableDeclaration" }): () => void {
        const parts = node.declarations.map((declarator): (() => void) => {
            if (declarator.id.type !== "Identifier") return refuse("declares a destructuring target", declarator.id);
            const init = declarator.init;
            if (init === null) return () => undefined;
            const variable = this.#slotVariable(declarator.id);
            const slots = variable === undefined ? undefined : this.#slots.get(variable);
            if (slots !== undefined && init.type === "ArrayExpression" && this.#slotInits.get(variable as Variable) === init) {
                // A slot array: tracked per index, from its initial elements on.
                const elements = init.elements.map((element, index) => {
                    if (element?.type === "SpreadElement") return refuse("spreads into a slot array", element);
                    const value = element === null ? undefined : this.#compile(element);
                    const location = this.#location(slots, String(index));
                    return value === undefined ? undefined : () => this.#grow(location, value());
                });
                return () => {
                    for (const element of elements) element?.();
                };
            }
            const write = this.#compileWrite(declarator.id, this.#compile(init));
            return () => void write();
        });
        return () => {
            for (const part of parts) part();
        };
    }

    #compileLoopTarget(left: Node, value: Eval): () => void {
        if (left.type === "VariableDeclaration") {
            const [declarator] = left.declarations;
            if (declarator === undefined || declarator.id.type !== "Identifier") return refuse("declares a destructuring target", left);
            const write = this.#compileWrite(declarator.id, value);
            return () => void write();
        }
        const write = this.#compileWrite(left, value);
        return () => void write();
    }

    #compileStatement(node: Node): () => void {
        switch (node.type) {
            case "ExpressionStatement": {
                const expression = this.#compile(node.expression);
                return () => void expression();
            }
            case "VariableDeclaration":
                return this.#compileDeclaration(node);
            case "FunctionDeclaration":
                this.#compileFunction(node);
                return () => undefined;
            case "ReturnStatement": {
                const returns = this.#location(this.#returns, this.#returnOwner);
                if (node.argument === null) return () => undefined;
                const value = this.#compile(node.argument);
                return () => this.#grow(returns, value());
            }
            case "ThrowStatement": {
                const value = this.#compile(node.argument);
                return () => {
                    const thrown = value();
                    if (thrown.sites !== undefined || thrown.args !== undefined) refuse("throws an own object, which may leave the function", node);
                };
            }
            case "BlockStatement":
                return this.#compileStatements(node.body);
            case "IfStatement":
                return this.#compileParts([node.test, node.consequent, node.alternate]);
            case "WhileStatement":
            case "DoWhileStatement":
                return this.#compileParts([node.test, node.body]);
            case "ForStatement":
                return this.#compileParts([node.init, node.test, node.update, node.body]);
            case "ForInStatement": {
                const right = this.#compile(node.right); // enumerating keys only reads
                const left = this.#compileLoopTarget(node.left, () => kinds(STRING));
                const body = this.#compileStatement(node.body);
                return () => {
                    right();
                    left();
                    body();
                };
            }
            case "ForOfStatement": {
                if (node.await) return refuse("has for await", node);
                const left = this.#compileLoopTarget(node.left, this.#compileSpread(node.right));
                const body = this.#compileStatement(node.body);
                return () => {
                    left();
                    body();
                };
            }
            case "LabeledStatement":
                return this.#compileStatement(node.body);
            case "SwitchStatement":
                return this.#compileParts([node.discriminant, ...node.cases.flatMap((c) => [c.test, ...c.consequent])]);
            case "TryStatement": {
                if (node.handler?.param !== null && node.handler?.param !== undefined && node.handler.param.type !== "Identifier")
                    return refuse("catches into a destructuring target", node.handler.param);
                return this.#compileParts([node.block, node.handler?.body, node.finalizer]);
            }
            case "EmptyStatement":
            case "BreakStatement":
            case "ContinueStatement":
            case "DebuggerStatement":
                return () => undefined;
            default:
                return refuse(`has a ${node.type}, which the analysis doesn't follow`, node);
        }
    }

    /** Statements and expressions in a list (missing ones skipped), for their effects. */
    #compileParts(parts: readonly (Node | null | undefined)[]): () => void {
        const compiled = parts.flatMap((part): (() => void)[] => {
            if (part === null || part === undefined) return [];
            if (part.type === "VariableDeclaration" || part.type.endsWith("Statement") || part.type === "FunctionDeclaration") return [this.#compileStatement(part)];
            const value = this.#compile(part);
            return [() => void value()];
        });
        return () => {
            for (const part of compiled) part();
        };
    }
}

/**
 * Whether calling `fn` changes nothing but objects it creates and the slot `allowed` (`undefined`: proven), or the
 * first effect found. `parents` covers the subtree its slot arrays are declared in.
 *
 * A flow-insensitive abstract interpretation to a fixpoint: every location (the function's own variables, its slot
 * arrays per index, the fields of each own object by allocation site and key, each own function's `this`, arguments
 * and returns) collects every kind of value any of its code may put there, whether or not that code runs. Values from
 * outside (globals, outer variables, the function's own `this` and arguments) and intrinsics are tracked as such; the
 * function may write only to its own variables, slot arrays and own objects, call only own functions, pure host
 * functions and builtin methods on own objects and primitives with nothing from outside, and construct only own
 * functions and plain host constructors.
 *
 * Assumptions: reads have no effects (host getters included), and operators only read (conversions of host objects
 * included); the host functions and methods it models behave as specified (relies on model 7: builtins intact).
 * Thrown exceptions and loops that don't end aren't effects here: whether the function completes is the caller's
 * question (model 5: the environment passes the checks). `isGlobalRead` names calls known to do nothing but read a
 * global property (the runtime's global-read getters): they count as reads of a value from outside.
 */
export const localityOf = (fn: Node, allowed: Slot, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, isGlobalRead: (call: Node) => boolean): Effect | undefined =>
    new Analysis(fn, allowed, scopes, parents, isGlobalRead).run();
