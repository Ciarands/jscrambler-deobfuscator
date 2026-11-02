import type { Expression, FunctionLike, Node } from "../core/ast.js";
import { isFunctionNode, keyName, propertyKey } from "../core/ast.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import { keySets, mayName } from "./key-sets.js";
import type { Slot } from "./runtime/builders.js";
import { returnsOf, sameSlot, slotArray, slotOf } from "./runtime/builders.js";

export interface Effect {
    readonly reason: string;
    readonly node: Node;
}

/**
 * A call the runtime's facts model: `alias`, a call alias `G.k(...)` standing for a builtin (model 7; no arguments give
 * the builtin itself); `own-state`, a call writing only state the runtime keeps for itself (a templated decoder's),
 * giving a primitive or a builtin.
 */
export type RuntimeCall =
    | { readonly kind: "alias"; readonly owner: readonly string[]; readonly original: string; readonly style: "static" | "method" | "call"; readonly nullishCalls: boolean }
    | { readonly kind: "own-state" };

// Own objects are tracked by allocation site so fields keyed by strings read from own arrays stay exact.
/** Non-string primitives. */
const OTHER = 1;
const STRING = 2;
const BUILTIN = 8;
/** Globals, outer variables, the function's own arguments and `this`, caught exceptions. */
const OUTSIDE = 16;
/** A symbol that may be a well-known one (`Symbol.iterator`): as a key it may name an intrinsic. */
const SYMBOL = 32;
const STRING_LIMIT = 32;
const MAX_ROUNDS = 32;

/** Field buckets: one per exact key, one for keys a number (or boolean, null, undefined) gives, one for unknown keys. */
const INDEX = "\u0000index";
const UNKNOWN = "\u0000unknown";

class Kinds {
    bits = 0;
    strings: Set<string> | undefined;
    /** Own objects, by allocation site (a node, or a function's prototype object). */
    sites: Set<object> | undefined;
    args: Set<Node> | undefined;

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

const foreign = (value: Kinds): number => value.bits & (OUTSIDE | BUILTIN);

/** `a + b`: a string only when an operand may be one or an object (converted, model 4: no `valueOf` of the program's). */
const sumOf = (left: Kinds, right: Kinds): Kinds => {
    const stringy = (value: Kinds): boolean => (value.bits & ~OTHER) !== 0 || value.strings !== undefined || value.sites !== undefined || value.args !== undefined;
    return stringy(left) || stringy(right) ? PRIMITIVE_KINDS : OTHER_KINDS;
};

/** Whether a key may be any string: one the function doesn't know exactly, or an object's or a symbol's. */
const unknownKey = (key: Kinds): boolean => (key.bits & (STRING | SYMBOL | BUILTIN | OUTSIDE)) !== 0 || key.sites !== undefined || key.args !== undefined;

const mayBe = (key: Kinds, name: string): boolean => unknownKey(key) || key.strings?.has(name) === true;

const mayBeOneOf = (key: Kinds, names: ReadonlySet<string>): boolean => unknownKey(key) || (key.strings !== undefined && [...key.strings].some((name) => names.has(name)));

/** The key a number, boolean, null or undefined converts to (`"1.5"`, `"true"`): all share one bucket. */
const isPrimitiveKey = (key: string): boolean => key === "true" || key === "false" || key === "null" || key === "undefined" || String(Number(key)) === key;

const bucketOf = (key: string): string => (isPrimitiveKey(key) ? INDEX : key);

const writeBuckets = (key: Kinds): string[] => {
    const buckets = [...(key.strings ?? [])].map(bucketOf);
    if ((key.bits & OTHER) !== 0) buckets.push(INDEX);
    if (unknownKey(key)) buckets.push(UNKNOWN);
    return buckets;
};

// Accessors count as functions: reading one may give an intrinsic (`__proto__`). Relies on model 7: builtins intact.
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

type StaticResult = "other" | "string" | "keys" | "prototype" | "descriptor";

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
            ["getOwnPropertyDescriptor", "descriptor"],
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

/** Keys host code calls a function under, on an object it got as a value: conversions, iteration, thenables, `JSON.stringify`. */
const HOST_CALLED: ReadonlySet<string> = new Set(["valueOf", "toString", "toLocaleString", "toJSON", "then", "next", "return", "throw", "handleEvent"]);

/** The standard library's globals (model 7: the global object holds the builtins under these names). */
const STANDARD_GLOBALS: ReadonlySet<string> = new Set([
    "Object",
    "Function",
    "Array",
    "String",
    "Number",
    "Boolean",
    "Symbol",
    "BigInt",
    "Math",
    "JSON",
    "Date",
    "RegExp",
    "Error",
    "EvalError",
    "RangeError",
    "ReferenceError",
    "SyntaxError",
    "TypeError",
    "URIError",
    "parseInt",
    "parseFloat",
    "isNaN",
    "isFinite",
    "escape",
    "unescape",
    "encodeURI",
    "decodeURI",
    "encodeURIComponent",
    "decodeURIComponent",
]);

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
    const name = scopes.variableOf(node.id);
    return name !== undefined && scopes.staticReferences(name).length === 0;
};

const insideWith = (scope: Scope | null): boolean => {
    for (let s = scope; s !== null; s = s.upper) if (s.type === "with") return true;
    return false;
};

/** Calls defining a property under a key they are passed: the key's argument, by method name (`set`: `Reflect.set`). */
const DEFINING_KEY: Readonly<Record<string, number>> = { defineProperty: 1, set: 1, __defineGetter__: 0, __defineSetter__: 0 };

/**
 * Calls giving their first argument the keys of others, own or inherited: the first such argument, by method name
 * (`Object.assign(o, ...sources)`, `Object.defineProperties(o, descriptors)`, `Object.setPrototypeOf(o, prototype)`).
 */
const COPYING_FROM: Readonly<Record<string, number>> = { assign: 1, defineProperties: 1, setPrototypeOf: 1 };

/** What a variable may hold, written so: objects the program made, never the global object. */
const MADE: Readonly<Record<string, true>> = { ArrayExpression: true, ObjectExpression: true, FunctionExpression: true, ArrowFunctionExpression: true, ClassExpression: true };

/**
 * What a variable holds when every write (a declarator or a plain assignment) gives it an object or array literal or a
 * function: those values; `undefined` otherwise.
 */
const ownValues = (variable: Variable, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>): Node[] | undefined => {
    const references = scopes.references(variable);
    if (references === undefined || !variable.defs.every((def) => def.type === "Variable" || def.type === "FunctionName")) return undefined;
    const values: Node[] = [];
    for (const reference of references) {
        if (!reference.isWrite()) continue;
        const id = reference.identifier as unknown as Node;
        const parent = parents.get(id);
        const value =
            parent?.type === "VariableDeclarator" && parent.id === id
                ? parent.init
                : parent?.type === "AssignmentExpression" && parent.operator === "=" && parent.left === id
                  ? parent.right
                  : undefined;
        if (value === undefined || value === null || MADE[value.type] !== true) return undefined;
        values.push(value);
    }
    return values;
};

/** `Array(...)`, `new Array(...)` (model 7: the builtin), an array literal, or `fill` or `map` called on one: a fresh array. */
const freshArray = (node: Node, scopes: ScopeInfo): boolean => {
    if (node.type === "ArrayExpression") return true;
    if ((node.type === "CallExpression" || node.type === "NewExpression") && node.callee.type === "Identifier") return node.callee.name === "Array" && scopes.isGlobalReference(node.callee);
    if (node.type !== "CallExpression" || node.callee.type !== "MemberExpression") return false;
    const name = propertyKey(node.callee);
    return (name === "fill" || name === "map") && freshArray(node.callee.object, scopes);
};

/** A value that is never the global object: a literal, a function, a primitive an operator gives, a fresh array. */
const notGlobal = (node: Node, scopes: ScopeInfo): boolean =>
    MADE[node.type] === true ||
    node.type === "Literal" ||
    node.type === "TemplateLiteral" ||
    node.type === "UnaryExpression" ||
    node.type === "BinaryExpression" ||
    node.type === "UpdateExpression" ||
    freshArray(node, scopes);

/**
 * A fresh array none of whose own values is the global object (model 7: `fill` fills its receiver, `map` makes a
 * plain array of what its callback returns): an array literal or `Array(...)` of such values, `fill` with one, `map`
 * with a plain function returning only such values.
 */
const freshElements = (node: Node, scopes: ScopeInfo): boolean => {
    if (node.type === "ArrayExpression") return node.elements.every((element) => element === null || notGlobal(element, scopes));
    if (node.type !== "CallExpression" && node.type !== "NewExpression") return false;
    const { callee } = node;
    const args = node.arguments;
    if (callee.type === "Identifier") return freshArray(node, scopes) && args.every((arg) => notGlobal(arg, scopes));
    if (node.type !== "CallExpression" || callee.type !== "MemberExpression" || !freshArray(callee.object, scopes)) return false;
    const name = propertyKey(callee);
    const [first] = args;
    // `fill(v, start, end)` leaves the receiver's values outside `start..end`.
    if (name === "fill") return (first === undefined || notGlobal(first, scopes)) && (args.length <= 1 || freshElements(callee.object, scopes));
    if (name !== "map" || (first?.type !== "FunctionExpression" && first?.type !== "ArrowFunctionExpression") || first.async || (first.type === "FunctionExpression" && first.generator)) return false;
    if (first.body?.type !== "BlockStatement") return first.body !== null && first.body !== undefined && notGlobal(first.body, scopes);
    return returnsOf(first).every((ret) => ret.type === "ReturnStatement" && (ret.argument === null || notGlobal(ret.argument, scopes)));
};

/**
 * `a` in `a[i][k] = v`: written once, by its declarator, with a fresh array none of whose own values is the global
 * object (`freshElements`); read only for one of its properties, never written to one: `a[i]` is one of those values, a
 * number (`length`) or a builtin (inherited, model 7), never the global object.
 */
const freshHolder = (variable: Variable, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, written: ReadonlySet<Node>): boolean => {
    const references = scopes.references(variable);
    const definition = variable.defs.length === 1 ? (variable.defs[0]?.node as unknown as Node) : undefined;
    if (references === undefined || definition?.type !== "VariableDeclarator" || definition.init === null || !freshElements(definition.init, scopes)) return false;
    const method = (member: Node): boolean => {
        const parent = parents.get(member);
        return parent?.type === "CallExpression" && parent.callee === member;
    };
    return references.every((reference) => {
        const id = reference.identifier as unknown as Node;
        if (reference.isWrite()) return id === definition.id && !reference.isRead();
        const element = parents.get(id);
        return element?.type === "MemberExpression" && element.object === id && !written.has(element) && !method(element);
    });
};

const requireMakers = new WeakMap<ScopeInfo, { readonly generation: number; readonly effect: Effect | undefined }>();

/**
 * Why the program may itself make a global `require` (model 10 speaks only of the host's), or `undefined`: a `with`; a
 * write of the bare name; `require` as a static property name or in a string (a write by name,
 * `Object.defineProperty(o, "require", ...)`, code a string hands `eval`); a computed key `key-sets` can't tell from
 * `require` or `__proto__` of a write, of an object literal or class, or of a property-defining call (`DEFINING_KEY`,
 * also through `.call` and `.apply`, and called by a computed name `key-sets` can't tell from every such builtin). The
 * global object may be held anywhere else.
 *
 * A write to a variable only holding objects the program made (`ownValue`), or to a value of a fresh array a variable
 * keeps (`freshHolder`: `a[i][k] = v`), writes no global; but the keys it gives reach the global object where that
 * object is copied there (`COPYING_FROM`, a `__proto__` write or literal property). A copy may take keys only from
 * literals and from variables holding their own objects, whose writes are then checked; any other value refuses.
 */
const requireMaker = (scopes: ScopeInfo): Effect | undefined => {
    const known = requireMakers.get(scopes);
    if (known !== undefined && known.generation === scopes.generation) return known.effect;
    const program = scopes.manager.globalScope?.block as unknown as Node | undefined;
    let effect: Effect | undefined;
    const parents = new Map<Node, Node>();
    const keys: { key: Node; object?: Node }[] = [];
    /** Method calls: the method's member, and the arguments it gets (`undefined` where `apply` hides them). */
    const calls: { call: Node; member: Node & { type: "MemberExpression" }; args: readonly Node[] | undefined }[] = [];
    /** What a copy may take keys from. */
    const sources: Node[] = [];
    /** Members written to. */
    const written = new Set<Node>();
    if (program !== undefined) {
        traverse(program, {
            enter(path) {
                const node = path.node;
                if (path.parent !== null) parents.set(node, path.parent);
                if (effect !== undefined) return;
                const parent = path.parent;
                if (node.type === "WithStatement") effect = { reason: "a with statement may make a name a property", node };
                else if (
                    (node.type === "Literal" && typeof node.value === "string" && node.value.includes("require")) ||
                    (node.type === "TemplateElement" && node.value.cooked?.includes("require") === true)
                )
                    effect = { reason: "a string names require", node };
                else if (node.type === "Identifier" && node.name === "require") {
                    const asKey =
                        (parent?.type === "MemberExpression" && path.key === "property" && !parent.computed) ||
                        ((parent?.type === "Property" || parent?.type === "MethodDefinition" || parent?.type === "PropertyDefinition") && path.key === "key" && !parent.computed);
                    if (asKey) effect = { reason: "it names require as a property", node };
                    else if (path.isWriteTarget() && scopes.staticVariableOf(node) === undefined) effect = { reason: "it writes the global require", node };
                } else if (node.type === "MemberExpression" && path.isWriteTarget()) {
                    written.add(node);
                    if (node.computed && node.property.type !== "Literal") keys.push({ key: node.property, object: node.object });
                    else if (propertyKey(node) === "__proto__") {
                        if (parent?.type === "AssignmentExpression" && parent.operator === "=" && path.key === "left") sources.push(parent.right);
                        else effect = { reason: "a copy takes keys from a value it can't tell", node };
                    }
                } else if ((node.type === "Property" || node.type === "MethodDefinition" || node.type === "PropertyDefinition") && node.computed) keys.push({ key: node.key });
                else if (node.type === "CallExpression" && node.callee.type === "MemberExpression") {
                    // `f.call(self, ...args)` and `f.apply(self, args)` call `f` too.
                    const via = propertyKey(node.callee);
                    const through = (via === "call" || via === "apply") && node.callee.object.type === "MemberExpression";
                    const member = through ? (node.callee.object as Node & { type: "MemberExpression" }) : node.callee;
                    const name = propertyKey(member);
                    if (name === undefined ? member.computed : Object.hasOwn(DEFINING_KEY, name) || Object.hasOwn(COPYING_FROM, name)) {
                        const args = !through ? node.arguments : via === "call" && node.arguments[0]?.type !== "SpreadElement" ? node.arguments.slice(1) : undefined;
                        calls.push({ call: node, member, args });
                    }
                }
            },
        });
    }
    const keySetOf = keySets(scopes, parents);
    for (const { call, member, args } of effect === undefined ? calls : []) {
        const name = propertyKey(member);
        const names = name === undefined ? keySetOf(member.property as Expression) : undefined;
        if (name === undefined && names === undefined) {
            effect ??= { reason: "a call by a computed name may be a property-defining builtin's", node: member.property };
            continue;
        }
        const may = (builtin: string): boolean => (names === undefined ? builtin === name : mayName(names, builtin));
        // `set` only as `Reflect.set`, but the object of a call by a computed name isn't told.
        const reflect = name === undefined || (member.object.type === "Identifier" && member.object.name === "Reflect");
        const defining = Object.keys(DEFINING_KEY).filter((builtin) => may(builtin) && (builtin !== "set" || reflect));
        const copying = Object.keys(COPYING_FROM).filter(may);
        if (defining.length + copying.length === 0) continue;
        if (args === undefined) {
            effect ??= { reason: "a property-defining call's arguments can't be told", node: call };
            continue;
        }
        for (const builtin of defining) {
            const index = DEFINING_KEY[builtin] as number;
            const key = args[index];
            if (args.slice(0, index + 1).some((argument) => argument.type === "SpreadElement")) effect ??= { reason: "a property-defining call's key can't be told", node: call };
            else if (key !== undefined && key.type !== "Literal") keys.push({ key });
        }
        for (const builtin of copying) {
            const from = COPYING_FROM[builtin] as number;
            if (args.slice(0, from).some((argument) => argument.type === "SpreadElement")) effect ??= { reason: "a copy takes keys from a value it can't tell", node: call };
            // `assign` takes every later argument.
            else sources.push(...(builtin === "assign" ? args.slice(from) : args.slice(from, from + 1)));
        }
    }
    /** Variables holding their own objects whose keys a copy takes: their writes stay checked. */
    const sourced = new Set<Variable>();
    for (let i = 0; i < sources.length; i++) {
        const source = sources[i] as Node;
        // A literal's own keys are in the program (computed ones are checked); a spread's, a prototype's and a
        // superclass's are a value's.
        if (source.type === "ObjectExpression") {
            for (const property of source.properties) {
                if (property.type === "SpreadElement") sources.push(property.argument);
                else if (property.kind === "init" && !property.computed && !property.shorthand && !property.method && keyName(property.key) === "__proto__") sources.push(property.value);
            }
            continue;
        }
        if (source.type === "ClassExpression" && source.superClass !== null) sources.push(source.superClass);
        if (MADE[source.type] === true || (source.type === "Literal" && source.value === null)) continue;
        const variable = source.type === "Identifier" ? scopes.staticVariableOf(source) : undefined;
        const values = variable === undefined ? undefined : ownValues(variable, scopes, parents);
        if (variable === undefined || values === undefined) effect ??= { reason: "a copy takes keys from a value it can't tell", node: source };
        else if (!sourced.has(variable)) {
            sourced.add(variable);
            sources.push(...values);
        }
    }
    if (effect === undefined) {
        for (const { key, object } of keys) {
            const variable = object?.type === "Identifier" ? scopes.staticVariableOf(object) : undefined;
            if (variable !== undefined && !sourced.has(variable) && ownValues(variable, scopes, parents) !== undefined) continue;
            const holder = object?.type === "MemberExpression" && object.object.type === "Identifier" ? scopes.staticVariableOf(object.object) : undefined;
            if (holder !== undefined && freshHolder(holder, scopes, parents, written)) continue;
            const set = keySetOf(key as Expression);
            const named = set === undefined ? "require" : ["require", "__proto__"].find((name) => mayName(set, name));
            if (named === undefined) continue;
            effect = { reason: `a computed key that may be ${named}`, node: key };
            break;
        }
    }
    requireMakers.set(scopes, { generation: scopes.generation, effect });
    return effect;
};

const argsKinds = (fn: Node): Kinds => {
    const result = new Kinds();
    result.addArgs(fn);
    return result;
};

class Analysis {
    readonly #fn: Node;
    readonly #allowed: Slot | undefined;
    /** Set when outside code calls what `fn` returns: the path of the call it makes. */
    readonly #called: readonly string[] | undefined;
    readonly #scopes: ScopeInfo;
    readonly #parents: ReadonlyMap<Node, Node>;
    readonly #isGlobalRead: (call: Node) => boolean;
    readonly #runtimeCall: ((call: Node) => RuntimeCall | undefined) | undefined;
    /** `f.bind(t, ...a)` results, by the call making them: what calling one calls, with which `this` and leading arguments. */
    readonly #bound = new Map<object, { readonly target: Kinds; readonly self: Kinds; readonly args: Kinds }>();
    /** Bound functions being called (a bound function may end up calling itself). */
    readonly #calling = new Set<object>();
    readonly #fnScope: Scope | null;
    readonly #within = new Map<Scope, boolean>();
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
    /** Functions that may run. A function only held in variables and stringified (the checks' probes) never runs. */
    readonly #live = new Set<Node>();
    readonly #argKinds = new Map<Node, Kinds>();
    readonly #thisKinds = new Map<Node, Kinds>();
    readonly #returns = new Map<Node, Kinds>();
    /** Every own object but the slot arrays: what `this` may be when host code calls an own function implicitly. */
    readonly #allSites = new Kinds();
    /** The statement lists being compiled in the current function, outermost first, at the statement being compiled. */
    #lists: { readonly statements: readonly Node[]; index: number }[] = [];
    /** `#setBefore`'s reads, and the field buckets a `delete` may take off own objects. */
    readonly #setReads: { readonly site: Node; readonly key: string; readonly node: Node }[] = [];
    readonly #deleted = new Map<object, Set<string>>();

    #thisOwner: Node;
    #returnOwner: Node;

    constructor(
        fn: Node,
        allowed: Slot | undefined,
        called: readonly string[] | undefined,
        scopes: ScopeInfo,
        parents: ReadonlyMap<Node, Node>,
        isGlobalRead: (call: Node) => boolean,
        runtimeCall?: (call: Node) => RuntimeCall | undefined
    ) {
        this.#fn = fn;
        this.#allowed = allowed;
        this.#called = called;
        this.#scopes = scopes;
        this.#parents = parents;
        this.#isGlobalRead = isGlobalRead;
        this.#runtimeCall = runtimeCall;
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
            if (this.#called !== undefined) this.#facts.push(() => this.#exposeResult());
            for (let round = 0; ; round++) {
                if (round === MAX_ROUNDS) return { reason: `the analysis didn't settle in ${MAX_ROUNDS} rounds`, node: this.#fn };
                this.#changed = false;
                for (const fact of this.#facts) fact();
                if (!this.#changed) {
                    const lost = this.#setReads.find(({ site, key }) => this.#deleted.get(site)?.has(bucketOf(key)) === true || this.#deleted.get(site)?.has(UNKNOWN) === true);
                    if (lost !== undefined) return { reason: "reads a field a delete may take off, where what its prototype has shows", node: lost.node };
                    return this.#called === undefined ? undefined : this.#calledEffect(this.#called);
                }
            }
        } catch (error) {
            if (error instanceof Refusal) return error.effect;
            throw error;
        }
    }

    /** Outside code may call any function the result reaches, on anything, with primitive arguments. */
    #exposeResult(): void {
        const reached = this.#reach(this.#location(this.#returns, this.#fn));
        this.#markLive(reached);
        const self = union([reached, OUTSIDE_KINDS]);
        for (const site of reached.sites ?? []) {
            if (!this.#functions.has(site)) continue;
            this.#grow(this.#thisOf(site as Node), self);
            this.#grow(this.#argsOf(site as Node), PRIMITIVE_KINDS);
        }
    }

    /** Why calling `path` of the result may run more than its own functions: it may hold a value from outside or a builtin, or an own `apply` (a wrapper calls through `apply`). */
    #calledEffect(path: readonly string[]): Effect | undefined {
        let value = this.#location(this.#returns, this.#fn);
        for (const key of path) value = this.#read(value, exact(key));
        const name = path.length === 0 ? "what it returns" : `${path.join(".")} of what it returns`;
        if (foreign(value) !== 0) return { reason: `${name} may be a function from outside or a builtin`, node: this.#fn };
        for (const site of value.sites ?? []) {
            const apply = new Kinds();
            this.#collectFields(site, exact("apply"), apply, new Set());
            if (apply.bits !== 0 || apply.strings !== undefined || apply.sites !== undefined || apply.args !== undefined) return { reason: `${name} may have an own apply`, node: this.#fn };
        }
        return undefined;
    }

    #grow(target: Kinds, value: Kinds): void {
        if (target.add(value)) this.#changed = true;
    }

    #growField(site: object, bucket: string, value: Kinds): void {
        // Host code calls a function an own object holds only under these keys (conversions, the iteration and
        // thenable protocols, `JSON.stringify`) or a symbol's; any other host call gets the object first (a builtin's
        // argument: `#callBuiltin` marks what it reaches live; anything from outside is refused).
        if (bucket === UNKNOWN || HOST_CALLED.has(bucket)) this.#markLive(value);
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
            const declarator = variable.defs[0]?.node as unknown as Node | undefined;
            const literal = declarator?.type === "VariableDeclarator" && declarator.init?.type === "ArrayExpression" ? declarator.init : undefined;
            // `array`: its slots start as the literal's elements; a spread there is refused when compiling the declaration.
            const init =
                this.#isWithin(variable.scope) && slotArray(variable, this.#scopes.staticReferences(variable), this.#parents, { init: "array", placement: "anywhere", uses: "index" })
                    ? literal
                    : undefined;
            this.#slots.set(variable, init === undefined ? undefined : new Map());
            if (init !== undefined) {
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

    /** What reading `key` of `receiver` may give. Reads (host getters included) have no effects. */
    #read(receiver: Kinds, key: Kinds): Kinds {
        const out = new Kinds();
        if ((receiver.bits & OUTSIDE) !== 0) out.addBits(OUTSIDE);
        if ((receiver.bits & BUILTIN) !== 0) out.addBits(OTHER | STRING | BUILTIN | SYMBOL);
        const namesFunction = mayBeOneOf(key, INTRINSIC_FUNCTIONS);
        const namesValue = mayBeOneOf(key, INTRINSIC_VALUES);
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

    #collectFields(site: object, key: Kinds, out: Kinds, seen: Set<object>): void {
        if (seen.has(site)) return;
        seen.add(site);
        const array = this.#slotSites.get(site);
        if (array !== undefined) {
            for (const slot of this.#slots.get(array)?.values() ?? []) out.add(slot);
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
                const bound = this.#bound.get(site);
                if (bound !== undefined) found.add(union([bound.target, bound.self, bound.args]));
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
        if (this.#allowed !== undefined && sameSlot(this.#allowed, slotOf(target, this.#scopes))) return value;
        const array = this.#slotVariable(target.object);
        const index = propertyKey(target);
        if (array !== undefined && index !== undefined) {
            const location = this.#location(this.#slots.get(array) as Map<string, Kinds>, index);
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
        if (mayBeOneOf(method, ACCESSOR_METHODS)) refuse("may define an accessor", node);
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
        for (const site of reached.sites ?? []) {
            if (this.#slotSites.has(site)) refuse("hands a slot array to a builtin method", node);
            if (this.#bound.has(site)) refuse("hands a bound function to a builtin method", node);
        }
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
        // `f.bind(t)`/`f.toString()` on a value from outside or a bound function: the methods functions inherit, host
        // ones included (model 7, user decision 2026-11-02); they read `f` and make a bound function or a string.
        const name = !unknownKey(method) && (method.bits & OTHER) === 0 && method.strings?.size === 1 ? [...method.strings][0] : undefined;
        const hostReceiver =
            (self.bits & OUTSIDE) !== 0 &&
            (self.bits & ~(OUTSIDE | OTHER)) === 0 &&
            self.strings === undefined &&
            self.args === undefined &&
            [...(self.sites ?? [])].every((site) => this.#bound.has(site) && !this.#fields.has(site));
        if ((callee.bits & OUTSIDE) !== 0 && hostReceiver && node.type === "CallExpression" && (name === "bind" || name === "toString")) {
            if (name === "toString") return kinds(STRING);
            const bound = this.#bound.get(node) ?? { target: new Kinds(), self: new Kinds(), args: new Kinds() };
            this.#bound.set(node, bound);
            this.#grow(bound.target, self);
            this.#grow(bound.self, args);
            this.#grow(bound.args, args);
            return siteKinds(node);
        }
        if ((callee.bits & OUTSIDE) !== 0) refuse("calls a function from outside", node);
        const out = this.#callOwn(callee, self, args, node);
        for (const site of callee.sites ?? []) {
            const bound = this.#bound.get(site);
            if (bound === undefined || this.#calling.has(site)) continue;
            this.#calling.add(site);
            out.add(this.#invoke(bound.target, bound.self, NOTHING, union([bound.args, args]), node));
            this.#calling.delete(site);
        }
        if ((callee.bits & BUILTIN) === 0) return out;
        // `f.bind(t, ...a)` makes a function and does nothing else (model 7); calling it calls `f` with `t` and `a`.
        if (node.type === "CallExpression" && !unknownKey(method) && (method.bits & OTHER) === 0 && method.strings?.size === 1 && method.strings.has("bind")) {
            const bound = this.#bound.get(node) ?? { target: new Kinds(), self: new Kinds(), args: new Kinds() };
            this.#bound.set(node, bound);
            this.#grow(bound.target, self);
            this.#grow(bound.self, args);
            this.#grow(bound.args, args);
            out.add(siteKinds(node));
            return out;
        }
        out.add(this.#callBuiltin(self, method, args, node));
        return out;
    }

    /** A call the runtime's facts model (`RuntimeCall`). */
    #compileRuntimeCall(modeled: RuntimeCall, node: CallNode): Eval {
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        const all = (): Kinds => union(parts.map((part) => part()));
        if (modeled.kind === "own-state") {
            return () => {
                all();
                return kinds(OTHER | STRING | BUILTIN);
            };
        }
        if (parts.length === 0) return () => kinds(BUILTIN);
        const { owner, original, style } = modeled;
        if (style === "static") {
            const result = owner.length === 0 ? undefined : PURE_STATICS.get(owner.join("."))?.get(original);
            if (result !== undefined) return this.#compileStatic(result, all, node);
            const pure = owner.length === 0 ? PURE_FUNCTIONS.get(original) : undefined;
            if (pure === undefined) return refuse(`calls ${[...owner, original].join(".")} through a call alias, which it can't tell`, node);
            return () => {
                all();
                return pure;
            };
        }
        const [receiver, ...rest] = parts;
        const name = exact(original);
        return () => {
            const self = (receiver as Eval)();
            const args = union(rest.map((part) => part()));
            if (modeled.nullishCalls && (self.bits & OTHER) !== 0) refuse("a call alias may call another builtin on a null or undefined receiver", node);
            // `call`: always the builtin; `method`: whatever the receiver has under that name.
            return style === "call" ? this.#callBuiltin(self, name, args, node) : this.#invoke(this.#read(self, name), self, name, args, node);
        };
    }

    #compileArguments(node: CallNode): Eval {
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        return () => union(parts.map((part) => part()));
    }

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
        const modeled = this.#runtimeCall?.(node);
        if (modeled !== undefined) return this.#compileRuntimeCall(modeled, node);
        const inPlace = this.#compileInPlace(node);
        if (inPlace !== undefined) return inPlace;
        const callee = node.callee;
        // Model 10 (user decision 2026-11-02): the script runs in a web page, which has no `require`, unless the program
        // makes one (`requireMaker`). Calling it throws a ReferenceError before the arguments are evaluated; here that
        // throw lands in a handler of this function's own `try`, or a `typeof require` test keeps the call from running
        // at all: either way the call does nothing.
        if (callee.type === "Identifier" && this.#hostGlobal(callee) === "require" && this.#guardedRequire(node)) {
            const maker = requireMaker(this.#scopes);
            if (maker !== undefined) return refuse(`calls require, which the program may make a global: ${maker.reason}`, maker.node);
            return () => NOTHING;
        }
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
        const known = this.#knownCall(node, args);
        if (known !== undefined) return known;
        if (callee.type !== "MemberExpression") {
            const value = this.#compile(callee);
            return () => this.#invoke(value(), OUTSIDE_KINDS, NOTHING, args(), node);
        }
        const array = this.#slotVariable(callee.object);
        const init = array === undefined ? undefined : this.#slotInits.get(array);
        const receiver = init !== undefined ? () => siteKinds(init) : this.#compile(callee.object);
        const value = this.#compileMember(callee);
        const key = this.#compileKey(callee);
        return () => this.#invoke(value(), receiver(), key(), args(), node);
    }

    /** A `require(...)` call that a `try` of this function catches the throw of, or that `typeof require` guards. */
    #guardedRequire(call: Node): boolean {
        const typeofRequire = (test: Node): boolean =>
            test.type === "BinaryExpression" &&
            [test.left, test.right].some(
                (side) => side.type === "UnaryExpression" && side.operator === "typeof" && side.argument.type === "Identifier" && this.#hostGlobal(side.argument) === "require"
            ) &&
            [test.left, test.right].some(
                (side) =>
                    side.type === "Literal" &&
                    ((side.value === "function" && (test.operator === "===" || test.operator === "==")) || (side.value === "undefined" && (test.operator === "!==" || test.operator === "!=")))
            );
        let child: Node = call;
        for (let parent = this.#parents.get(call); parent !== undefined; child = parent, parent = this.#parents.get(parent)) {
            if (isFunctionNode(parent)) return false;
            if (parent.type === "TryStatement" && parent.block === child && parent.handler !== null) return true;
            if (parent.type === "LogicalExpression" && parent.operator === "&&" && parent.right === child && typeofRequire(parent.left)) return true;
            if ((parent.type === "IfStatement" || parent.type === "ConditionalExpression") && parent.consequent === child && typeofRequire(parent.test)) return true;
        }
        return false;
    }

    /**
     * Calls of standard builtins reached by name, through `globalThis` or a variable holding one (`knownGlobal`, model
     * 7): constructors make a fresh object holding their arguments, `Object.defineProperty(ies)` on an own object
     * defines its properties, `C.prototype.m.call(o, ...)` is `o.m(...)` with the builtin `m`.
     */
    #knownCall(node: CallNode, args: Eval): Eval | undefined {
        const callee = node.callee;
        const path = this.#knownGlobal(callee, new Set());
        if (path !== undefined) {
            if (node.type === "CallExpression" && PURE_FUNCTIONS.has(path)) {
                const result = PURE_FUNCTIONS.get(path) as Kinds;
                return () => {
                    args();
                    return result;
                };
            }
            if (PURE_CONSTRUCTORS.has(path)) {
                return () => {
                    this.#growField(node, UNKNOWN, args());
                    return siteKinds(node);
                };
            }
            const dot = path.lastIndexOf(".");
            const result = node.type === "CallExpression" && dot > 0 ? PURE_STATICS.get(path.slice(0, dot))?.get(path.slice(dot + 1)) : undefined;
            if (result !== undefined) return this.#compileStatic(result, args, node);
            if (node.type === "CallExpression" && (path === "Object.defineProperty" || path === "Object.defineProperties")) return this.#compileDefine(node, path === "Object.defineProperties");
            return undefined;
        }
        const method = callee.type === "MemberExpression" ? propertyKey(callee) : undefined;
        if (node.type !== "CallExpression" || callee.type !== "MemberExpression" || (method !== "call" && method !== "apply")) return undefined;
        const target = this.#knownGlobal(callee.object, new Set());
        const name = target?.match(/^[A-Za-z]+\.prototype\.(\w+)$/)?.[1];
        if (name === undefined || ACCESSOR_METHODS.has(name)) return undefined;
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        return () => {
            const [self = OTHER_KINDS, ...rest] = parts.map((part) => part());
            const passed = method === "call" ? union(rest) : this.#read(rest[0] ?? OTHER_KINDS, OTHER_KINDS);
            return this.#callBuiltin(self, exact(name), passed, node);
        };
    }

    /**
     * `Object.defineProperty(o, k, d)`/`Object.defineProperties(o, ds)` on own objects `o` with own descriptors: `o`'s
     * fields get the descriptors' values and what their getters return. Accessors run on any read of `o`, by anyone:
     * they are taken as live, called on `o`, setters with anything `o` may hold.
     */
    #compileDefine(node: CallNode, many: boolean): Eval {
        const parts = node.arguments.map((argument) => (argument.type === "SpreadElement" ? this.#compileSpread(argument.argument) : this.#compile(argument)));
        return () => {
            const [target = OTHER_KINDS, key = OTHER_KINDS, descriptors = OTHER_KINDS] = parts.map((part) => part());
            // `defineProperties` takes the descriptors from its second argument's own properties.
            const listed = new Kinds();
            if (many) {
                if (foreign(key) !== 0 || key.args !== undefined || (key.bits & ~OTHER) !== 0 || key.strings !== undefined) refuse("defines properties from descriptors not its own", node);
                for (const site of key.sites ?? []) this.#collectFields(site, kinds(STRING), listed, new Set());
            } else listed.add(descriptors);
            const keys = many ? kinds(STRING) : key;
            if (foreign(target) !== 0 || target.args !== undefined || target.sites === undefined || foreign(listed) !== 0 || listed.args !== undefined) {
                return refuse("defines properties of something other than its own objects, or from descriptors not its own", node);
            }
            const values = union([this.#read(listed, exact("value")), OTHER_KINDS]);
            for (const accessor of [this.#read(listed, exact("get")), this.#read(listed, exact("set"))]) {
                if (foreign(accessor) !== 0 || accessor.args !== undefined) refuse("defines an accessor from outside", node);
                this.#markLive(accessor);
                for (const site of accessor.sites ?? []) {
                    if (!this.#functions.has(site)) continue;
                    this.#grow(this.#thisOf(site as Node), target);
                    this.#grow(this.#argsOf(site as Node), PRIMITIVE_KINDS);
                    values.add(this.#location(this.#returns, site as Node));
                }
            }
            for (const site of target.sites) this.#store(site, keys, values, node);
            return target;
        };
    }

    /** The standard builtin `node` names (`Error`, `Object.defineProperties`, `Array.prototype.push`), if it surely does (model 7). */
    #knownGlobal(node: Node, seen: Set<Node>): string | undefined {
        if (seen.has(node)) return undefined;
        seen.add(node);
        if (node.type === "SequenceExpression") {
            const last = node.expressions.at(-1);
            return last !== undefined && node.expressions.slice(0, -1).every((e) => e.type === "Literal") ? this.#knownGlobal(last, seen) : undefined;
        }
        if (node.type === "Identifier") {
            const global = this.#hostGlobal(node);
            if (global !== undefined) return STANDARD_GLOBALS.has(global) ? global : undefined;
            const variable = this.#scopes.staticVariableOf(node);
            const declarator = variable?.defs[0]?.node as unknown as Node | undefined;
            if (variable === undefined || variable.defs.length !== 1 || declarator?.type !== "VariableDeclarator" || declarator.init === null) return undefined;
            if (this.#scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length !== 1) return undefined;
            return this.#knownGlobal(declarator.init, seen);
        }
        if (node.type !== "MemberExpression") return undefined;
        const key = propertyKey(node);
        if (key === undefined) return undefined;
        const object = node.object;
        const base = object.type === "Identifier" && this.#hostGlobal(object) === "globalThis" ? undefined : this.#knownGlobal(object, seen);
        const path = base === undefined ? (object.type === "Identifier" && this.#hostGlobal(object) === "globalThis" ? key : undefined) : `${base}.${key}`;
        if (path === undefined || (base === undefined && !STANDARD_GLOBALS.has(path))) return undefined;
        let value: unknown = globalThis;
        for (const part of path.split(".")) {
            const holder = value as Record<string, unknown>;
            if ((typeof value !== "object" && typeof value !== "function") || value === null || !Object.hasOwn(holder, part)) return undefined;
            const descriptor = Object.getOwnPropertyDescriptor(holder, part);
            if (descriptor === undefined || !("value" in descriptor)) return undefined;
            value = descriptor.value;
        }
        return typeof value === "function" || (typeof value === "object" && value !== null) ? path : undefined;
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
                case "descriptor": {
                    // A fresh descriptor (or undefined) holding the property's value or accessors: from outside, or
                    // what an own object holds.
                    const held = kinds(values.bits & OUTSIDE);
                    for (const site of values.sites ?? []) this.#collectFields(site, kinds(STRING), held, new Set());
                    this.#growField(node, UNKNOWN, held);
                    return union([siteKinds(node), OTHER_KINDS]);
                }
                case "prototype": {
                    const out = kinds(OTHER | BUILTIN | (values.bits & OUTSIDE));
                    for (const site of values.sites ?? []) out.add(this.#links.get(site) ?? NOTHING);
                    return out;
                }
            }
        };
    }

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
        const array = this.#slotVariable(node.object);
        const index = propertyKey(node);
        if (array !== undefined && index !== undefined) {
            const location = this.#location(this.#slots.get(array) as Map<string, Kinds>, index);
            return () => union([location, OTHER_KINDS]);
        }
        const own = this.#setBefore(node);
        if (own !== undefined) {
            const key = exact(own.key);
            return () => {
                const out = new Kinds();
                this.#collectFields(own.site, key, out, new Set());
                return out;
            };
        }
        const receiver = this.#compile(node.object);
        const key = this.#compileKey(node);
        return () => this.#read(receiver(), key());
    }

    /**
     * `V.k`, where V's one write is `var V = {...}` and a statement `V.k = e;` ran before this one in the same list,
     * after that declaration (or the declaration before the statement holding that list), all in this function: the
     * literal's own `k`, not what its prototype has under that name. Only a `delete` takes `k` off it again (builtins
     * given the object write only index keys, model 7; anything from outside is refused), which `run` checks.
     */
    #setBefore(node: Node & { type: "MemberExpression" }): { site: Node; key: string } | undefined {
        const key = propertyKey(node);
        if (key === undefined || isPrimitiveKey(key) || node.object.type !== "Identifier") return undefined;
        const variable = this.#scopes.staticVariableOf(node.object);
        const declarator = variable?.defs[0]?.node as unknown as Node | undefined;
        if (variable === undefined || !this.#isWithin(variable.scope) || variable.defs.length !== 1 || declarator?.type !== "VariableDeclarator" || declarator.init?.type !== "ObjectExpression")
            return undefined;
        if (this.#scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length !== 1) return undefined;
        const declares = (statement: Node | undefined): boolean => statement?.type === "VariableDeclaration" && statement.declarations.includes(declarator as never);
        const sets = (statement: Node | undefined): boolean => {
            if (statement?.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return false;
            const left = statement.expression.left;
            return left.type === "MemberExpression" && left.object.type === "Identifier" && this.#scopes.staticVariableOf(left.object) === variable && propertyKey(left) === key;
        };
        for (const [level, { statements, index }] of this.#lists.entries()) {
            const set = statements.findIndex((statement, i) => i < index && sets(statement));
            if (set < 0) continue;
            const declared = statements.slice(0, set).some(declares) || this.#lists.slice(0, level).some((outer) => outer.statements.slice(0, outer.index).some(declares));
            if (!declared) continue;
            this.#setReads.push({ site: declarator.init, key, node });
            return { site: declarator.init, key };
        }
        return undefined;
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
        const [thisOwner, returnOwner, lists] = [this.#thisOwner, this.#returnOwner, this.#lists];
        if (node.type !== "ArrowFunctionExpression") this.#thisOwner = node;
        this.#returnOwner = node;
        this.#lists = [];
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
        this.#lists = lists;
    }

    #compileBody(node: FunctionLike): () => void {
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
            const name = property.computed ? undefined : keyName(property.key);
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
                      const [before, after] = [old(), right()];
                      return operator === "+=" ? sumOf(before, after) : OTHER_KINDS;
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
            const receiverKinds = receiver();
            const keyKinds = key();
            for (const site of receiverKinds.sites ?? []) {
                const buckets = this.#deleted.get(site) ?? new Set<string>();
                for (const bucket of writeBuckets(keyKinds)) buckets.add(bucket);
                this.#deleted.set(site, buckets);
            }
            this.#write(receiverKinds, keyKinds, NOTHING, target);
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
                const [left, right] = [this.#compile(node.left), this.#compile(node.right)];
                if (node.operator === "+") return () => sumOf(left(), right());
                return this.#sequence([left, right], OTHER_KINDS);
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

    #sequence(parts: readonly Eval[], result: Kinds): Eval {
        return () => {
            for (const part of parts) part();
            return result;
        };
    }

    #compileStatements(statements: readonly Node[]): () => void {
        const position = { statements, index: 0 };
        this.#lists.push(position);
        const parts = statements.map((statement, index) => {
            position.index = index;
            return this.#compileStatement(statement);
        });
        this.#lists.pop();
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
 * The first effect calling `fn` may have beyond objects it creates and the slot `allowed`; `undefined` when proven local.
 *
 * Flow-insensitive abstract interpretation to a fixpoint: every location collects every kind of value any of its code
 * may put there, whether or not that code runs. Assumes reads and operator conversions have no effects and modeled
 * host functions behave as specified (model 7: builtins intact). Throws and non-termination aren't effects here
 * (model 5: the environment passes the checks). `isGlobalRead` calls count as reads of a value from outside.
 */
export const localityOf = (fn: Node, allowed: Slot, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, isGlobalRead: (call: Node) => boolean): Effect | undefined =>
    new Analysis(fn, allowed, undefined, scopes, parents, isGlobalRead).run();

/**
 * The first effect calling `fn` may have beyond objects it creates and the runtime's own state (`runtimeCall`'s
 * `own-state` calls); `undefined` when proven local. Analysed as `localityOf`.
 */
export const callLocalityOf = (
    fn: Node,
    scopes: ScopeInfo,
    parents: ReadonlyMap<Node, Node>,
    isGlobalRead: (call: Node) => boolean,
    runtimeCall: (call: Node) => RuntimeCall | undefined
): Effect | undefined => new Analysis(fn, undefined, undefined, scopes, parents, isGlobalRead, runtimeCall).run();

/**
 * The first effect calling `builder`, and then from outside (on anything, with primitive arguments) any function its
 * result reaches, may have beyond its variables and objects those calls create; `undefined` when proven local, and
 * `path` of the result then is one of those functions (if any function: a value from outside or a builtin may be
 * anything). Analysed as `localityOf`.
 */
export const exposedLocalityOf = (builder: Node, path: readonly string[], scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, isGlobalRead: (call: Node) => boolean): Effect | undefined =>
    new Analysis(builder, undefined, path, scopes, parents, isGlobalRead).run();
