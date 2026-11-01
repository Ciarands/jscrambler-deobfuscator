import type { ArrowFunctionExpression, Function as FunctionNode } from "./ast.js";
import type { Value } from "./evaluate.js";

/**
 * The values `interpret.ts` computes with, and the builtins it models. Builtins act on primitives with the host's own
 * builtins (model 7: the program's builtins are intact, and both follow the spec); on the interpreter's objects they
 * are written out here. What isn't modelled refuses: a member a value doesn't have in the modelled surface, a
 * conversion that would run program code (`toString`, `valueOf` own properties), approximated or engine-dependent
 * results (`Math.sin`, `toString(radix)` of fractions, locale methods, sorts with comparators), and writes the
 * program's sloppy and strict modes treat differently.
 */

/** A function of the interpreted code, closed over an interpreter environment (`null`: names it doesn't declare are outer). */
export class Closure {
    constructor(
        readonly node: FunctionNode | ArrowFunctionExpression,
        readonly env: object | null
    ) {}
}

/** `shape` counts changes to which keys exist (for-in refuses when they change under it). */
export class ArrayObject {
    shape = 0;
    frozen = false;
    constructor(readonly items: JsValue[]) {}
}

export class PlainObject {
    readonly props = new Map<string, JsValue>();
    shape = 0;
    frozen = false;
}

export class Bound {
    constructor(
        readonly target: JsValue,
        readonly self: JsValue,
        readonly args: readonly JsValue[]
    ) {}
}

export type NativeCall = (self: JsValue, args: readonly JsValue[], run: Run) => JsValue;

/** A builtin: a function when it has `call`, else a namespace. `name` is its path (`Math`, `String.prototype`): aliases are looked up under it. */
export class Native {
    readonly members = new Map<string, JsValue>();
    constructor(
        readonly name: string,
        readonly call?: NativeCall,
        readonly construct?: (args: readonly JsValue[], run: Run) => JsValue
    ) {}
}

export type JsObject = Closure | ArrayObject | PlainObject | Bound | Native;
export type JsValue = Value | JsObject;

/** The program throws here (no `try` is interpreted, so the call has no value). */
export class Thrown {
    constructor(readonly message: string) {}
}

/** Outside the modelled subset. */
export class Refused {
    constructor(readonly reason: string) {}
}

/** Thrown when the step budget runs out. */
export const EXHAUSTED: unique symbol = Symbol("exhausted");

/** What builtins need from the interpreter. */
export interface Run {
    /** Charges `count` steps against the budget. */
    step(count: number): void;
    call(callee: JsValue, self: JsValue, args: readonly JsValue[]): JsValue;
    /** The original name an alias stands for on `owner` (`String.prototype`), if any. */
    aliasOf(owner: string, name: string): string | undefined;
    hasAliases(owner: string): boolean;
}

/** Longest string a call may make: bounds the host memory a call can take. */
export const MAX_STRING = 1 << 22;

export const thrown = (message: string): never => {
    throw new Thrown(message);
};

export const refuse = (reason: string): never => {
    throw new Refused(reason);
};

export const isObject = (v: JsValue): v is JsObject => typeof v === "object" && v !== null;

export const isCallable = (v: JsValue): boolean => v instanceof Closure || v instanceof Bound || (v instanceof Native && v.call !== undefined);

export const typeOf = (v: JsValue): string => (isObject(v) ? (isCallable(v) ? "function" : "object") : v === null ? "object" : typeof v);

export const truthy = (v: JsValue): boolean => isObject(v) || Boolean(v);

const checked = <T>(result: T): T => {
    if (typeof result === "string" && result.length > MAX_STRING) refuse(`it makes a string longer than ${MAX_STRING} characters`);
    return result;
};

/** An array index (`ToString(ToUint32(key)) === key`, below 2^32 - 1), or -1. */
export const arrayIndex = (key: string): number => {
    const n = Number(key);
    return Number.isInteger(n) && n >= 0 && n < 4294967295 && String(n) === key ? n : -1;
};

const isNumericKey = (key: string): boolean => String(Number(key)) === key;

const joining = new Set<ArrayObject>();

const join = (array: ArrayObject, separator: string, run: Run): string => {
    if (joining.has(array)) return refuse("it joins an array that contains itself");
    const items = array.items;
    const length = items.length;
    run.step(length);
    joining.add(array);
    try {
        let out = "";
        for (let i = 0; i < length; i++) {
            if (i > 0) out += separator;
            const item = items[i];
            if (item !== undefined && item !== null) out += toStr(item, run);
            checked(out);
        }
        return out;
    } finally {
        joining.delete(array);
    }
};

/** `ToPrimitive`: arrays join (Array.prototype.toString, model 7), plain objects without own conversions are `[object Object]`. */
export const toPrimitive = (v: JsValue, run: Run): Value => {
    if (!isObject(v)) return v;
    if (v instanceof ArrayObject) return join(v, ",", run);
    if (v instanceof PlainObject) {
        if (v.props.has("toString") || v.props.has("valueOf")) return refuse("it converts an object with its own toString or valueOf");
        return "[object Object]";
    }
    return refuse("it converts a function or builtin to a primitive");
};

export const toStr = (v: JsValue, run: Run): string => String(toPrimitive(v, run));

export const toNum = (v: JsValue, run: Run): number => Number(toPrimitive(v, run));

const primitives = (args: readonly JsValue[], run: Run): Value[] => args.map((arg) => toPrimitive(arg, run));

const OBJECT_PROTOTYPE_NAMES: ReadonlySet<string> = new Set(
    "constructor hasOwnProperty isPrototypeOf propertyIsEnumerable toLocaleString toString valueOf __defineGetter__ __defineSetter__ __lookupGetter__ __lookupSetter__ __proto__".split(" ")
);

const native = (name: string, call: NativeCall, construct?: (args: readonly JsValue[], run: Run) => JsValue): Native => new Native(name, call, construct);

const namespace = (name: string, members: Record<string, JsValue>, call?: NativeCall, construct?: (args: readonly JsValue[], run: Run) => JsValue): Native => {
    const made = new Native(name, call, construct);
    for (const [key, member] of Object.entries(members)) made.members.set(key, member);
    return made;
};

// ---------------------------------------------------------------- Object.prototype, Function.prototype

/** Own properties as the program sees them; functions and builtins refuse (their own `length`/`name` aren't modelled). */
export const hasOwn = (v: JsValue, key: string): boolean => {
    if (v === null || v === undefined) return thrown(`TypeError: cannot convert ${v} to an object`);
    if (typeof v === "string") return key === "length" || (arrayIndex(key) !== -1 && arrayIndex(key) < v.length);
    if (typeof v === "number" || typeof v === "boolean") return false;
    if (v instanceof ArrayObject) {
        const index = arrayIndex(key);
        return key === "length" || (index !== -1 && index in v.items);
    }
    if (v instanceof PlainObject) return v.props.has(key);
    return refuse("it asks for an own property of a function or builtin");
};

const OBJECT_PROTO = namespace("Object.prototype", {
    hasOwnProperty: native("hasOwnProperty", (self, args, run) => {
        const key = toStr(args[0], run);
        return hasOwn(self, key);
    }),
});

const applyArgs = (list: JsValue): JsValue[] => {
    if (list === null || list === undefined) return [];
    if (list instanceof ArrayObject) return Array.from(list.items, (item) => item);
    if (!isObject(list)) return thrown("TypeError: apply's arguments aren't an object");
    return refuse("it applies an array-like that isn't an array");
};

const FUNCTION_PROTO = namespace("Function.prototype", {
    call: native("call", (self, args, run) => run.call(self, args[0], args.slice(1))),
    apply: native("apply", (self, args, run) => {
        if (!isCallable(self)) thrown("TypeError: apply of something that isn't a function");
        return run.call(self, args[0], applyArgs(args[1]));
    }),
    bind: native("bind", (self, args) => {
        if (!isCallable(self)) thrown("TypeError: bind of something that isn't a function");
        return new Bound(self, args[0], args.slice(1));
    }),
});

// ---------------------------------------------------------------- String

const HOST_STRING = String.prototype as unknown as Record<string, (this: string, ...args: Value[]) => Value>;

const thisString = (self: JsValue, name: string, run: Run): string => {
    if (self === null || self === undefined) thrown(`TypeError: String.prototype.${name} called on ${self}`);
    return toStr(self, run);
};

const stringMethod = (name: string, guard?: (s: string, args: readonly Value[]) => void): Native =>
    native(name, (self, args, run) => {
        const s = thisString(self, name, run);
        const converted = primitives(args, run);
        guard?.(s, converted);
        const method = HOST_STRING[name] as (this: string, ...args: Value[]) => Value;
        return checked(method.apply(s, converted));
    });

const lengthGuard = (s: string, args: readonly Value[]): void => {
    if (Number(args[0]) > MAX_STRING) refuse(`it makes a string longer than ${MAX_STRING} characters`);
};

const thisStringValue = (self: JsValue, name: string): string => (typeof self === "string" ? self : thrown(`TypeError: String.prototype.${name} requires a string`));

const replace = (name: string, all: boolean): Native =>
    native(name, (self, args, run) => {
        const s = thisString(self, name, run);
        const search = toStr(args[0], run);
        const replacement = args[1];
        if (!isCallable(replacement)) {
            const text = toStr(replacement, run);
            return checked(all ? s.replaceAll(search, text) : s.replace(search, text));
        }
        const positions: number[] = [];
        const advance = Math.max(1, search.length);
        for (let at = s.indexOf(search); at !== -1; at = !all || at + advance > s.length ? -1 : s.indexOf(search, at + advance)) {
            run.step(1);
            positions.push(at);
        }
        let out = "";
        let end = 0;
        for (const at of positions) {
            out += s.slice(end, at) + toStr(run.call(replacement, undefined, [search, at, s]), run);
            end = at + search.length;
            checked(out);
        }
        return checked(out + s.slice(end));
    });

const STRING_PROTO = namespace("String.prototype", {
    toString: native("toString", (self) => thisStringValue(self, "toString")),
    valueOf: native("valueOf", (self) => thisStringValue(self, "valueOf")),
    split: native("split", (self, args, run) => {
        const s = thisString(self, "split", run);
        const parts = s.split(...(primitives(args, run) as [string, number]));
        run.step(parts.length);
        return new ArrayObject(parts);
    }),
    replace: replace("replace", false),
    replaceAll: replace("replaceAll", true),
    repeat: stringMethod("repeat", (s, args) => {
        const count = Math.trunc(Number(args[0])) || 0;
        if (count > 0 && s.length * count > MAX_STRING) refuse(`it makes a string longer than ${MAX_STRING} characters`);
    }),
    padStart: stringMethod("padStart", lengthGuard),
    padEnd: stringMethod("padEnd", lengthGuard),
});
for (const name of "at charAt charCodeAt codePointAt concat endsWith includes indexOf lastIndexOf slice startsWith substr substring toLowerCase toUpperCase trim trimEnd trimStart trimLeft trimRight anchor big blink bold fixed fontcolor fontsize italics link small strike sub sup".split(
    " "
)) {
    STRING_PROTO.members.set(name, stringMethod(name));
}

// ---------------------------------------------------------------- Number, Boolean

const thisNumber = (self: JsValue, name: string): number => (typeof self === "number" ? self : thrown(`TypeError: Number.prototype.${name} requires a number`));

const numberMethod = (name: string): Native =>
    native(name, (self, args, run) => {
        const n = thisNumber(self, name);
        const method = (Number.prototype as unknown as Record<string, (this: number, ...args: Value[]) => Value>)[name] as (this: number, ...args: Value[]) => Value;
        return method.apply(n, primitives(args, run));
    });

const NUMBER_PROTO = namespace("Number.prototype", {
    toString: native("toString", (self, args, run) => {
        const n = thisNumber(self, "toString");
        const radix = args[0];
        if (radix === undefined) return String(n);
        const base = toNum(radix, run);
        if (base !== 10 && !Number.isInteger(n)) refuse("toString(radix) of a fraction is engine-dependent");
        return n.toString(base);
    }),
    valueOf: native("valueOf", (self) => thisNumber(self, "valueOf")),
    toFixed: numberMethod("toFixed"),
    toPrecision: numberMethod("toPrecision"),
    toExponential: numberMethod("toExponential"),
});

const thisBoolean = (self: JsValue, name: string): boolean => (typeof self === "boolean" ? self : thrown(`TypeError: Boolean.prototype.${name} requires a boolean`));

const BOOLEAN_PROTO = namespace("Boolean.prototype", {
    toString: native("toString", (self) => String(thisBoolean(self, "toString"))),
    valueOf: native("valueOf", (self) => thisBoolean(self, "valueOf")),
});

// ---------------------------------------------------------------- Array

const thisArray = (self: JsValue, name: string): ArrayObject => (self instanceof ArrayObject ? self : refuse(`Array.prototype.${name} of something other than an array`));

/** An array a method changes: charged for its length (host methods walk it), refused when frozen (strict and sloppy differ). */
const changing = (self: JsValue, name: string, run: Run): ArrayObject => {
    const array = thisArray(self, name);
    if (array.frozen) refuse("it changes a frozen array");
    run.step(1 + array.items.length);
    array.shape++;
    return array;
};

const reading = (self: JsValue, name: string, run: Run): ArrayObject => {
    const array = thisArray(self, name);
    run.step(1 + array.items.length);
    return array;
};

const callbackOf = (v: JsValue, name: string): JsValue => (isCallable(v) ? v : thrown(`TypeError: ${name}'s callback isn't a function`));

/** Converts the arguments at `positions` (indices, counts) to primitives; the rest stay values. */
const numericAt = (args: readonly JsValue[], positions: readonly number[], run: Run): JsValue[] => args.map((arg, i) => (positions.includes(i) ? toPrimitive(arg, run) : arg));

type HostArrayMethod = (this: JsValue[], ...args: JsValue[]) => unknown;
const HOST_ARRAY = Array.prototype as unknown as Record<string, HostArrayMethod>;

const hostArray = (name: string, mutates: boolean, numeric: readonly number[], wrap: boolean): Native =>
    native(name, (self, args, run) => {
        const array = mutates ? changing(self, name, run) : reading(self, name, run);
        const method = HOST_ARRAY[name] as HostArrayMethod;
        const result = method.apply(array.items, numericAt(args, numeric, run));
        return wrap ? new ArrayObject(result as JsValue[]) : (result as JsValue);
    });

/** `map`, `filter` and the like: visits present indices below the starting length (holes skipped), as the spec says. */
const iterating = (name: string, visit: (array: ArrayObject, callback: JsValue, thisArg: JsValue, run: Run) => JsValue): Native =>
    native(name, (self, args, run) => {
        const array = thisArray(self, name);
        return visit(array, callbackOf(args[0], name), args[1], run);
    });

const reduce = (name: string, fromRight: boolean): Native =>
    native(name, (self, args, run) => {
        const array = thisArray(self, name);
        const callback = callbackOf(args[0], name);
        const items = array.items;
        const length = items.length;
        const step = fromRight ? -1 : 1;
        let k = fromRight ? length - 1 : 0;
        const inRange = (i: number): boolean => (fromRight ? i >= 0 : i < length);
        let accumulator: JsValue;
        if (args.length >= 2) accumulator = args[1];
        else {
            while (inRange(k) && !(k in items)) {
                run.step(1);
                k += step;
            }
            if (!inRange(k)) return thrown(`TypeError: ${name} of an empty array with no initial value`);
            accumulator = items[k];
            k += step;
        }
        for (; inRange(k); k += step) {
            run.step(1);
            if (k in items) accumulator = run.call(callback, undefined, [accumulator, items[k], k, array]);
        }
        return accumulator;
    });

const concat = native("concat", (self, args, run) => {
    const array = reading(self, "concat", run);
    const out: JsValue[] = array.items.slice();
    for (const arg of args) {
        if (arg instanceof ArrayObject) {
            run.step(arg.items.length);
            const start = out.length;
            out.length += arg.items.length;
            for (const key of Object.keys(arg.items)) out[start + Number(key)] = arg.items[Number(key)];
        } else {
            out.push(arg);
        }
    }
    return new ArrayObject(out);
});

const ARRAY_PROTO = namespace("Array.prototype", {
    push: hostArray("push", true, [], false),
    pop: hostArray("pop", true, [], false),
    shift: hostArray("shift", true, [], false),
    unshift: hostArray("unshift", true, [], false),
    reverse: native("reverse", (self, args, run) => {
        changing(self, "reverse", run).items.reverse();
        return self;
    }),
    splice: hostArray("splice", true, [0, 1], true),
    fill: native("fill", (self, args, run) => {
        const array = changing(self, "fill", run);
        array.items.fill(args[0], ...(primitives(args.slice(1, 3), run) as number[]));
        return self;
    }),
    slice: hostArray("slice", false, [0, 1], true),
    indexOf: hostArray("indexOf", false, [1], false),
    lastIndexOf: hostArray("lastIndexOf", false, [1], false),
    includes: hostArray("includes", false, [1], false),
    at: hostArray("at", false, [0], false),
    concat,
    join: native("join", (self, args, run) => {
        const array = thisArray(self, "join");
        return join(array, args[0] === undefined ? "," : toStr(args[0], run), run);
    }),
    toString: native("toString", (self, args, run) => join(thisArray(self, "toString"), ",", run)),
    sort: native("sort", (self, args, run) => {
        if (args[0] !== undefined) return refuse("sorting with a comparator may not be consistent");
        const array = changing(self, "sort", run);
        if (array.items.some(isObject)) return refuse("sorting objects converts them in an engine-dependent order");
        array.items.sort();
        return self;
    }),
    forEach: iterating("forEach", (array, callback, thisArg, run) => {
        const length = array.items.length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (k in array.items) run.call(callback, thisArg, [array.items[k], k, array]);
        }
        return undefined;
    }),
    map: iterating("map", (array, callback, thisArg, run) => {
        const length = array.items.length;
        const out: JsValue[] = [];
        out.length = length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (k in array.items) out[k] = run.call(callback, thisArg, [array.items[k], k, array]);
        }
        return new ArrayObject(out);
    }),
    filter: iterating("filter", (array, callback, thisArg, run) => {
        const length = array.items.length;
        const out: JsValue[] = [];
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (!(k in array.items)) continue;
            const item = array.items[k];
            if (truthy(run.call(callback, thisArg, [item, k, array]))) out.push(item);
        }
        return new ArrayObject(out);
    }),
    some: iterating("some", (array, callback, thisArg, run) => {
        const length = array.items.length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (k in array.items && truthy(run.call(callback, thisArg, [array.items[k], k, array]))) return true;
        }
        return false;
    }),
    every: iterating("every", (array, callback, thisArg, run) => {
        const length = array.items.length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (k in array.items && !truthy(run.call(callback, thisArg, [array.items[k], k, array]))) return false;
        }
        return true;
    }),
    find: iterating("find", (array, callback, thisArg, run) => {
        const length = array.items.length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            const item = array.items[k];
            if (truthy(run.call(callback, thisArg, [item, k, array]))) return item;
        }
        return undefined;
    }),
    findIndex: iterating("findIndex", (array, callback, thisArg, run) => {
        const length = array.items.length;
        for (let k = 0; k < length; k++) {
            run.step(1);
            if (truthy(run.call(callback, thisArg, [array.items[k], k, array]))) return k;
        }
        return -1;
    }),
    reduce: reduce("reduce", false),
    reduceRight: reduce("reduceRight", true),
});

function* codePoints(text: string, run: Run): Generator<JsValue, void, undefined> {
    for (const point of text) {
        run.step(1);
        yield point;
    }
}

function* elements(array: ArrayObject, run: Run): Generator<JsValue, void, undefined> {
    for (let i = 0; i < array.items.length; i++) {
        run.step(1);
        yield array.items[i];
    }
}

/**
 * Iterates like the builtin array and string iterators (model 7): arrays live by index, strings by code point.
 * Checks the value at once, as GetIterator does, even when nothing is taken from it.
 */
export const iterate = (v: JsValue, run: Run): Generator<JsValue, void, undefined> => {
    if (typeof v === "string") return codePoints(v, run);
    if (v instanceof ArrayObject) return elements(v, run);
    if (v instanceof PlainObject || !isObject(v)) return thrown("TypeError: not iterable");
    return refuse("it iterates a function or builtin");
};

const newArray = (args: readonly JsValue[]): JsValue => {
    const [first] = args;
    if (args.length !== 1 || typeof first !== "number") return new ArrayObject([...args]);
    if (first >>> 0 !== first) return thrown("RangeError: invalid array length");
    const items: JsValue[] = [];
    items.length = first;
    return new ArrayObject(items);
};

const ARRAY = namespace(
    "Array",
    {
        prototype: ARRAY_PROTO,
        isArray: native("isArray", (self, args) => args[0] instanceof ArrayObject),
        of: native("of", (self, args) => new ArrayObject([...args])),
        from: native("from", (self, args, run) => {
            const [source, mapper, thisArg] = args;
            if (mapper !== undefined) callbackOf(mapper, "Array.from");
            if (source === null || source === undefined) return thrown("TypeError: Array.from of null or undefined");
            if (typeof source !== "string" && !(source instanceof ArrayObject)) return refuse("Array.from of something other than an array or a string");
            const out: JsValue[] = [];
            let k = 0;
            for (const item of iterate(source, run)) {
                out.push(mapper === undefined ? item : run.call(mapper, thisArg, [item, k]));
                k++;
            }
            return new ArrayObject(out);
        }),
    },
    (self, args) => newArray(args),
    (args) => newArray(args)
);

// ---------------------------------------------------------------- Object

/** Own enumerable string keys in the spec's order (array indices ascending, then insertion order). */
export const ownKeys = (v: JsValue): string[] => {
    if (typeof v === "string") return Array.from({ length: v.length }, (_, i) => String(i));
    if (v instanceof ArrayObject) return Object.keys(v.items);
    if (v instanceof PlainObject) {
        const indices: number[] = [];
        const names: string[] = [];
        for (const key of v.props.keys()) {
            const index = arrayIndex(key);
            if (index === -1) names.push(key);
            else indices.push(index);
        }
        indices.sort((a, b) => a - b);
        return [...indices.map(String), ...names];
    }
    // Numbers, booleans, functions and the modelled builtins have no enumerable own properties.
    return [];
};

const objectArgument = (v: JsValue, name: string): JsValue => (v === null || v === undefined ? thrown(`TypeError: Object.${name} of ${v}`) : v);

const OBJECT = namespace("Object", {
    prototype: OBJECT_PROTO,
    keys: native("keys", (self, args, run) => {
        const keys = ownKeys(objectArgument(args[0], "keys"));
        run.step(keys.length);
        return new ArrayObject(keys);
    }),
    values: native("values", (self, args, run) => {
        const source = objectArgument(args[0], "values");
        const keys = ownKeys(source);
        run.step(keys.length);
        return new ArrayObject(keys.map((key) => getMember(source, key, run)));
    }),
    entries: native("entries", (self, args, run) => {
        const source = objectArgument(args[0], "entries");
        const keys = ownKeys(source);
        run.step(keys.length);
        return new ArrayObject(keys.map((key) => new ArrayObject([key, getMember(source, key, run)])));
    }),
    assign: native("assign", (self, args, run) => {
        const [target, ...sources] = args;
        if (!(target instanceof PlainObject)) return refuse("Object.assign to something other than a plain object");
        for (const source of sources) {
            if (source === null || source === undefined) continue;
            const keys = ownKeys(source);
            run.step(keys.length);
            for (const key of keys) setMember(target, key, getMember(source, key, run), run);
        }
        return target;
    }),
    fromEntries: native("fromEntries", (self, args, run) => {
        const out = new PlainObject();
        for (const entry of iterate(objectArgument(args[0], "fromEntries"), run)) {
            if (!isObject(entry)) thrown("TypeError: an entry isn't an object");
            out.props.set(toStr(getMember(entry, "0", run), run), getMember(entry, "1", run));
        }
        return out;
    }),
    freeze: native("freeze", (self, args) => {
        const [target] = args;
        if (target instanceof PlainObject || target instanceof ArrayObject) target.frozen = true;
        else if (isObject(target)) refuse("it freezes a function or builtin");
        return target;
    }),
    is: native("is", (self, args) => Object.is(args[0], args[1])),
    hasOwn: native("hasOwn", (self, args, run) => {
        const target = objectArgument(args[0], "hasOwn");
        return hasOwn(target, toStr(args[1], run));
    }),
});

// ---------------------------------------------------------------- JSON

const fromHost = (v: unknown, run: Run): JsValue => {
    run.step(1);
    if (Array.isArray(v)) return new ArrayObject(v.map((item) => fromHost(item, run)));
    if (typeof v === "object" && v !== null) {
        const out = new PlainObject();
        for (const [key, item] of Object.entries(v)) out.props.set(key, fromHost(item, run));
        return out;
    }
    return v as Value;
};

const serialize = (v: JsValue, stack: Set<JsObject>, run: Run): string | undefined => {
    run.step(1);
    if (v === null) return "null";
    if (typeof v === "string" || typeof v === "number" || typeof v === "boolean") return JSON.stringify(v);
    if (v === undefined || isCallable(v)) return undefined;
    if (stack.has(v)) return thrown("TypeError: JSON.stringify of a cyclic structure");
    if (run.aliasOf("Object.prototype", "toJSON") !== undefined) return refuse("Object.prototype has an alias named toJSON");
    stack.add(v);
    try {
        if (v instanceof ArrayObject) {
            if (run.aliasOf("Array.prototype", "toJSON") !== undefined) return refuse("Array.prototype has an alias named toJSON");
            const parts: string[] = [];
            for (let i = 0; i < v.items.length; i++) parts.push(serialize(v.items[i], stack, run) ?? "null");
            return checked(`[${parts.join(",")}]`);
        }
        if (v instanceof PlainObject) {
            if (v.props.has("toJSON")) return refuse("it serializes an object with its own toJSON");
            const parts: string[] = [];
            for (const key of ownKeys(v)) {
                const text = serialize(v.props.get(key), stack, run);
                if (text !== undefined) parts.push(`${JSON.stringify(key)}:${text}`);
            }
            return checked(`{${parts.join(",")}}`);
        }
        return refuse("it serializes a builtin");
    } finally {
        stack.delete(v);
    }
};

const JSON_NAMESPACE = namespace("JSON", {
    parse: native("parse", (self, args, run) => {
        if (args[1] !== undefined) return refuse("JSON.parse with a reviver");
        return fromHost(JSON.parse(toStr(args[0], run)), run);
    }),
    stringify: native("stringify", (self, args, run) => {
        if (args[1] !== undefined || args[2] !== undefined) return refuse("JSON.stringify with a replacer or indentation");
        return serialize(args[0], new Set(), run);
    }),
});

// ---------------------------------------------------------------- Math, globals

/** Exact functions only: the others are approximated differently by engines (and `random` isn't pure). */
const MATH_FUNCTIONS = "abs ceil clz32 floor fround imul max min round sign trunc".split(" ");
const MATH_CONSTANTS = "E LN10 LN2 LOG10E LOG2E PI SQRT1_2 SQRT2".split(" ");

const MATH = namespace("Math", {});
for (const name of MATH_FUNCTIONS) {
    const method = (Math as unknown as Record<string, (...args: number[]) => number>)[name] as (...args: number[]) => number;
    MATH.members.set(
        name,
        native(name, (self, args, run) => method(...args.map((arg) => toNum(arg, run))))
    );
}
for (const name of MATH_CONSTANTS) MATH.members.set(name, (Math as unknown as Record<string, number>)[name] as number);

/** The members of `Math` the interpreter models. */
export const MATH_MEMBERS: ReadonlySet<string> = new Set([...MATH_FUNCTIONS, ...MATH_CONSTANTS]);

const onString = (name: string, method: (s: string) => Value): Native => native(name, (self, args, run) => checked(method(toStr(args[0], run))));

const PARSE_INT = native("parseInt", (self, args, run) => parseInt(toStr(args[0], run), toPrimitive(args[1], run) as number));
const PARSE_FLOAT = native("parseFloat", (self, args, run) => parseFloat(toStr(args[0], run)));

const STRING = namespace(
    "String",
    {
        prototype: STRING_PROTO,
        fromCharCode: native("fromCharCode", (self, args, run) => {
            run.step(args.length);
            return String.fromCharCode(...args.map((arg) => toNum(arg, run)));
        }),
        fromCodePoint: native("fromCodePoint", (self, args, run) => {
            run.step(args.length);
            return String.fromCodePoint(...args.map((arg) => toNum(arg, run)));
        }),
    },
    (self, args, run) => (args.length === 0 ? "" : toStr(args[0], run))
);

const NUMBER = namespace(
    "Number",
    {
        prototype: NUMBER_PROTO,
        isFinite: native("isFinite", (self, args) => Number.isFinite(args[0])),
        isInteger: native("isInteger", (self, args) => Number.isInteger(args[0])),
        isNaN: native("isNaN", (self, args) => Number.isNaN(args[0])),
        isSafeInteger: native("isSafeInteger", (self, args) => Number.isSafeInteger(args[0])),
        parseInt: PARSE_INT,
        parseFloat: PARSE_FLOAT,
        EPSILON: Number.EPSILON,
        MAX_SAFE_INTEGER: Number.MAX_SAFE_INTEGER,
        MIN_SAFE_INTEGER: Number.MIN_SAFE_INTEGER,
        MAX_VALUE: Number.MAX_VALUE,
        MIN_VALUE: Number.MIN_VALUE,
        NaN: Number.NaN,
        NEGATIVE_INFINITY: Number.NEGATIVE_INFINITY,
        POSITIVE_INFINITY: Number.POSITIVE_INFINITY,
    },
    (self, args, run) => (args.length === 0 ? 0 : toNum(args[0], run))
);

const BOOLEAN = namespace("Boolean", { prototype: BOOLEAN_PROTO }, (self, args) => truthy(args[0]));

/** The globals the interpreter models, by name. */
export const GLOBALS: ReadonlyMap<string, JsValue> = new Map<string, JsValue>([
    ["undefined", undefined],
    ["NaN", Number.NaN],
    ["Infinity", Number.POSITIVE_INFINITY],
    ["Array", ARRAY],
    ["String", STRING],
    ["Number", NUMBER],
    ["Boolean", BOOLEAN],
    ["Object", OBJECT],
    ["Math", MATH],
    ["JSON", JSON_NAMESPACE],
    ["parseInt", PARSE_INT],
    ["parseFloat", PARSE_FLOAT],
    ["isNaN", native("isNaN", (self, args, run) => Number.isNaN(toNum(args[0], run)))],
    ["isFinite", native("isFinite", (self, args, run) => Number.isFinite(toNum(args[0], run)))],
    ["encodeURIComponent", onString("encodeURIComponent", encodeURIComponent)],
    ["decodeURIComponent", onString("decodeURIComponent", decodeURIComponent)],
    ["encodeURI", onString("encodeURI", encodeURI)],
    ["decodeURI", onString("decodeURI", decodeURI)],
    ["escape", onString("escape", escape)],
    ["unescape", onString("unescape", unescape)],
]);

// ---------------------------------------------------------------- members

const STRING_CHAIN = [STRING_PROTO, OBJECT_PROTO];
const NUMBER_CHAIN = [NUMBER_PROTO, OBJECT_PROTO];
const BOOLEAN_CHAIN = [BOOLEAN_PROTO, OBJECT_PROTO];
const ARRAY_CHAIN = [ARRAY_PROTO, OBJECT_PROTO];
const OBJECT_CHAIN = [OBJECT_PROTO];
const FUNCTION_CHAIN = [FUNCTION_PROTO];

/** A modelled member of one of `chain`'s builtins, also under an alias (model 7); `undefined` when none has it. */
const memberOf = (chain: readonly Native[], key: string, run: Run): JsValue | undefined => {
    for (const owner of chain) if (owner.members.has(key)) return owner.members.get(key);
    for (const owner of chain) {
        const original = run.aliasOf(owner.name, key);
        if (original === undefined) continue;
        if (!owner.members.has(original)) return refuse(`it uses ${owner.name}.${original} (as ${key}), which isn't modelled`);
        return owner.members.get(original);
    }
    return undefined;
};

/** Inherited from builtins: modelled members, `undefined` for numeric keys (no builtin prototype has any), else refused. */
const inherited = (chain: readonly Native[], key: string, run: Run): JsValue => {
    const member = memberOf(chain, key, run);
    if (member !== undefined || isNumericKey(key)) return member;
    return refuse(`it reads ${key} of a ${chain[0]?.name ?? "builtin"} value, which isn't modelled`);
};

const parameterCount = (closure: Closure): number => {
    let count = 0;
    for (const param of closure.node.params) {
        if (param.type === "AssignmentPattern" || param.type === "RestElement") break;
        count++;
    }
    return count;
};

export const getMember = (v: JsValue, key: string, run: Run): JsValue => {
    if (v === null || v === undefined) return thrown(`TypeError: cannot read ${key} of ${v}`);
    switch (typeof v) {
        case "string": {
            if (key === "length") return v.length;
            const index = arrayIndex(key);
            if (index !== -1) return v[index];
            return inherited(STRING_CHAIN, key, run);
        }
        case "number":
            return inherited(NUMBER_CHAIN, key, run);
        case "boolean":
            return inherited(BOOLEAN_CHAIN, key, run);
        default:
            break;
    }
    if (v instanceof ArrayObject) {
        if (key === "length") return v.items.length;
        const index = arrayIndex(key);
        if (index !== -1) return v.items[index];
        return inherited(ARRAY_CHAIN, key, run);
    }
    if (v instanceof PlainObject) {
        if (v.props.has(key)) return v.props.get(key);
        const member = memberOf(OBJECT_CHAIN, key, run);
        if (member !== undefined) return member;
        if (OBJECT_PROTOTYPE_NAMES.has(key)) return refuse(`it reads Object.prototype.${key}, which isn't modelled`);
        return undefined;
    }
    if (v instanceof Native) {
        if (v.members.has(key)) return v.members.get(key);
        const original = run.aliasOf(v.name, key);
        if (original !== undefined && v.members.has(original)) return v.members.get(original);
        if (v.call === undefined) return refuse(`it reads ${v.name}.${key}, which isn't modelled`);
    }
    if (v instanceof Closure && key === "length") return parameterCount(v);
    return inherited(FUNCTION_CHAIN, key, run);
};

/** `PutValue` on a member; writes the program's modes treat differently (primitives, frozen objects, builtins) refuse. */
export const setMember = (target: JsValue, key: string, value: JsValue, run: Run): void => {
    if (target === null || target === undefined) return void thrown(`TypeError: cannot set ${key} of ${target}`);
    if (target instanceof ArrayObject) {
        if (target.frozen) return void refuse("it writes to a frozen array");
        const index = arrayIndex(key);
        if (index !== -1) {
            if (!(index in target.items)) target.shape++;
            target.items[index] = value;
            return;
        }
        if (key === "length") {
            const length = toNum(value, run);
            if (length >>> 0 !== length) return void thrown("RangeError: invalid array length");
            target.shape++;
            target.items.length = length;
            return;
        }
        return void refuse(`it sets ${key} of an array`);
    }
    if (target instanceof PlainObject) {
        if (target.frozen) return void refuse("it writes to a frozen object");
        if (key === "__proto__") return void refuse("it sets __proto__");
        if (!target.props.has(key)) {
            if (run.aliasOf("Object.prototype", key) !== undefined) return void refuse(`it sets ${key}, an alias on Object.prototype`);
            target.shape++;
        }
        target.props.set(key, value);
        return;
    }
    refuse(isObject(target) ? "it writes a property of a function or builtin" : "it writes a property of a primitive");
};

export const deleteMember = (target: JsValue, key: string): boolean => {
    if (target instanceof PlainObject && !target.frozen) {
        if (target.props.delete(key)) target.shape++;
        return true;
    }
    if (target instanceof ArrayObject && !target.frozen) {
        const index = arrayIndex(key);
        if (index !== -1) {
            if (index in target.items) target.shape++;
            delete target.items[index];
            return true;
        }
    }
    return refuse("it deletes something other than a property of its own objects");
};

/** `key in target`. */
export const hasProperty = (target: JsValue, key: string, run: Run): boolean => {
    if (!isObject(target)) return thrown("TypeError: in on a primitive");
    if (target instanceof PlainObject) {
        if (target.props.has(key) || OBJECT_PROTOTYPE_NAMES.has(key)) return true;
        return memberOf(OBJECT_CHAIN, key, run) !== undefined;
    }
    if (target instanceof ArrayObject) {
        if (hasOwn(target, key)) return true;
        if (isNumericKey(key)) return false;
        if (memberOf(ARRAY_CHAIN, key, run) !== undefined || OBJECT_PROTOTYPE_NAMES.has(key)) return true;
    }
    return refuse(`it asks whether ${key} is in a builtin value`);
};

/** For-in's keys: own enumerable ones; refused when an alias (maybe enumerable) is on the prototype chain. */
export const forInKeys = (v: JsValue, run: Run): string[] => {
    if (v === null || v === undefined) return [];
    const prototype =
        typeof v === "string"
            ? "String.prototype"
            : typeof v === "number"
              ? "Number.prototype"
              : typeof v === "boolean"
                ? "Boolean.prototype"
                : v instanceof ArrayObject
                  ? "Array.prototype"
                  : v instanceof PlainObject
                    ? "Object.prototype"
                    : refuse("it enumerates a function or builtin");
    if (run.hasAliases(prototype) || run.hasAliases("Object.prototype")) return refuse("aliases on its prototypes may be enumerable");
    return ownKeys(v);
};

export const shapeOf = (v: JsValue): number => (v instanceof PlainObject || v instanceof ArrayObject ? v.shape : 0);

/** Copies own enumerable properties (object spread, rest patterns) except `excluded`. */
export const copyOwn = (target: PlainObject, source: JsValue, excluded: ReadonlySet<string>, run: Run): void => {
    if (source === null || source === undefined) return;
    if (isObject(source) && !(source instanceof PlainObject) && !(source instanceof ArrayObject)) return void refuse("it copies a function or builtin");
    const keys = ownKeys(source);
    run.step(keys.length);
    for (const key of keys) if (!excluded.has(key)) target.props.set(key, getMember(source, key, run));
};
