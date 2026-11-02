import type { PropertyPath } from "./model.js";

/**
 * The builtins as a program finds them before it runs (model 7: builtins intact), by reflection on the host's own
 * builtins: nothing here runs program code, or any code beyond reading descriptors. The global object is a stand-in
 * holding ECMAScript's global properties (as the host has them) and the page's host model: `window`/`self` are the
 * global object, the timer functions and `console` exist (model 10). Every other host global is absent here: what the
 * program reads of it is a live read (`getters.ts`, model 10).
 */

/** ECMAScript's global properties (ECMA-262 §19, Annex B), in the specification's order. */
const STANDARD_GLOBALS: readonly string[] = [
    "globalThis",
    "Infinity",
    "NaN",
    "undefined",
    "eval",
    "isFinite",
    "isNaN",
    "parseFloat",
    "parseInt",
    "decodeURI",
    "decodeURIComponent",
    "encodeURI",
    "encodeURIComponent",
    "AggregateError",
    "Array",
    "ArrayBuffer",
    "BigInt",
    "BigInt64Array",
    "BigUint64Array",
    "Boolean",
    "DataView",
    "Date",
    "Error",
    "EvalError",
    "FinalizationRegistry",
    "Float16Array",
    "Float32Array",
    "Float64Array",
    "Function",
    "Int8Array",
    "Int16Array",
    "Int32Array",
    "Iterator",
    "Map",
    "Number",
    "Object",
    "Promise",
    "Proxy",
    "RangeError",
    "ReferenceError",
    "RegExp",
    "Set",
    "SharedArrayBuffer",
    "String",
    "Symbol",
    "SyntaxError",
    "TypeError",
    "Uint8Array",
    "Uint8ClampedArray",
    "Uint16Array",
    "Uint32Array",
    "URIError",
    "WeakMap",
    "WeakRef",
    "WeakSet",
    "Atomics",
    "JSON",
    "Math",
    "Reflect",
    "escape",
    "unescape",
];

/** The page's functions the host model has (model 10); each its own function, as in a browser. */
const HOST_FUNCTIONS: readonly string[] = ["setTimeout", "setInterval", "requestAnimationFrame", "clearTimeout", "clearInterval", "cancelAnimationFrame", "queueMicrotask"];

const CONSOLE_METHODS: readonly string[] = [
    "assert",
    "clear",
    "count",
    "countReset",
    "debug",
    "dir",
    "dirxml",
    "error",
    "group",
    "groupCollapsed",
    "groupEnd",
    "info",
    "log",
    "profile",
    "profileEnd",
    "table",
    "time",
    "timeEnd",
    "timeLog",
    "timeStamp",
    "trace",
    "warn",
];

/**
 * A property lookup on a builtin: `base` when the path doesn't reach a value by data properties; otherwise where along
 * the prototype chain it is found (`holder`: an owner index, -1 for another object). `owner` is the value's owner index
 * (-1: not an owner); `value` the primitive (`null` for objects, symbols and bigints).
 */
export type Lookup =
    | { readonly kind: "base" }
    | { readonly kind: "absent" }
    | { readonly kind: "accessor"; readonly holder: number }
    | { readonly kind: "data"; readonly holder: number; readonly owner: number; readonly type: string; readonly value: unknown; readonly writable: boolean };

type Value = unknown;

const isObject = (value: Value): value is object => (typeof value === "object" && value !== null) || typeof value === "function";

/** Functions no code calls: only their identity and their own properties are looked at. */
const standIn = (name: string): Value => Object.getOwnPropertyDescriptor({ [name]() {} }, name)?.value;

const makeGlobal = (): object => {
    const global: object = Object.create(Object.prototype);
    const define = (name: string, value: Value): void => void Object.defineProperty(global, name, { value, writable: true, enumerable: false, configurable: true });
    for (const name of STANDARD_GLOBALS) {
        if (name === "globalThis") define(name, global);
        else if (Object.hasOwn(globalThis, name)) define(name, (globalThis as Record<string, Value>)[name]);
    }
    define("window", global);
    define("self", global);
    for (const name of HOST_FUNCTIONS) define(name, standIn(name));
    const console: object = Object.create(Object.prototype);
    for (const name of CONSOLE_METHODS) Object.defineProperty(console, name, { value: standIn(name), writable: true, enumerable: true, configurable: true });
    define("console", console);
    return global;
};

export class Realm {
    readonly #global: object;
    readonly #ownerIndex = new Map<object, number>();
    /** Every builtin object a name reaches: the global object, each global holding an object, each such function's prototype. */
    readonly owners: readonly PropertyPath[];
    /** Each owner's own names, by owner index. */
    readonly before: readonly ReadonlySet<string>[];

    constructor() {
        this.#global = makeGlobal();
        const owners: PropertyPath[] = [[]];
        this.#ownerIndex.set(this.#global, 0);
        const add = (path: PropertyPath, value: Value): void => {
            if (!isObject(value) || this.#ownerIndex.has(value)) return;
            this.#ownerIndex.set(value, owners.length);
            owners.push(path);
        };
        const names = Object.getOwnPropertyNames(this.#global);
        for (const name of names) add([name], this.#own(this.#global, name));
        for (const name of names) {
            const value = this.#own(this.#global, name);
            if (typeof value === "function") add([name, "prototype"], this.#own(value, "prototype"));
        }
        this.owners = owners;
        this.before = owners.map((path) => {
            const value = this.#at(path);
            return new Set(isObject(value) ? Object.getOwnPropertyNames(value) : []);
        });
    }

    /** An own data property's value; `undefined` for an accessor or none. */
    #own(object: object, key: string): Value {
        const descriptor = Object.getOwnPropertyDescriptor(object, key);
        return descriptor !== undefined && "value" in descriptor ? descriptor.value : undefined;
    }

    /** `key` along `object`'s prototype chain, and where. */
    #find(object: object, key: string): { holder: object; descriptor: PropertyDescriptor } | undefined {
        for (let holder: object | null = object; holder !== null; holder = Object.getPrototypeOf(holder) as object | null) {
            const descriptor = Object.getOwnPropertyDescriptor(holder, key);
            if (descriptor !== undefined) return { holder, descriptor };
        }
        return undefined;
    }

    /** The value at `path` from the global object through data properties (own or inherited); `undefined` when a step isn't one. */
    #at(path: PropertyPath): Value {
        let value: Value = this.#global;
        for (const key of path) {
            if (value === null || value === undefined) return undefined;
            const found = this.#find(Object(value) as object, key);
            if (found === undefined || !("value" in found.descriptor)) return undefined;
            value = found.descriptor.value;
        }
        return value;
    }

    /** Whether `path` reaches a value by data properties at all (as `#at`, telling `undefined` values apart). */
    #reaches(path: PropertyPath): boolean {
        let value: Value = this.#global;
        for (const key of path) {
            if (value === null || value === undefined) return false;
            const found = this.#find(Object(value) as object, key);
            if (found === undefined || !("value" in found.descriptor)) return false;
            value = found.descriptor.value;
        }
        return true;
    }

    ownerIndexOf(path: PropertyPath): number {
        const value = this.#at(path);
        return isObject(value) ? (this.#ownerIndex.get(value) ?? -1) : -1;
    }

    /** `path.key` looked up on the builtins. */
    lookup(path: PropertyPath, key: string): Lookup {
        if (!this.#reaches(path)) return { kind: "base" };
        const base = this.#at(path);
        if (base === null || base === undefined) return { kind: "base" };
        const found = this.#find(Object(base) as object, key);
        if (found === undefined) return { kind: "absent" };
        const holder = this.#ownerIndex.get(found.holder) ?? -1;
        if (!("value" in found.descriptor)) return { kind: "accessor", holder };
        const value: Value = found.descriptor.value;
        const owner = isObject(value) ? (this.#ownerIndex.get(value) ?? -1) : -1;
        const primitive = isObject(value) || typeof value === "symbol" || typeof value === "bigint" ? null : value;
        return { kind: "data", holder, owner, type: typeof value, value: primitive, writable: found.descriptor.writable === true };
    }

    /** Own names of the builtin at `path` (an owner or not); `undefined` when no object is there. */
    ownNames(path: PropertyPath): ReadonlySet<string> | undefined {
        const index = this.ownerIndexOf(path);
        if (index >= 0) return this.before[index];
        const value = this.#at(path);
        return isObject(value) ? new Set(Object.getOwnPropertyNames(value)) : undefined;
    }

    /** Whether two paths reach one builtin object. */
    same(a: PropertyPath, b: PropertyPath): boolean {
        const left = this.#at(a);
        return isObject(left) && left === this.#at(b);
    }

    /**
     * The first of `owner`'s own names (in its own order) holding `value` as a data property: a builtin by path, or a
     * primitive by `===`.
     */
    nameOf(owner: PropertyPath, value: { readonly path: PropertyPath } | { readonly primitive: Value }): string | undefined {
        const holder = this.#at(owner);
        if (!isObject(holder)) return undefined;
        const wanted = "path" in value ? this.#at(value.path) : value.primitive;
        if ("path" in value && !isObject(wanted)) return undefined;
        return Object.getOwnPropertyNames(holder).find((name) => {
            const descriptor = Object.getOwnPropertyDescriptor(holder, name);
            return descriptor !== undefined && "value" in descriptor && descriptor.value === wanted;
        });
    }

    /** The first owner (the global object first) holding the builtin at `path` as an own data property, and the name. */
    holderOf(path: PropertyPath): { owner: PropertyPath; name: string } | undefined {
        for (const owner of this.owners) {
            const name = this.nameOf(owner, { path });
            if (name !== undefined) return { owner, name };
        }
        return undefined;
    }
}

let shared: Realm | undefined;

/** One per process: the host's builtins don't change. */
export const realm = (): Realm => (shared ??= new Realm());
