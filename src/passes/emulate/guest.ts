import type { Value } from "../../core/evaluate.js";
import type { Held, RunResult } from "../../core/sandbox.js";
import { Sandbox } from "../../core/sandbox.js";

/**
 * The obfuscator runtime as it lives in the QuickJS sandbox, and the one interface the passes use to ask it things.
 *
 * Guest side: an object of helper functions, installed once and held by the host only (no guest name reaches it).
 * Host side: `Guest`, one typed method per helper. Every question is a `Sandbox.invoke` with plain data (property
 * paths, keys, argument values); no source text is assembled for any of it. The only code the sandbox compiles is
 * the program's own statements (`run`).
 *
 * Paths are property paths: from the global object for builtins (`["String", "prototype"]`, `[]` is the global object
 * itself), from the storage object for the runtime (`["k", "m"]`). Keys are property keys as JS sees them
 * (strings: `G[593908]` has key `"593908"`).
 */

export type PropertyPath = readonly string[];

/**
 * How a call alias passes arguments on to its builtin (probed in the runtime):
 * `"static"`: `G.alias(a)` is `Owner.original(a)`; `"method"`: `G.alias(x, a)` is `x.original(a)` (dispatch on x);
 * `"call"`: `G.alias(x, a)` is `Owner.original.call(x, a)`.
 */
export type CallStyle = "static" | "method" | "call";

/**
 * A wrapper call the prelude made: key, arguments and result. Objects and functions are reported by type only. With the
 * wrapper's target given to `record`, also the guest identities (`idOf`) around the call: of the target's owner before it,
 * and of the target before and after it (`null`: a primitive, or reached through an accessor). A change is a write
 * the call made to the target, such as the string decoder replacing its stage function when it freezes.
 */
export interface LoggedCall {
    readonly key: string;
    readonly args: readonly unknown[];
    readonly result: unknown;
    readonly owner: number | null;
    readonly before: number | null;
    readonly after: number | null;
    /** For a number result: whether `Array.prototype` or `Object.prototype` had an index property right after the call. */
    readonly indexed?: boolean;
}

/** Guest identities of a storage object part and of the functions it holds in own data properties, by name. */
export interface BuiltIdentities {
    readonly holder: number;
    readonly methods: ReadonlyMap<string, number>;
}

/** One call for `resolve`: `storage.path(...args)`, then optionally `[lookup[0]][lookup[1]]...` on the result. */
export interface ResolveRequest {
    readonly path: PropertyPath;
    readonly args: readonly Value[];
    readonly lookup?: PropertyPath;
}

export type ResolveResult =
    | { readonly ok: true; readonly value: Value; readonly repeatable: boolean }
    | { readonly ok: true; readonly nonPrimitive: "object" | "function" }
    /** `stale`: not called, because an earlier call in the batch changed the runtime's state. */
    | { readonly ok: false; readonly error: string; readonly stale?: true };

/**
 * How the owners (builtins, the global object) and the storage object's accessors changed since the guest's baseline:
 * entries are `[owner index, name, value]`, values as identities (`#3`) or typed primitives. Only what changed is
 * copied out; `namesBefore` lists, for owners that gained a property, the names they had.
 */
export interface OwnersChange {
    readonly same: boolean;
    readonly accessorsBefore: number;
    readonly accessorsAfter: number;
    /** Entries the baseline had that are gone or hold something else now. */
    readonly changed: readonly (readonly [number, string, string])[];
    /** Entries that are new or hold something else now. */
    readonly added: readonly (readonly [number, string, string])[];
    readonly namesBefore: Readonly<Record<number, readonly string[]>>;
}

/** An object or function is reported as `{ nonPrimitive: typeof value }`: copying it out could degrade it. */
const GUEST_RUNTIME = String.raw`(function () {
    function isObject(v) { return v !== null && (typeof v === "object" || typeof v === "function"); }
    function plain(v) { return isObject(v) ? { nonPrimitive: typeof v } : v; }
    function from(base, path) {
        var v = base;
        for (var i = 0; i < path.length; i++) {
            if (v === null || v === undefined) return undefined;
            v = v[path[i]];
        }
        return v;
    }
    var store = null;
    var calls = [];
    var ids = new Map();
    function idOf(v) {
        if (!ids.has(v)) ids.set(v, ids.size + 1);
        return ids.get(v);
    }
    function describe(v) { return isObject(v) ? "#" + idOf(v) : typeof v + ":" + String(v); }
    /** The value at a storage path, as { value }, when every step is a data property (reading it runs no code); else null. */
    function dataAt(path) {
        var v = store;
        for (var i = 0; i < path.length; i++) {
            if (v === null || v === undefined) return null;
            var holder = Object(v), d;
            while (holder !== null && !(d = Object.getOwnPropertyDescriptor(holder, path[i]))) holder = Object.getPrototypeOf(holder);
            if (d === undefined || !("value" in d)) return null;
            v = d.value;
        }
        return { value: v };
    }
    function identityAt(path) {
        var found = dataAt(path);
        return found !== null && isObject(found.value) ? idOf(found.value) : null;
    }
    /** Whether an object has an own property named like an array index. */
    function hasIndex(o) {
        return Object.getOwnPropertyNames(o).some(function (name) { return String(name >>> 0) === name && name !== "4294967295"; });
    }
    /** Whether the descriptor d is what state recorded for its property j. */
    function recorded(d, state, j) {
        return "value" in d ? !state.accessor[j] && Object.is(d.value, state.values[j]) : state.accessor[j] && Object.is(d.get, state.values[j]) && Object.is(d.set, state.setters[j]);
    }
    /**
     * One owner's own properties as they are now, in their own order (a change of order is a change), values kept as
     * they are: comparing two states needs no strings. The owner's last state (previous) comes back as it is when
     * nothing changed, so two states compare by identity (sameOwners); otherwise the properties up to the first
     * difference are previous's, and only the rest is recorded again.
     */
    function ownerState(owner, previous) {
        if (!isObject(owner)) return null;
        var names = Object.getOwnPropertyNames(owner), same = 0;
        if (previous !== null) {
            var shared = Math.min(names.length, previous.names.length);
            while (same < shared && names[same] === previous.names[same] && recorded(Object.getOwnPropertyDescriptor(owner, names[same]), previous, same)) same++;
            if (same === names.length && same === previous.names.length) return previous;
        }
        var values = previous === null ? [] : previous.values.slice(0, same);
        var setters = previous === null ? [] : previous.setters.slice(0, same);
        var accessor = previous === null ? [] : previous.accessor.slice(0, same);
        for (var j = same; j < names.length; j++) {
            var d = Object.getOwnPropertyDescriptor(owner, names[j]);
            var isData = "value" in d;
            accessor.push(!isData);
            values.push(isData ? d.value : d.get);
            setters.push(isData ? undefined : d.set);
        }
        return { names: names, values: values, setters: setters, accessor: accessor };
    }
    /** The owners' states (ownerState, given previous's), plus how many accessors the storage object has. */
    function ownersState(owners, previous) {
        var states = [];
        for (var i = 0; i < owners.length; i++) states.push(ownerState(from(globalThis, owners[i]), previous === undefined ? null : previous.owners[i]));
        var accessors = 0;
        var keys = isObject(store) ? Object.getOwnPropertyNames(store) : [];
        for (var k = 0; k < keys.length; k++) {
            if (!("value" in Object.getOwnPropertyDescriptor(store, keys[k]))) accessors++;
        }
        return { owners: states, accessors: accessors };
    }
    /** Whether the owners are as they were: b was made with a as its previous state, so unchanged owners are a's. */
    function sameOwners(a, b) {
        for (var i = 0; i < a.owners.length; i++) if (a.owners[i] !== b.owners[i]) return false;
        return true;
    }
    /** A state's properties as [owner index, name, value] entries, values as identities (#3) or typed primitives. */
    function entriesOf(state) {
        var entries = [];
        for (var i = 0; i < state.owners.length; i++) {
            var s = state.owners[i];
            if (s === null) continue;
            for (var j = 0; j < s.names.length; j++) {
                entries.push([i, s.names[j], s.accessor[j] ? "get " + describe(s.values[j]) + " set " + describe(s.setters[j]) : describe(s.values[j])]);
            }
        }
        return entries;
    }
    /** The owners as last marked (markOwners, ownersSince): compared with in the guest, so only changes are copied out. */
    var baseline = null;
    function ownersSince(owners) {
        var before = baseline, after = ownersState(owners, before);
        baseline = after;
        var change = { same: sameOwners(before, after), accessorsBefore: before.accessors, accessorsAfter: after.accessors, changed: [], added: [], namesBefore: {} };
        if (change.same) return change;
        function key(e) { return e[0] + "\u0000" + e[1] + "\u0000" + e[2]; }
        var beforeEntries = entriesOf(before), afterEntries = entriesOf(after);
        var had = new Set(beforeEntries.map(key)), has = new Set(afterEntries.map(key));
        change.changed = beforeEntries.filter(function (e) { return !has.has(key(e)); });
        change.added = afterEntries.filter(function (e) { return !had.has(key(e)); });
        change.added.forEach(function (e) {
            if (change.namesBefore[e[0]] === undefined) change.namesBefore[e[0]] = before.owners[e[0]] === null ? [] : before.owners[e[0]].names;
        });
        return change;
    }
    /**
     * How a call alias passes its arguments on, probed with spies:
     * - "static": G.alias(7, 8) calls owner[name] with this = owner;
     * - "method": G.alias(r, 7, 8) calls r[name](7, 8), dispatching on the receiver, and a missing receiver throws
     *   (as undefined.name() would);
     * - "call": G.alias(r, 7, 8) calls owner[name] with this = r.
     * Exactly one must hold, or the answer is null and the alias can't be rewritten.
     */
    function styleOf(fn, owner, name) {
        var calls, self, args;
        function spy() { calls++; self = this; args = Array.prototype.slice.call(arguments); return spy; }
        function saw(receiver) { return calls === 1 && self === receiver && args.length === 2 && args[0] === 7 && args[1] === 8; }
        function probe(run) {
            calls = 0;
            try { return run() === spy; } catch (e) { return false; }
        }
        var original = owner[name], isStatic = false, isCall = false, isMethod = false;
        var receiver = Object.create(null);
        try {
            owner[name] = spy;
            isStatic = probe(function () { return fn(7, 8); }) && saw(owner);
            isCall = probe(function () { return fn(receiver, 7, 8); }) && saw(receiver);
        } finally {
            owner[name] = original;
        }
        var dispatching = Object.create(null);
        dispatching[name] = spy;
        isMethod = probe(function () { return fn(dispatching, 7, 8); }) && saw(dispatching);
        if (isMethod) {
            try { fn(undefined, 7, 8); isMethod = false; } catch (e) {}
        }
        var styles = (isStatic ? ["static"] : []).concat(isCall ? ["call"] : [], isMethod ? ["method"] : []);
        return styles.length === 1 ? styles[0] : null;
    }
    function call(request) {
        var owner = from(store, request.path.slice(0, -1));
        var result = owner[request.path[request.path.length - 1]].apply(owner, request.args);
        return request.lookup ? from(result, request.lookup) : result;
    }
    var api = {
        globals: function () { return Object.getOwnPropertyNames(globalThis); },
        /**
         * Every builtin object reachable by name before the program runs: the global object, each global data
         * property holding an object or function, and each such function's prototype, once per object.
         */
        owners: function () {
            var paths = [[]], seen = new Set([globalThis]);
            function add(path, value) {
                if (!isObject(value) || seen.has(value)) return;
                seen.add(value);
                paths.push(path);
            }
            var names = Object.getOwnPropertyNames(globalThis);
            var data = names.map(function (name) { var d = Object.getOwnPropertyDescriptor(globalThis, name); return "value" in d ? d.value : undefined; });
            names.forEach(function (name, i) { add([name], data[i]); });
            names.forEach(function (name, i) {
                if (typeof data[i] !== "function") return;
                var d = Object.getOwnPropertyDescriptor(data[i], "prototype");
                if (d !== undefined && "value" in d) add([name, "prototype"], d.value);
            });
            return paths;
        },
        bind: function (name) {
            store = globalThis[name];
            return isObject(store);
        },
        snapshot: function (owners) {
            return owners.map(function (path) {
                var owner = from(globalThis, path);
                return isObject(owner) ? Object.getOwnPropertyNames(owner) : [];
            });
        },
        markOwners: function (owners) { baseline = ownersState(owners); return true; },
        ownersSince: ownersSince,
        record: function (request) {
            var key = request.key, target = request.target;
            var fn = store[key];
            if (typeof fn !== "function") return false;
            store[key] = function () {
                var owner = target === null ? null : identityAt(target.slice(0, -1));
                var before = target === null ? null : identityAt(target);
                var result = fn.apply(this, arguments);
                var call = { key: key, args: Array.prototype.map.call(arguments, plain), result: plain(result), owner: owner, before: before, after: target === null ? null : identityAt(target) };
                if (typeof result === "number") call.indexed = hasIndex(Array.prototype) || hasIndex(Object.prototype);
                calls.push(call);
                return result;
            };
            return true;
        },
        built: function (path) {
            var holder = dataAt(path);
            if (holder === null || !isObject(holder.value)) return null;
            var methods = {};
            var names = Object.getOwnPropertyNames(holder.value);
            for (var i = 0; i < names.length; i++) {
                var d = Object.getOwnPropertyDescriptor(holder.value, names[i]);
                if ("value" in d && typeof d.value === "function") methods[names[i]] = idOf(d.value);
            }
            return { holder: idOf(holder.value), methods: methods };
        },
        takeCalls: function () {
            var taken = calls;
            calls = [];
            return taken;
        },
        aliasOf: function (request) {
            var owner = from(globalThis, request.owner);
            var value = owner[request.alias];
            if (value === undefined) return null;
            for (var i = 0; i < request.candidates.length; i++) {
                try { if (owner[request.candidates[i]] === value) return request.candidates[i]; } catch (e) {}
            }
            return null;
        },
        callAliases: function (owners) {
            var found = [];
            var keys = Object.getOwnPropertyNames(store);
            for (var i = 0; i < keys.length; i++) {
                var d = Object.getOwnPropertyDescriptor(store, keys[i]);
                if (typeof d.get !== "function") continue;
                var fn, builtin;
                try {
                    fn = store[keys[i]];
                    if (typeof fn !== "function") continue;
                    builtin = fn();
                } catch (e) { continue; }
                if (builtin === undefined || builtin === null) continue;
                // Owners in order, the global object first: a constructor is found as the global, not as some
                // prototype's "constructor".
                search: for (var o = 0; o < owners.length; o++) {
                    var owner = from(globalThis, owners[o]);
                    if (!isObject(owner)) continue;
                    var names = Object.getOwnPropertyNames(owner);
                    for (var n = 0; n < names.length; n++) {
                        try {
                            if (owner[names[n]] !== builtin) continue;
                        } catch (e) { continue; }
                        found.push({ key: keys[i], owner: o, original: names[n], style: styleOf(fn, owner, names[n]) });
                        break search;
                    }
                }
            }
            return found;
        },
        globalReads: function () {
            // Getters handing out a function whose zero-argument call reads one global property the global object
            // lacks and returns it (undefined): the read is seen by a proxy put in the global object's prototype
            // chain, which only lookups of missing names reach.
            var found = [];
            var proto = Object.getPrototypeOf(globalThis);
            var read;
            var note = function (key) { if (read !== undefined && read.indexOf(key) === -1) read.push(key); };
            var spy = new Proxy(proto === null ? Object.create(null) : proto, {
                get: function (target, key, receiver) { note(key); return Reflect.get(target, key, receiver); },
                has: function (target, key) { note(key); return Reflect.has(target, key); }
            });
            try { Object.setPrototypeOf(globalThis, spy); } catch (e) { return found; }
            try {
                var keys = Object.getOwnPropertyNames(store);
                for (var i = 0; i < keys.length; i++) {
                    var d = Object.getOwnPropertyDescriptor(store, keys[i]);
                    if (typeof d.get !== "function") continue;
                    var fn, result, names;
                    try {
                        fn = store[keys[i]];
                        if (typeof fn !== "function") continue;
                        read = [];
                        result = fn();
                    } catch (e) { continue; } finally { names = read; read = undefined; }
                    if (names === undefined) continue;
                    if (result !== undefined || names.length !== 1 || typeof names[0] !== "string") continue;
                    if (Object.prototype.hasOwnProperty.call(globalThis, names[0])) continue;
                    found.push({ key: keys[i], name: names[0] });
                }
            } finally {
                read = undefined;
                Object.setPrototypeOf(globalThis, proto);
            }
            return found;
        },
        hostAliases: function (names) {
            // Global accessors forwarding to one global property the guest lacks (a host object): the getter reads it
            // and hands out its value, absent (seen by a proxy in the global object's prototype chain, which only
            // lookups of missing names reach) or present (a marker put there for the probe), and the setter writes it.
            // (An accessor that looks up nothing missing can't be told apart from one reading state that changes
            // later, so it isn't answered: an alias of undefined stays.)
            var found = [];
            var proto = Object.getPrototypeOf(globalThis);
            var reads, writes;
            var spy = new Proxy(proto === null ? Object.create(null) : proto, {
                get: function (target, key, receiver) { if (reads !== undefined && reads.indexOf(key) === -1) reads.push(key); return Reflect.get(target, key, receiver); },
                has: function (target, key) { if (reads !== undefined && reads.indexOf(key) === -1) reads.push(key); return Reflect.has(target, key); },
                set: function (target, key, value, receiver) {
                    if (writes === undefined) return Reflect.set(target, key, value, receiver);
                    writes.push([key, value]);
                    return true;
                }
            });
            try { Object.setPrototypeOf(globalThis, spy); } catch (e) { return found; }
            try {
                for (var i = 0; i < names.length; i++) {
                    var d = Object.getOwnPropertyDescriptor(globalThis, names[i]);
                    if (d === undefined || typeof d.get !== "function" || typeof d.set !== "function") continue;
                    var got, read, written, marker = {};
                    try { reads = []; got = d.get.call(globalThis); } catch (e) { continue; } finally { read = reads; reads = undefined; }
                    if (got !== undefined || read.length !== 1 || typeof read[0] !== "string") continue;
                    var name = read[0];
                    if (Object.prototype.hasOwnProperty.call(globalThis, name)) continue;
                    try {
                        Object.defineProperty(globalThis, name, { value: marker, configurable: true, writable: true });
                        got = d.get.call(globalThis);
                    } catch (e) { got = undefined; } finally { delete globalThis[name]; }
                    if (got !== marker) continue;
                    try { writes = []; d.set.call(globalThis, marker); } catch (e) { continue; } finally { written = writes; writes = undefined; }
                    if (written.length !== 1 || written[0][0] !== name || written[0][1] !== marker || Object.prototype.hasOwnProperty.call(globalThis, name)) continue;
                    found.push({ alias: names[i], name: name });
                }
            } finally {
                reads = undefined;
                writes = undefined;
                Object.setPrototypeOf(globalThis, proto);
            }
            return found;
        },
        compare: function (requests) {
            // Equality of the values at two storage paths, read through data properties only: objects by identity,
            // primitives by value; an object against a primitive would convert it, so it isn't answered.
            return requests.map(function (request) {
                var a = dataAt(request.left), b = dataAt(request.right);
                if (a === null || b === null) return { ok: false, reason: "a step to a value is not a data property" };
                var x = a.value, y = b.value;
                if (isObject(x) !== isObject(y)) return { ok: false, reason: "an object compared with a primitive converts it" };
                switch (request.op) {
                    case "===": return { ok: true, value: x === y };
                    case "!==": return { ok: true, value: x !== y };
                    case "==": return { ok: true, value: x == y };
                    case "!=": return { ok: true, value: x != y };
                }
                return { ok: false, reason: "not an equality" };
            });
        },
        globalKeys: function () {
            return Object.getOwnPropertyNames(store).filter(function (key) {
                try { return store[key] === globalThis; } catch (e) { return false; }
            });
        },
        resolve: function (requests) {
            // A call whose result differs when repeated changed the runtime's state (a decoder stage, say): everything
            // after it would be answered by a runtime the program never has, so stop calling.
            var changed = false;
            return requests.map(function (request) {
                if (changed) return { ok: false, error: "after a call that changed the runtime's state", stale: true };
                var first, second;
                try { first = call(request); } catch (e) { return { ok: false, error: String(e && e.message !== undefined ? e.message : e) }; }
                if (isObject(first)) return { ok: true, nonPrimitive: typeof first };
                try { second = call(request); } catch (e) { changed = true; return { ok: true, value: first, repeatable: false }; }
                if (!Object.is(first, second)) changed = true;
                return { ok: true, value: first, repeatable: !changed };
            });
        },
        stateKey: function (path) {
            // Data properties only: a getter on the way would run code and could change the runtime.
            var found = dataAt(path);
            if (found === null) return null;
            var v = found.value;
            if (isObject(v)) return "o:" + idOf(v);
            return typeof v === "number" ? "n:" + v : typeof v === "string" ? "s:" + v : null;
        },
        inspect: function (path) {
            // The value's type, and whether every step to it is a data property (reading it can't run code).
            var v = store, data = true;
            for (var i = 0; i < path.length && v !== null && v !== undefined; i++) {
                var holder = Object(v), d;
                while (holder !== null && !(d = Object.getOwnPropertyDescriptor(holder, path[i]))) holder = Object.getPrototypeOf(holder);
                if (d && !("value" in d)) data = false;
                v = v[path[i]];
            }
            return { type: typeof v, data: data };
        },
        ownCallables: function () {
            // The storage object's own properties a call could reach: function values, and getters (which run on access).
            return Object.getOwnPropertyNames(store).filter(function (key) {
                var d = Object.getOwnPropertyDescriptor(store, key);
                return !("value" in d) || typeof d.value === "function";
            });
        },
        effectFree: function (request) {
            var before = ownersState(request.owners);
            var storeBefore = describeStore();
            try { call(request.call); } catch (e) { return false; }
            var after = ownersState(request.owners, before);
            return sameOwners(before, after) && before.accessors === after.accessors && storeBefore === describeStore();
        }
    };
    function describeStore() {
        var keys = Object.getOwnPropertyNames(store).sort();
        return keys.map(function (k) {
            var d = Object.getOwnPropertyDescriptor(store, k);
            return k + "=" + ("value" in d ? describe(d.value) : "accessor");
        }).join("|");
    }
    return api;
})()`;

/**
 * The browser globals a prelude touches while the page loads, modelled as far as a synchronous run can observe them:
 * `window` and `self` are the global object; timers take their callbacks and never run them (no callback fires
 * before the script that scheduled it has finished). Everything else a browser has stays absent: code that needs
 * it fails in the guest, visibly, instead of seeing a made-up value.
 */
const HOST_MODEL = String.raw`(function () {
    globalThis.window = globalThis;
    globalThis.self = globalThis;
    var next = 1;
    function schedule() { return next++; }
    function cancel() {}
    globalThis.setTimeout = schedule;
    globalThis.setInterval = schedule;
    globalThis.requestAnimationFrame = schedule;
    globalThis.clearTimeout = cancel;
    globalThis.clearInterval = cancel;
    globalThis.cancelAnimationFrame = cancel;
    globalThis.queueMicrotask = cancel;
})();`;

export const pathName = (path: PropertyPath): string => (path.length === 0 ? "globalThis" : path.join("."));

/** Requests per `resolve` round trip: a timeout costs at most one chunk. */
const RESOLVE_CHUNK = 2000;
const RESOLVE_CHUNK_TIMEOUT_MS = 30_000;

const array = <T>(result: RunResult): T[] | undefined => (result.ok && Array.isArray(result.value) ? (result.value as T[]) : undefined);

export class Guest {
    readonly sandbox: Sandbox;
    /** The helper object: held by the host only, so no program name can collide with it or reach it. */
    readonly #api: Held;
    /**
     * Builtins whose own properties are snapshotted (aliases the setup function adds, effects outside the runtime):
     * every builtin object a name reached before the program ran (`owners` in the guest). Indexes are owner ids.
     */
    readonly owners: readonly PropertyPath[];
    /** Why the guest's state is no longer known (a batch of calls stopped partway), if it isn't. */
    #tainted: string | undefined;

    private constructor(sandbox: Sandbox, api: Held, owners: readonly PropertyPath[]) {
        this.sandbox = sandbox;
        this.#api = api;
        this.owners = owners;
    }

    static async create(): Promise<Guest> {
        const sandbox = await Sandbox.create();
        const host = sandbox.run(HOST_MODEL);
        const installed = host.ok ? sandbox.hold(GUEST_RUNTIME) : host;
        const owners = installed.ok && "held" in installed ? array<PropertyPath>(sandbox.invoke(["owners"], null, undefined, installed.held)) : undefined;
        if (!installed.ok || !("held" in installed) || owners === undefined) {
            sandbox.dispose();
            throw new Error(`guest runtime install failed: ${installed.ok ? "no helper object or owners" : installed.error}`);
        }
        return new Guest(sandbox, installed.held, owners);
    }

    /** Why the guest can't be asked anything more: the sandbox aborted, or its state is no longer known. */
    get broken(): string | undefined {
        return this.sandbox.broken ?? this.#tainted;
    }

    #invoke(helper: string, payload: unknown, timeoutMs?: number): RunResult {
        return this.sandbox.invoke([helper], payload, timeoutMs, this.#api);
    }

    /** Run one of the program's own statements in the guest's global scope, for its effects (nothing is copied out). */
    run(source: string, timeoutMs: number): RunResult {
        return this.sandbox.execute(source, timeoutMs);
    }

    /** Names the guest's global object has before any program code runs. */
    globals(): string[] {
        return array<string>(this.#invoke("globals", null)) ?? [];
    }

    /** Point the runtime helpers at the storage object (a global, after the root functions are declared). */
    bind(storage: string): boolean {
        const bound = this.#invoke("bind", storage);
        return bound.ok && bound.value === true;
    }

    snapshot(): (readonly string[])[] {
        return array<string[]>(this.#invoke("snapshot", this.owners)) ?? [];
    }

    /** Remember the owners as they are now: the baseline `ownersSince` compares with. */
    markOwners(): boolean {
        const result = this.#invoke("markOwners", this.owners);
        return result.ok && result.value === true;
    }

    /** How the owners changed since the baseline, which becomes what they are now. */
    ownersSince(): OwnersChange | undefined {
        const result = this.#invoke("ownersSince", this.owners);
        return result.ok ? (result.value as OwnersChange) : undefined;
    }

    /**
     * Storage getters handing out a function whose zero-argument call reads one global property the global object
     * lacks (observed in the guest: the only lookup that reached its prototype chain) and returns it.
     */
    globalReads(): { key: string; name: string }[] {
        return array<{ key: string; name: string }>(this.#invoke("globalReads", null)) ?? [];
    }

    /**
     * Which of the global accessors `names` forward to one global property the guest lacks: the getter hands out that
     * property's value whether it is absent or present, the setter writes it (observed in the guest).
     */
    hostAliases(names: readonly string[]): { alias: string; name: string }[] {
        return array<{ alias: string; name: string }>(this.#invoke("hostAliases", names)) ?? [];
    }

    /**
     * Replace `storage[key]` with a recorder that logs every call (`takeCalls`), with the identities of `target` (the
     * wrapper's target, a storage path) and its owner around each call.
     */
    record(key: string, target?: PropertyPath): boolean {
        const result = this.#invoke("record", { key, target: target ?? null });
        return result.ok && result.value === true;
    }

    takeCalls(): LoggedCall[] {
        return array<LoggedCall>(this.#invoke("takeCalls", null)) ?? [];
    }

    /** Identities of the object at a storage path and of the functions in its own data properties (`undefined`: not an object reached through data properties). */
    built(path: PropertyPath): BuiltIdentities | undefined {
        const result = this.#invoke("built", path);
        if (!result.ok || result.value === null || typeof result.value !== "object") return undefined;
        const { holder, methods } = result.value as { holder: number; methods: Record<string, number> };
        return { holder, methods: new Map(Object.entries(methods)) };
    }

    /** Which of `candidates` on `owner` holds the same value as `owner[alias]`. */
    aliasOf(owner: PropertyPath, alias: string, candidates: readonly string[]): string | undefined {
        const result = this.#invoke("aliasOf", { owner, alias, candidates });
        return result.ok && typeof result.value === "string" ? result.value : undefined;
    }

    /**
     * Storage getters handing out a builtin: key, owner, the builtin's name there, and how a call passes its arguments
     * on (probed, see `CallStyle`; `undefined` when not exactly one style holds).
     */
    callAliases(): { key: string; owner: PropertyPath; original: string; style: CallStyle | undefined }[] {
        type Found = { key: string; owner: number; original: string; style: CallStyle | null };
        const found = array<Found>(this.#invoke("callAliases", this.owners)) ?? [];
        return found.flatMap(({ key, owner, original, style }) => {
            const path = this.owners[owner];
            return path === undefined ? [] : [{ key, owner: path, original, style: style ?? undefined }];
        });
    }

    /** Storage keys holding the global object. */
    globalKeys(): string[] {
        return array<string>(this.#invoke("globalKeys", null)) ?? [];
    }

    /** Make each call (twice, to see whether its result repeats), in chunks. */
    resolve(requests: readonly ResolveRequest[]): ResolveResult[] {
        const results: ResolveResult[] = [];
        for (let start = 0; start < requests.length; start += RESOLVE_CHUNK) {
            const chunk = requests.slice(start, start + RESOLVE_CHUNK);
            if (this.broken !== undefined) {
                results.push(...chunk.map((): ResolveResult => ({ ok: false, error: `not asked: ${this.broken}` })));
                continue;
            }
            const answered = this.#invoke("resolve", chunk, RESOLVE_CHUNK_TIMEOUT_MS);
            const values = array<ResolveResult>(answered);
            if (values !== undefined) {
                results.push(...values);
                continue;
            }
            // The batch stopped somewhere inside: the calls it made may have moved the runtime's state, and nothing
            // says which. Nothing asks this guest anything more.
            const failure = answered.ok ? "malformed answer" : answered.error;
            this.#tainted = `a batch of calls failed partway (${failure}), leaving the guest's state unknown`;
            results.push(...chunk.map((): ResolveResult => ({ ok: false, error: failure })));
        }
        return results;
    }

    /** `left op right` (an equality) of the values at two storage paths, as the snapshot holds them. */
    compare(requests: readonly { left: PropertyPath; right: PropertyPath; op: string }[]): ({ ok: true; value: boolean } | { ok: false; reason: string })[] {
        const answered = this.#invoke("compare", requests);
        return array<{ ok: true; value: boolean } | { ok: false; reason: string }>(answered) ?? requests.map(() => ({ ok: false as const, reason: answered.ok ? "malformed answer" : answered.error }));
    }

    /** A state key for the value at `path` on the storage object: objects by identity, primitives by value. */
    stateKey(path: PropertyPath): string | undefined {
        const result = this.#invoke("stateKey", path);
        return result.ok && typeof result.value === "string" ? result.value : undefined;
    }

    /** `typeof storage.path`, and whether every step to it is a data property (reading it runs no code). */
    inspect(path: PropertyPath): { type: string; data: boolean } | undefined {
        const result = this.#invoke("inspect", path);
        return result.ok ? (result.value as { type: string; data: boolean }) : undefined;
    }

    /** Keys of the storage object's own properties a call could reach: function values and getters. */
    ownCallables(): string[] | undefined {
        const result = this.#invoke("ownCallables", null);
        return result.ok && Array.isArray(result.value) ? (result.value as string[]) : undefined;
    }

    /** Make a call and report whether it changed anything outside its own state (builtins, globals, storage keys). */
    effectFree(call: ResolveRequest): boolean {
        const result = this.#invoke("effectFree", { owners: this.owners, call });
        return result.ok && result.value === true;
    }

    dispose(): void {
        this.sandbox.dispose();
    }
}
