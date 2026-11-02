/**
 * The guest side of `Guest` (guest.ts), as source: `HOST_MODEL`, then the runtime, which evaluates to the helper object
 * only the host holds. The runtime's parts run in order in one function scope; each uses what earlier ones define.
 */

/** How far ahead the second lane's clock runs: about forty years, past any plausible date lock. */
const CLOCK_SHIFT_MS = 40 * 365.25 * 24 * 60 * 60 * 1000;

/**
 * Host globals of the web platform the guest lacks: a read of one (also `typeof`, `in`, through the global object) is an
 * environment read, since a browser has it (model 10). Other absent globals (`globalThis.prototype`, page-script
 * globals) are absent in the guest and answer as such. Kept here, in one place.
 */
const WEB_GLOBALS: readonly string[] = [
    // Document, browser and window state.
    "document",
    "navigator",
    "location",
    "history",
    "screen",
    "frames",
    "parent",
    "top",
    "opener",
    "frameElement",
    "origin",
    "name",
    "status",
    "closed",
    "length",
    "event",
    "external",
    "chrome",
    "visualViewport",
    "customElements",
    "isSecureContext",
    "crossOriginIsolated",
    "devicePixelRatio",
    "innerWidth",
    "innerHeight",
    "outerWidth",
    "outerHeight",
    "screenX",
    "screenY",
    "screenLeft",
    "screenTop",
    "scrollX",
    "scrollY",
    "pageXOffset",
    "pageYOffset",
    // Storage, network, timing, crypto.
    "localStorage",
    "sessionStorage",
    "indexedDB",
    "caches",
    "cookieStore",
    "XMLHttpRequest",
    "fetch",
    "WebSocket",
    "EventSource",
    "Request",
    "Response",
    "Headers",
    "performance",
    "PerformanceObserver",
    "crypto",
    "Intl",
    // Window functions.
    "matchMedia",
    "getComputedStyle",
    "getSelection",
    "requestIdleCallback",
    "cancelIdleCallback",
    "postMessage",
    "addEventListener",
    "removeEventListener",
    "dispatchEvent",
    "alert",
    "confirm",
    "prompt",
    "open",
    "close",
    "print",
    "focus",
    "blur",
    "scroll",
    "scrollTo",
    "scrollBy",
    "moveTo",
    "resizeTo",
    "atob",
    "btoa",
    "structuredClone",
    "reportError",
    // Interfaces.
    "Window",
    "Document",
    "HTMLDocument",
    "Navigator",
    "Location",
    "History",
    "Screen",
    "Storage",
    "Node",
    "Element",
    "HTMLElement",
    "Event",
    "CustomEvent",
    "EventTarget",
    "NodeFilter",
    "MutationObserver",
    "IntersectionObserver",
    "ResizeObserver",
    "DOMParser",
    "XMLSerializer",
    "Image",
    "Audio",
    "Blob",
    "File",
    "FileReader",
    "FormData",
    "URL",
    "URLSearchParams",
    "AbortController",
    "TextEncoder",
    "TextDecoder",
    "Worker",
    "SharedWorker",
    "ServiceWorker",
    "Notification",
    "BroadcastChannel",
    "MessageChannel",
    "WebAssembly",
    "CSS",
    "Range",
    "Selection",
];

/** Builtins as captured before the program runs. */
const PRIMORDIALS = String.raw`
    // Builtins as they were before the program ran: the helpers never use what it adds or replaces.
    var uncurry = Function.prototype.bind.bind(Function.prototype.call);
    var global = globalThis, ObjectCtor = Object, ObjectProto = Object.prototype, ArrayProto = Array.prototype, ErrorProto = Error.prototype;
    var names = Object.getOwnPropertyNames, describe = Object.getOwnPropertyDescriptor, define = Object.defineProperty;
    var protoOf = Object.getPrototypeOf, setProto = Object.setPrototypeOf, create = Object.create, hasOwn = Object.hasOwn, is = Object.is;
    var apply = Reflect.apply, construct = Reflect.construct, reflectGet = Reflect.get, reflectHas = Reflect.has, reflectSet = Reflect.set, deleteProperty = Reflect.deleteProperty, reflectDefine = Reflect.defineProperty;
    var toText = String, ProxyCtor = Proxy, MapCtor = Map, SetCtor = Set, WeakMapCtor = WeakMap, WeakSetCtor = WeakSet;
    var mapGet = uncurry(Map.prototype.get), mapSet = uncurry(Map.prototype.set), mapHas = uncurry(Map.prototype.has);
    var setAdd = uncurry(Set.prototype.add), setHas = uncurry(Set.prototype.has);
    var weakGet = uncurry(WeakMap.prototype.get), weakSet = uncurry(WeakMap.prototype.set), weakHas = uncurry(WeakMap.prototype.has);
    var weakSetAdd = uncurry(WeakSet.prototype.add), weakSetHas = uncurry(WeakSet.prototype.has);
    var sort = uncurry(Array.prototype.sort);
    // QuickJS's own: where a function made from source starts, and the file name of the run that made it.
    var positionGetters = [describe(Function.prototype, "fileName"), describe(Function.prototype, "lineNumber"), describe(Function.prototype, "columnNumber")];`;

/** Value and property helpers: `dataIn`/`dataFrom` run no program code, `from` reads as the program does. */
const HELPERS = String.raw`

    function isObject(v) { return v !== null && (typeof v === "object" || typeof v === "function"); }
    function addOnce(list, value) {
        for (var i = 0; i < list.length; i++) if (list[i] === value) return;
        push(list, value);
    }
    function push(list, value) { define(list, list.length, { __proto__: null, value: value, writable: true, enumerable: true, configurable: true }); }
    function copy(list, end) {
        var out = [];
        for (var i = 0; i < end; i++) push(out, list[i]);
        return out;
    }
    function plain(v) { return isObject(v) || typeof v === "symbol" || typeof v === "bigint" ? { nonPrimitive: typeof v } : v; }
    /** v[key] as { value } when the property found (own or inherited) is a data property (reading it runs no code); else null. */
    function dataIn(v, key) {
        var holder = ObjectCtor(v), d;
        while (holder !== null && (d = describe(holder, key)) === undefined) holder = protoOf(holder);
        return d !== undefined && hasOwn(d, "value") ? { value: d.value } : null;
    }
    function dataFrom(base, path) {
        var v = base;
        for (var i = 0; i < path.length; i++) {
            if (v === null || v === undefined) return null;
            var found = dataIn(v, path[i]);
            if (found === null) return null;
            v = found.value;
        }
        return { value: v };
    }
    /** As the program reads it: getters run. */
    function from(base, path) {
        var v = base;
        for (var i = 0; i < path.length; i++) {
            if (v === null || v === undefined) return undefined;
            v = v[path[i]];
        }
        return v;
    }`;

/** Environment reads: the read noted, the global object's prototype that sees lookups of missing globals. */
const ENVIRONMENT = String.raw`

    // Environment reads (see Guest): the first since the last take, as a reason. A probe watching lookups of missing
    // globals (listener) gets them instead. A host global's read and Math.random aren't: they set checkRead, and the
    // answer is checked by a second lane (see Guest).
    var envRead = null, listener = null, checkRead = false;
    function note(reason) { if (envRead === null) envRead = reason; }
    var webGlobals = new SetCtor();
    var webNames = ${JSON.stringify(WEB_GLOBALS)};
    for (var w = 0; w < webNames.length; w++) setAdd(webGlobals, webNames[w]);
    function look(key) {
        if (listener !== null) listener.read(key);
        else if (setHas(webGlobals, key)) checkRead = true;
    }
    // In the global object's prototype chain, where only lookups of names the global object lacks arrive.
    var envProxy = new ProxyCtor(create(ObjectProto), {
        __proto__: null,
        get: function (target, key, receiver) { look(key); return reflectGet(target, key, receiver); },
        has: function (target, key) { look(key); return reflectHas(target, key); },
        set: function (target, key, value, receiver) { return listener !== null && listener.write !== undefined ? listener.write(key, value) : reflectSet(target, key, value, receiver); }
    });
    function takeEnv() {
        if (protoOf(global) !== envProxy) note("the program replaced the global object's prototype, which hides its reads of host globals");
        var read = envRead;
        envRead = null;
        return read;
    }`;

/** Stand-ins for builtins: the program sees the original's text, or native code's. */
const STAND_INS = String.raw`
    // Functions the guest made for the host (its model's console and timers, the stack accessor, the second lane's
    // stubs) show the text QuickJS gives native functions, as the guest's builtins do; stand-ins for functions that
    // exist anyway (wrapped builtins, recorders) show the original's text. Either way the program sees no made-up text.
    var introduced = new WeakSetCtor();
    function introduce(fn) { if (isObject(fn)) weakSetAdd(introduced, fn); return fn; }
    var originals = new WeakMapCtor();
    function standIn(fn, original) { weakSet(originals, fn, original); return fn; }
    /** Replaces owner[key] by a stand-in that calls check (with its this) first. */
    function wrapMethod(owner, key, check) {
        var d = describe(owner, key);
        if (d === undefined || !hasOwn(d, "value") || typeof d.value !== "function") return;
        var original = d.value;
        var method = standIn(({ [key]() { "use strict"; check(this); return apply(original, this, arguments); } })[key], original);
        define(method, "length", { __proto__: null, value: original.length });
        define(owner, key, { __proto__: null, value: method });
    }
    function noting(reason) { return function () { note(reason); }; }
    /**
     * The constructor's stand-in: same name, length, prototype and statics. before maps the arguments, call (if any)
     * answers a call without new, and after sees what was made.
     */
    function wrapConstructor(Real, before, after, call) {
        var name = Real.name;
        var Wrapper = standIn(({ [name]: function () {
            "use strict";
            var args = before === null ? arguments : before(arguments);
            var made = new.target !== undefined ? construct(Real, args, new.target === Wrapper ? Real : new.target) : call !== undefined ? call() : apply(Real, undefined, args);
            if (after !== null) after(made);
            return made;
        } })[name], Real);
        define(Wrapper, "length", { __proto__: null, value: Real.length });
        define(Wrapper, "prototype", { __proto__: null, value: Real.prototype, writable: false });
        var statics = names(Real);
        for (var i = 0; i < statics.length; i++) {
            if (statics[i] !== "length" && statics[i] !== "name" && statics[i] !== "prototype") define(Wrapper, statics[i], describe(Real, statics[i]));
        }
        define(Real.prototype, "constructor", { __proto__: null, value: Wrapper });
        setProto(Wrapper, protoOf(Real));
        define(global, name, { __proto__: null, value: Wrapper });
        return Wrapper;
    }`;

/** The builtins that read the environment (time, locale, error stacks), wrapped to note it; the host model's functions. */
const watchedBuiltins = (stubbed: boolean): string => String.raw`
    // Date isn't tainted: like Math.random it starts the second lane, whose clock runs about forty years ahead
    // (CLOCK_SHIFT_MS). A difference of two times agrees between the lanes, an absolute date doesn't.
    var realNow = Date.now, RealDate = Date, clockShift = ${stubbed} ? ${CLOCK_SHIFT_MS} : 0;
    function now() { return realNow() + clockShift; }
    var DateWrapper = wrapConstructor(
        Date,
        function (args) { checkRead = true; return args.length === 0 ? [now()] : args; },
        null,
        function () { return toText(construct(RealDate, [now()])); }
    );
    // Not wrapMethod: the second lane's now is shifted, not the original's.
    define(DateWrapper, "now", { __proto__: null, value: standIn({ now() { "use strict"; checkRead = true; return now(); } }.now, realNow) });
    wrapMethod(DateWrapper, "parse", function () { checkRead = true; });
    wrapMethod(Math, "random", function () { checkRead = true; });
    var realToString = Function.prototype.toString;
    var toStringMethod = standIn({ toString() {
        "use strict";
        var shown = this;
        while (weakHas(originals, shown)) shown = weakGet(originals, shown);
        if (weakSetHas(introduced, shown)) {
            var name = describe(shown, "name");
            return "function " + (name !== undefined && hasOwn(name, "value") && typeof name.value === "string" ? name.value : "") + "() {\n    [native code]\n}";
        }
        return apply(realToString, shown, arguments);
    } }.toString, realToString);
    define(toStringMethod, "length", { __proto__: null, value: 0 });
    define(Function.prototype, "toString", { __proto__: null, value: toStringMethod });
    var locale = noting("uses the locale");
    wrapMethod(Number.prototype, "toLocaleString", locale);
    wrapMethod(BigInt.prototype, "toLocaleString", locale);
    wrapMethod(String.prototype, "localeCompare", locale);
    wrapMethod(String.prototype, "toLocaleLowerCase", locale);
    wrapMethod(String.prototype, "toLocaleUpperCase", locale);
    // Constructed errors keep their stack where only an accessor on Error.prototype reads it (as in Firefox).
    var stacks = new WeakMapCtor();
    function conceal(error) {
        var d = isObject(error) ? describe(error, "stack") : undefined;
        if (d === undefined || !hasOwn(d, "value")) return;
        weakSet(stacks, error, d.value);
        deleteProperty(error, "stack");
    }
    var ErrorWrapper = wrapConstructor(Error, null, conceal);
    var subclasses = ["EvalError", "RangeError", "ReferenceError", "SyntaxError", "TypeError", "URIError", "AggregateError"];
    for (var s = 0; s < subclasses.length; s++) setProto(wrapConstructor(global[subclasses[s]], null, conceal), ErrorWrapper);
    var stackAccessor = describe({
        get stack() { note("reads an error's stack"); return isObject(this) ? weakGet(stacks, this) : undefined; },
        set stack(value) { if (isObject(this)) define(this, "stack", { __proto__: null, value: value, writable: true, enumerable: false, configurable: true }); }
    }, "stack");
    introduce(stackAccessor.get);
    introduce(stackAccessor.set);
    define(ErrorProto, "stack", { __proto__: null, get: stackAccessor.get, set: stackAccessor.set, enumerable: false, configurable: true });
    // The host model's functions (HOST_MODEL ran first).
    var hosted = ["setTimeout", "setInterval", "requestAnimationFrame", "clearTimeout", "clearInterval", "cancelAnimationFrame", "queueMicrotask"];
    for (var h = 0; h < hosted.length; h++) introduce(global[hosted[h]]);
    var consoleNames = names(global.console);
    for (var c = 0; c < consoleNames.length; c++) introduce(global.console[consoleNames[c]]);
    // QuickJS's own; no browser has it.
    deleteProperty(global, "InternalError");
    setProto(global, envProxy);`;

/** The second lane's stubs for host globals, and the ways helpers see past them. */
const hostStubs = (stubbed: boolean): string => String.raw`
    // The second lane's host globals: any use answers with the stub itself (a primitive conversion with the name). A
    // call, a construction or a write is an effect on the host, which no lane sees: hostEffect says so.
    var stubs = new MapCtor(), stubCount = 0, hostEffect = false;
    function stubOf(name) {
        var stubGetter = introduce(describe({ get value() { return stub; } }, "value").get);
        var stub = introduce(new ProxyCtor(function () { "use strict"; }, {
            __proto__: null,
            get: function (target, key) {
                if (key === toPrimitive) return function () { return "[object " + name + "]"; };
                // Builtins reached on a host object are the builtins (model 7): bind makes no effect, call does.
                if (typeof key === "string" && hasOwn(builtinMethods, key)) return reflectGet(target, key, stub);
                return stub;
            },
            apply: function () { hostEffect = true; return stub; },
            construct: function () { hostEffect = true; return stub; },
            set: function () { hostEffect = true; return true; },
            defineProperty: function (target, key, descriptor) { hostEffect = true; return reflectDefine(target, key, descriptor); },
            deleteProperty: function (target, key) { hostEffect = true; return deleteProperty(target, key); },
            // Reflection finds what a read finds (a host object's members exist, model 10): an attribute, as WebIDL
            // makes them, whose getter hands out the stub.
            getOwnPropertyDescriptor: function (target, key) {
                var own = describe(target, key);
                return own !== undefined || typeof key !== "string" ? own : { __proto__: null, get: stubGetter, set: undefined, enumerable: false, configurable: true };
            }
        }));
        return stub;
    }
    var toPrimitive = Symbol.toPrimitive;
    var builtinMethods = create(null);
    var methodOwners = [Function.prototype, ObjectProto];
    for (var m = 0; m < methodOwners.length; m++) {
        var methodNames = names(methodOwners[m]);
        for (var k = 0; k < methodNames.length; k++) {
            var described = describe(methodOwners[m], methodNames[k]);
            if (hasOwn(described, "value") && typeof described.value === "function" && methodNames[k] !== "constructor") builtinMethods[methodNames[k]] = true;
        }
    }
    if (${stubbed}) {
        for (var n = 0; n < webNames.length; n++) {
            if (hasOwn(global, webNames[n])) continue;
            mapSet(stubs, webNames[n], stubOf(webNames[n]));
            stubCount++;
            define(global, webNames[n], { __proto__: null, value: mapGet(stubs, webNames[n]), writable: true, enumerable: false, configurable: true });
        }
    }
    /** Whether the global property key still holds its stub. */
    function isStub(key) {
        if (!mapHas(stubs, key)) return false;
        var d = describe(global, key);
        return d !== undefined && hasOwn(d, "value") && d.value === mapGet(stubs, key);
    }
    /** The owner's own names, the stubs left out: both lanes answer alike where the program didn't touch them. */
    function ownNames(owner) {
        var keys = names(owner);
        if (owner !== global || stubCount === 0) return keys;
        var out = [];
        for (var i = 0; i < keys.length; i++) if (!isStub(keys[i])) push(out, keys[i]);
        return out;
    }
    /** Probes of what an accessor reads need the host globals absent: the stubs step aside meanwhile. */
    function withoutStubs(run) {
        var removed = [], keys = names(global), i;
        for (i = 0; i < keys.length; i++) {
            if (!isStub(keys[i])) continue;
            deleteProperty(global, keys[i]);
            push(removed, keys[i]);
        }
        try {
            return run();
        } finally {
            for (i = 0; i < removed.length; i++) define(global, removed[i], { __proto__: null, value: mapGet(stubs, removed[i]), writable: true, enumerable: false, configurable: true });
        }
    }`;

/** The storage object, the calls logged on it, identities, and the owners' states `ownersSince` compares. */
const OWNER_STATE = String.raw`

    var store = null;
    var calls = [];
    var ids = new MapCtor(), nextId = 1;
    function idOf(v) {
        if (!mapHas(ids, v)) mapSet(ids, v, nextId++);
        return mapGet(ids, v);
    }
    function describeValue(v) { return isObject(v) ? "#" + idOf(v) : typeof v + ":" + toText(v); }
    /** owner[key] for one of its own properties; Error.prototype.stack (ours, see above) is skipped, it notes a read. */
    function ownValue(owner, key) {
        var d = describe(owner, key);
        if (d === undefined) return undefined;
        if (hasOwn(d, "value")) return d.value;
        return d.get === stackAccessor.get ? undefined : owner[key];
    }
    function identityAt(path) {
        var found = dataFrom(store, path);
        return found !== null && isObject(found.value) ? idOf(found.value) : null;
    }
    /** Whether an object has an own property named like an array index. */
    function hasIndex(o) {
        var keys = names(o);
        for (var i = 0; i < keys.length; i++) if (toText(keys[i] >>> 0) === keys[i] && keys[i] !== "4294967295") return true;
        return false;
    }
    /** Whether the descriptor d is what state recorded for its property j. */
    function recorded(d, state, j) {
        return hasOwn(d, "value") ? !state.accessor[j] && is(d.value, state.values[j]) : state.accessor[j] && is(d.get, state.values[j]) && is(d.set, state.setters[j]);
    }
    /**
     * One owner's own properties as they are now, in their own order (a change of order is a change), values kept as
     * they are: comparing two states needs no strings. The owner's last state (previous) comes back as it is when
     * nothing changed, so two states compare by identity (sameOwners); otherwise the properties up to the first
     * difference are previous's, and only the rest is recorded again.
     */
    function ownerState(owner, previous) {
        if (!isObject(owner)) return null;
        var keys = ownNames(owner), same = 0;
        if (previous !== null) {
            var shared = keys.length < previous.names.length ? keys.length : previous.names.length;
            while (same < shared && keys[same] === previous.names[same] && recorded(describe(owner, keys[same]), previous, same)) same++;
            if (same === keys.length && same === previous.names.length) return previous;
        }
        var values = previous === null ? [] : copy(previous.values, same);
        var setters = previous === null ? [] : copy(previous.setters, same);
        var accessor = previous === null ? [] : copy(previous.accessor, same);
        for (var j = same; j < keys.length; j++) {
            var d = describe(owner, keys[j]);
            var isData = hasOwn(d, "value");
            push(accessor, !isData);
            push(values, isData ? d.value : d.get);
            push(setters, isData ? undefined : d.set);
        }
        return { __proto__: null, names: keys, values: values, setters: setters, accessor: accessor };
    }
    function ownerAt(path) {
        var found = dataFrom(global, path);
        return found === null ? null : found.value;
    }
    /** The owners' states (ownerState, given previous's), plus how many accessors the storage object has. */
    function ownersState(owners, previous) {
        var states = [];
        for (var i = 0; i < owners.length; i++) push(states, ownerState(ownerAt(owners[i]), previous === undefined ? null : previous.owners[i]));
        var accessors = 0;
        var keys = isObject(store) ? names(store) : [];
        for (var k = 0; k < keys.length; k++) if (!hasOwn(describe(store, keys[k]), "value")) accessors++;
        return { __proto__: null, owners: states, accessors: accessors };
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
                push(entries, [i, s.names[j], s.accessor[j] ? "get " + describeValue(s.values[j]) + " set " + describeValue(s.setters[j]) : describeValue(s.values[j])]);
            }
        }
        return entries;
    }
    function entryKey(e) { return e[0] + "\u0000" + e[1] + "\u0000" + e[2]; }
    function keySet(entries) {
        var set = new SetCtor();
        for (var i = 0; i < entries.length; i++) setAdd(set, entryKey(entries[i]));
        return set;
    }
    function missingFrom(entries, set) {
        var out = [];
        for (var i = 0; i < entries.length; i++) if (!setHas(set, entryKey(entries[i]))) push(out, entries[i]);
        return out;
    }
    /** The owners as last marked (markOwners, ownersSince): compared with in the guest, so only changes are copied out. */
    var baseline = null;
    function ownersSince(owners) {
        var before = baseline, after = ownersState(owners, before);
        baseline = after;
        var same = sameOwners(before, after);
        var change = { same: same, accessorsBefore: before.accessors, accessorsAfter: after.accessors, changed: [], added: [], namesBefore: create(null) };
        if (same) return change;
        var beforeEntries = entriesOf(before), afterEntries = entriesOf(after);
        change.changed = missingFrom(beforeEntries, keySet(afterEntries));
        change.added = missingFrom(afterEntries, keySet(beforeEntries));
        for (var i = 0; i < change.added.length; i++) {
            var index = change.added[i][0];
            if (change.namesBefore[index] === undefined) change.namesBefore[index] = before.owners[index] === null ? [] : before.owners[index].names;
        }
        return change;
    }`;

/** Probes the helpers share: a call alias's style, a call by path, the storage object's getters. */
const PROBES = String.raw`
    /**
     * How a call alias passes its arguments on, probed with spies:
     * - "static": G.alias(7, 8) calls owner[name] with this = owner;
     * - "method": G.alias(r, 7, 8) calls r[name](7, 8), dispatching on the receiver, and a missing receiver throws
     *   (as undefined.name() would);
     * - "call": G.alias(r, 7, 8) calls owner[name] with this = r.
     * Exactly one must hold, or the answer is null and the alias can't be rewritten.
     */
    function styleOf(fn, owner, name) {
        var count, self, args;
        function spy() { count++; self = this; args = copy(arguments, arguments.length); return spy; }
        function saw(receiver) { return count === 1 && self === receiver && args.length === 2 && args[0] === 7 && args[1] === 8; }
        function probe(run) {
            count = 0;
            try { return run() === spy; } catch (e) { return false; }
        }
        var original = owner[name], isStatic = false, isCall = false, isMethod = false;
        var receiver = create(null);
        try {
            owner[name] = spy;
            isStatic = probe(function () { return fn(7, 8); }) && saw(owner);
            isCall = probe(function () { return fn(receiver, 7, 8); }) && saw(receiver);
        } finally {
            owner[name] = original;
        }
        var dispatching = create(null);
        dispatching[name] = spy;
        isMethod = probe(function () { return fn(dispatching, 7, 8); }) && saw(dispatching);
        if (isMethod) {
            try { fn(undefined, 7, 8); isMethod = false; } catch (e) {}
        }
        var styles = (isStatic ? 1 : 0) + (isCall ? 1 : 0) + (isMethod ? 1 : 0);
        return styles !== 1 ? null : isStatic ? "static" : isCall ? "call" : "method";
    }
    function call(request) {
        var owner = from(store, copy(request.path, request.path.length - 1));
        var result = apply(owner[request.path[request.path.length - 1]], owner, request.args);
        return request.lookup !== undefined ? from(result, request.lookup) : result;
    }
    /** Own getters of the storage object, as [key, getter's value] pairs; getters run (they are the program's). */
    function getterKeys() {
        var keys = isObject(store) ? names(store) : [], out = [];
        for (var i = 0; i < keys.length; i++) {
            var d = describe(store, keys[i]);
            if (d !== undefined && hasOwn(d, "get") && typeof d.get === "function") push(out, keys[i]);
        }
        return out;
    }
    /** Where a function the program's source made starts ({ file, line, column }), or null for any other value. */
    function siteOf(fn) {
        if (typeof fn !== "function") return null;
        var site = [];
        for (var i = 0; i < positionGetters.length; i++) {
            var d = positionGetters[i];
            if (d === undefined || typeof d.get !== "function") return null;
            push(site, apply(d.get, fn, []));
        }
        return typeof site[0] === "string" && typeof site[1] === "number" && typeof site[2] === "number" ? { file: site[0], line: site[1], column: site[2] } : null;
    }
    function functionRecord(fn) { return isObject(fn) ? { id: idOf(fn), site: siteOf(fn) } : null; }`;

/** The helpers, each wrapped to report whether a second lane must check its answer. */
const API = String.raw`
    /**
     * Every builtin object reachable by name before the program runs: the global object, each global data property
     * holding an object or function, and each such function's prototype, once per object. Taken now, before any
     * program code; the second lane's stubs are left out, so both lanes number the owners alike.
     */
    var ownerPaths = [[]], ownerIndex = new MapCtor();
    mapSet(ownerIndex, global, 0);
    (function () {
        function add(path, value) {
            if (!isObject(value) || mapHas(ownerIndex, value)) return;
            mapSet(ownerIndex, value, ownerPaths.length);
            push(ownerPaths, path);
        }
        var keys = ownNames(global), data = [], i;
        for (i = 0; i < keys.length; i++) {
            var d = describe(global, keys[i]);
            push(data, hasOwn(d, "value") ? d.value : undefined);
            add([keys[i]], data[i]);
        }
        for (i = 0; i < keys.length; i++) {
            if (typeof data[i] !== "function") continue;
            var p = describe(data[i], "prototype");
            if (p !== undefined && hasOwn(p, "value")) add([keys[i], "prototype"], p.value);
        }
    })();
    function ownerOf(v) { return isObject(v) && mapHas(ownerIndex, v) ? mapGet(ownerIndex, v) : -1; }
    var api = {
        globals: function () { return ownNames(global); },
        owners: function () { return ownerPaths; },
        bind: function (name) {
            var found = dataFrom(global, [name]);
            store = found === null ? null : found.value;
            return isObject(store);
        },
        snapshot: function (owners) {
            var out = [];
            for (var i = 0; i < owners.length; i++) {
                var owner = ownerAt(owners[i]);
                push(out, isObject(owner) ? ownNames(owner) : []);
            }
            return out;
        },
        markOwners: function (owners) { baseline = ownersState(owners); return true; },
        ownersSince: ownersSince,
        record: function (request) {
            var key = request.key, target = request.target;
            var d = isObject(store) ? describe(store, key) : undefined;
            if (d === undefined || !hasOwn(d, "value") || typeof d.value !== "function") return false;
            var fn = d.value;
            var recorder = standIn(function () {
                var owner = target === null ? null : identityAt(copy(target, target.length - 1));
                var before = target === null ? null : identityAt(target);
                var result = apply(fn, this, arguments);
                var args = [];
                for (var i = 0; i < arguments.length; i++) push(args, plain(arguments[i]));
                var logged = { __proto__: null, key: key, args: args, result: plain(result), owner: owner, before: before, after: target === null ? null : identityAt(target) };
                if (typeof result === "number") logged.indexed = hasIndex(ArrayProto) || hasIndex(ObjectProto);
                push(calls, logged);
                return result;
            }, fn);
            store[key] = recorder;
            var now = describe(store, key);
            return now !== undefined && hasOwn(now, "value") && now.value === recorder;
        },
        built: function (path) {
            var holder = dataFrom(store, path);
            if (holder === null || !isObject(holder.value)) return null;
            var methods = [];
            var keys = ownNames(holder.value);
            for (var i = 0; i < keys.length; i++) {
                var d = describe(holder.value, keys[i]);
                if (hasOwn(d, "value") && typeof d.value === "function") push(methods, [keys[i], idOf(d.value)]);
            }
            return { holder: idOf(holder.value), methods: methods };
        },
        takeRun: function () {
            var taken = calls;
            calls = [];
            return { calls: taken, env: takeEnv() };
        },
        aliasOf: function (request) {
            var owner = ownerAt(request.owner);
            if (!isObject(owner)) return null;
            takeEnv();
            var found = null;
            try {
                var value = owner[request.alias];
                if (value !== undefined) {
                    for (var i = 0; i < request.candidates.length && found === null; i++) {
                        try { if (ownValue(owner, request.candidates[i]) === value) found = request.candidates[i]; } catch (e) {}
                    }
                }
            } catch (e) {}
            var env = takeEnv();
            return found === null ? null : env !== null ? { env: env } : { original: found };
        },
        callAliases: function (owners) {
            var found = [], keys = getterKeys();
            for (var i = 0; i < keys.length; i++) {
                takeEnv();
                var answer = null;
                try {
                    var fn = store[keys[i]];
                    var builtin = typeof fn === "function" ? fn() : undefined;
                    // Owners in order, the global object first: a constructor is found as the global, not as some
                    // prototype's "constructor".
                    search: for (var o = 0; o < owners.length && builtin !== undefined && builtin !== null; o++) {
                        var owner = ownerAt(owners[o]);
                        if (!isObject(owner)) continue;
                        var ownerNames = ownNames(owner);
                        for (var n = 0; n < ownerNames.length; n++) {
                            try {
                                if (ownValue(owner, ownerNames[n]) !== builtin) continue;
                            } catch (e) { continue; }
                            answer = { key: keys[i], owner: o, original: ownerNames[n], style: styleOf(fn, owner, ownerNames[n]) };
                            break search;
                        }
                    }
                } catch (e) { answer = null; }
                var env = takeEnv();
                if (answer !== null) push(found, env !== null ? { key: keys[i], env: env } : answer);
            }
            return found;
        },
        globalReads: function () {
            // Getters handing out a function whose zero-argument call reads one global property the global object
            // lacks and returns it (undefined): the read is seen in the global object's prototype chain, which only
            // lookups of missing names reach.
            var found = [], keys = getterKeys();
            for (var i = 0; i < keys.length; i++) {
                var reads = [], result, ran = false;
                takeEnv();
                listener = { __proto__: null, read: function (key) { addOnce(reads, key); } };
                try {
                    var fn = store[keys[i]];
                    if (typeof fn === "function") {
                        result = fn();
                        ran = true;
                    }
                } catch (e) {} finally { listener = null; }
                if (takeEnv() !== null || !ran || result !== undefined || reads.length !== 1 || typeof reads[0] !== "string" || hasOwn(global, reads[0])) continue;
                push(found, { key: keys[i], name: reads[0] });
            }
            return found;
        },
        hostAliases: function (aliases) {
            // Global accessors forwarding to one global property the guest lacks (a host object): the getter reads it
            // and hands out its value, absent (seen in the global object's prototype chain, which only lookups of
            // missing names reach) or present (a marker put there for the probe), and the setter writes it. (An
            // accessor that looks up nothing missing can't be told apart from one reading state that changes later,
            // so it isn't answered: an alias of undefined stays.)
            var found = [];
            for (var i = 0; i < aliases.length; i++) {
                var d = describe(global, aliases[i]);
                if (d === undefined || !hasOwn(d, "get") || typeof d.get !== "function" || typeof d.set !== "function") continue;
                var reads = [], writes = [], got, marker = {}, ok = false;
                takeEnv();
                listener = {
                    __proto__: null,
                    read: function (key) { addOnce(reads, key); },
                    write: function (key, value) { push(writes, [key, value]); return true; }
                };
                try {
                    got = apply(d.get, global, []);
                    var name = reads[0];
                    if (got === undefined && reads.length === 1 && typeof name === "string" && !hasOwn(global, name)) {
                        try {
                            define(global, name, { __proto__: null, value: marker, configurable: true, writable: true });
                            got = apply(d.get, global, []);
                        } finally { deleteProperty(global, name); }
                        if (got === marker) {
                            apply(d.set, global, [marker]);
                            ok = writes.length === 1 && writes[0][0] === name && writes[0][1] === marker && !hasOwn(global, name);
                        }
                    }
                } catch (e) { ok = false; } finally { listener = null; }
                if (takeEnv() === null && ok) push(found, { alias: aliases[i], name: reads[0] });
            }
            return found;
        },
        compare: function (requests) {
            // Equality of the values at two storage paths, read through data properties only: objects by identity,
            // primitives by value; an object against a primitive would convert it, so it isn't answered.
            var out = [];
            for (var i = 0; i < requests.length; i++) {
                var request = requests[i], a = dataFrom(store, request.left), b = dataFrom(store, request.right), answer;
                if (a === null || b === null) answer = { ok: false, reason: "a step to a value is not a data property" };
                else if (isObject(a.value) !== isObject(b.value)) answer = { ok: false, reason: "an object compared with a primitive converts it" };
                else if (request.op === "===") answer = { ok: true, value: a.value === b.value };
                else if (request.op === "!==") answer = { ok: true, value: a.value !== b.value };
                else if (request.op === "==") answer = { ok: true, value: a.value == b.value };
                else if (request.op === "!=") answer = { ok: true, value: a.value != b.value };
                else answer = { ok: false, reason: "not an equality" };
                push(out, answer);
            }
            return out;
        },
        globalKeys: function () {
            var keys = isObject(store) ? names(store) : [], out = [];
            for (var i = 0; i < keys.length; i++) {
                var hit = false;
                takeEnv();
                try { hit = store[keys[i]] === global; } catch (e) {}
                if (takeEnv() === null && hit) push(out, keys[i]);
            }
            return out;
        },
        resolve: function (requests) {
            // A call whose result differs when repeated changed the runtime's state (a decoder stage, say): everything
            // after it would be answered by a runtime the program never has, so stop calling. So does one that read
            // the environment: what it wrote may differ in a real run.
            var changed = false, out = [];
            for (var i = 0; i < requests.length; i++) {
                if (changed) {
                    push(out, { ok: false, error: "after a call that changed the runtime's state", stale: true });
                    continue;
                }
                var first, second, env, answer;
                takeEnv();
                try {
                    first = call(requests[i]);
                    if (isObject(first)) answer = { ok: true, nonPrimitive: typeof first };
                    else {
                        try {
                            second = call(requests[i]);
                            if (!is(first, second)) changed = true;
                            answer = { ok: true, value: first, repeatable: !changed };
                        } catch (e) {
                            changed = true;
                            answer = { ok: true, value: first, repeatable: false };
                        }
                    }
                } catch (e) {
                    var message = isObject(e) ? describe(e, "message") : undefined;
                    answer = { ok: false, error: message !== undefined && hasOwn(message, "value") ? toText(message.value) : isObject(e) ? "a thrown " + typeof e : toText(e) };
                }
                env = takeEnv();
                if (env !== null) {
                    changed = true;
                    answer = { ok: false, error: "the call " + env + ", which a real run may answer differently", env: true, seen: isObject(first) ? undefined : first };
                }
                push(out, answer);
            }
            return out;
        },
        stateKey: function (path) {
            // Data properties only: a getter on the way would run code and could change the runtime.
            var found = dataFrom(store, path);
            if (found === null) return null;
            var v = found.value;
            if (isObject(v)) return "o:" + idOf(v);
            return typeof v === "number" ? "n:" + toText(v) : typeof v === "string" ? "s:" + v : null;
        },
        inspect: function (path) {
            // The value's type, and whether every step to it is a data property (reading it can't run code).
            var v = store, data = true;
            takeEnv();
            for (var i = 0; i < path.length && v !== null && v !== undefined; i++) {
                var holder = ObjectCtor(v), d;
                while (holder !== null && (d = describe(holder, path[i])) === undefined) holder = protoOf(holder);
                if (d !== undefined && !hasOwn(d, "value")) data = false;
                v = v[path[i]];
            }
            return takeEnv() === null ? { type: typeof v, data: data } : { type: "unknown", data: false };
        },
        ownCallables: function () {
            // The storage object's own properties a call could reach: function values, and getters (which run on access).
            var keys = names(store), out = [];
            for (var i = 0; i < keys.length; i++) {
                var d = describe(store, keys[i]);
                if (!hasOwn(d, "value") || typeof d.value === "function") push(out, keys[i]);
            }
            return out;
        },
        accessors: function (requests) {
            // Own accessors (of the storage object for a null path, else of an owner), read without running them:
            // their functions' identities and, when program source made them, where they start.
            var out = [];
            for (var i = 0; i < requests.length; i++) {
                var holder = requests[i].path === null ? store : ownerAt(requests[i].path);
                var d = isObject(holder) ? describe(holder, requests[i].key) : undefined;
                push(out, d === undefined || hasOwn(d, "value") ? null : { get: functionRecord(d.get), set: functionRecord(d.set) });
            }
            return out;
        },
        installed: function (requests) {
            // In one answer: the storage object's own accessors and the requested owner ones (as accessors answers
            // them), and each owner's own names with its accessors among them.
            var all = [], keys = isObject(store) ? names(store) : [], i, j;
            for (i = 0; i < keys.length; i++) {
                var d = describe(store, keys[i]);
                if (d !== undefined && !hasOwn(d, "value")) push(all, { path: null, key: keys[i] });
            }
            for (i = 0; i < requests.length; i++) push(all, requests[i]);
            var ownerNames = [], ownerAccessors = [];
            for (i = 0; i < ownerPaths.length; i++) {
                var owner = ownerAt(ownerPaths[i]), own = isObject(owner) ? ownNames(owner) : [], accessors = [];
                for (j = 0; j < own.length; j++) if (!hasOwn(describe(owner, own[j]), "value")) push(accessors, own[j]);
                push(ownerNames, own);
                push(ownerAccessors, accessors);
            }
            return { requests: all, accessors: api.accessors(all), names: ownerNames, accessorNames: ownerAccessors };
        },
        holdsGlobal: function (paths) {
            var out = [];
            for (var i = 0; i < paths.length; i++) {
                var found = dataFrom(store, paths[i]);
                push(out, found !== null && found.value === global);
            }
            return out;
        },
        lookup: function (requests) {
            // A property lookup on a builtin reached by data properties from the global object, run on its prototype
            // chain without running code: where it is found (an owner's index, -1 for another object), whether as
            // data, and the value (an owner's index, or a primitive). Owners are compared by identity.
            var out = [];
            for (var i = 0; i < requests.length; i++) {
                var base = dataFrom(global, requests[i].path), key = requests[i].key;
                if (base === null || base.value === null || base.value === undefined) {
                    push(out, { kind: "base" });
                    continue;
                }
                var holder = ObjectCtor(base.value), d;
                while (holder !== null && (d = describe(holder, key)) === undefined) holder = protoOf(holder);
                if (holder === null) push(out, { kind: "absent" });
                else if (!hasOwn(d, "value")) push(out, { kind: "accessor", holder: ownerOf(holder) });
                else {
                    var v = d.value;
                    push(out, { kind: "data", holder: ownerOf(holder), owner: ownerOf(v), type: typeof v, value: isObject(v) || typeof v === "symbol" || typeof v === "bigint" ? null : v });
                }
            }
            return out;
        }
    };
    // Every answer comes with whether Math.random was called since the previous one (the helper or a run before it).
    var answers = create(null), helpers = names(api);
    function envelope(helper) {
        return function (payload) {
            var value = helper === api.globalReads || helper === api.hostAliases ? withoutStubs(function () { return helper(payload); }) : helper(payload);
            var check = checkRead, effect = hostEffect;
            checkRead = false;
            hostEffect = false;
            return { value: value, check: check, effect: effect };
        };
    }
    for (var a = 0; a < helpers.length; a++) answers[helpers[a]] = envelope(api[helpers[a]]);
    return answers;`;

/**
 * An object or function is reported as `{ nonPrimitive: typeof value }`: copying it out could degrade it. `stubbed`: the
 * second lane's personality (see `Guest`), where every `WEB_GLOBALS` name the guest lacks is present.
 */
export const guestRuntime = (stubbed: boolean): string => `(function () {${PRIMORDIALS}${HELPERS}${ENVIRONMENT}${STAND_INS}${watchedBuiltins(stubbed)}${hostStubs(stubbed)}${OWNER_STATE}${PROBES}${API}
})()`;

/**
 * Browser globals as far as a synchronous run can observe them: `window`/`self` are the global object; timers never run
 * their callbacks (none fires before the scheduling script finishes); `console` is unwatched (model 5: not debugged;
 * model 10: host globals it uses exist): its methods have no visible effect and read no arguments. Everything else
 * stays absent, so code needing it fails visibly instead of seeing a made-up value (and its reads count as
 * environment reads).
 */
export const HOST_MODEL = String.raw`(function () {
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
    var console = {};
    ["assert", "clear", "count", "countReset", "debug", "dir", "dirxml", "error", "group", "groupCollapsed", "groupEnd", "info", "log", "profile", "profileEnd", "table", "time", "timeEnd", "timeLog", "timeStamp", "trace", "warn"].forEach(function (name) {
        var method = function () {}.bind(console);
        Object.defineProperty(method, "name", { value: name, configurable: true });
        console[name] = method;
    });
    Object.defineProperty(globalThis, "console", { value: console, writable: true, configurable: true, enumerable: false });
})();`;
