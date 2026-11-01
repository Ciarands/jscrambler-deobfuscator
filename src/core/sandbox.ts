import * as variantModule from "@jitl/quickjs-wasmfile-release-sync";
import { newQuickJSWASMModuleFromVariant, newVariant } from "quickjs-emscripten-core";
import type { CustomizeVariantOptions, QuickJSContext, QuickJSHandle, QuickJSRuntime, QuickJSSyncVariant, QuickJSWASMModule } from "quickjs-emscripten-core";

/**
 * QuickJS (WASM) sandbox for the obfuscator's own runtime helpers. Guest gets standard builtins only, nothing from the
 * host; plain values are copied out. Deadline plus memory/stack limits bound hostile code; `Math.random` is seeded.
 *
 * The guest is an adversary: everything crossing out goes through functions made before any guest code ran (captured
 * builtins, own data properties only, no `toJSON` or getters), arrives as text, and is checked again on the host. A
 * guest exception is described the same way, never rebuilt on the host.
 */

export interface SandboxLimits {
    readonly memoryBytes: number;
    readonly stackBytes: number;
    readonly timeoutMs: number;
}

export const DEFAULT_LIMITS: SandboxLimits = { memoryBytes: 256 * 1024 * 1024, stackBytes: 1024 * 1024, timeoutMs: 2000 };

export type RunResult =
    { readonly ok: true; readonly value: unknown } | { readonly ok: false; readonly error: string; readonly timedOut: boolean; readonly at?: { readonly line: number; readonly column: number } };

/** A guest object only the host holds (see `Sandbox.hold`): no name in the guest reaches it. */
export interface Held {
    readonly id: number;
}

let modulePromise: Promise<QuickJSWASMModule> | undefined;
const baseVariant = variantModule.default as unknown as QuickJSSyncVariant;
/** Emscripten prints aborts to stderr before throwing; silence it (the abort still surfaces as an exception). */
const silent = { print: () => {}, printErr: () => {} } as unknown as NonNullable<CustomizeVariantOptions["emscriptenModule"]>;
const syncVariant = newVariant(baseVariant, { emscriptenModule: silent });
const quickjs = (): Promise<QuickJSWASMModule> => (modulePromise ??= newQuickJSWASMModuleFromVariant(syncVariant));
/** Emscripten aborts throw it; not declared in the project's type libs. */
const WasmRuntimeError = (globalThis as unknown as { WebAssembly: { RuntimeError: abstract new (...args: never[]) => Error } }).WebAssembly.RuntimeError;

/** The default seed is what every sandbox used so far; another gives another (equally deterministic) sequence. */
export const DEFAULT_SEED = 0x9e3779b9 | 0;

const determinism = (seed: number): string => `(() => {
    let a = ${seed | 0};
    Math.random = function random() {
        a = (a + 0x6d2b79f5) | 0;
        let t = Math.imul(a ^ (a >>> 15), 1 | a);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
})();`;

/**
 * JSON with `undefined`/`NaN`/`±Infinity`/`-0` as exact one-key objects `{ "$jsd": name }`; an object key starting with
 * the tag gets it once more in front, so no carried object is ever read as a tag. Must stay in step with `TRANSPORT`.
 */
const TAG = "$jsd";
const MAX_DEPTH = 200;
const SPECIAL_NAMES: readonly string[] = ["undefined", "NaN", "Infinity", "-Infinity", "-0"];

class MalformedAnswer extends Error {}

const specialOf = (name: string): number | undefined => {
    switch (name) {
        case "NaN":
            return Number.NaN;
        case "Infinity":
            return Number.POSITIVE_INFINITY;
        case "-Infinity":
            return Number.NEGATIVE_INFINITY;
        case "-0":
            return -0;
        default:
            return undefined;
    }
};

const tagOf = (value: unknown): string | undefined => {
    if (value === undefined) return "undefined";
    if (typeof value !== "number") return undefined;
    if (Number.isNaN(value)) return "NaN";
    if (value === Number.POSITIVE_INFINITY) return "Infinity";
    if (value === Number.NEGATIVE_INFINITY) return "-Infinity";
    return Object.is(value, -0) ? "-0" : undefined;
};

const ownData = (target: object, key: string, value: unknown): void => {
    Object.defineProperty(target, key, { value, writable: true, enumerable: true, configurable: true });
};

const toWire = (value: unknown, depth: number): unknown => {
    if (depth > MAX_DEPTH) throw new MalformedAnswer("nested too deeply");
    const tag = tagOf(value);
    if (tag !== undefined) return { [TAG]: tag };
    if (Array.isArray(value)) return value.map((item: unknown) => toWire(item, depth + 1));
    if (typeof value !== "object" || value === null) return value;
    const out = {};
    for (const [key, item] of Object.entries(value)) ownData(out, key.startsWith(TAG) ? TAG + key : key, toWire(item, depth + 1));
    return out;
};

const fromWire = (raw: unknown, depth: number): unknown => {
    if (depth > MAX_DEPTH) throw new MalformedAnswer("nested too deeply");
    if (Array.isArray(raw)) return raw.map((item: unknown) => fromWire(item, depth + 1));
    if (typeof raw !== "object" || raw === null) return raw;
    const record = raw as Record<string, unknown>;
    const keys = Object.keys(record);
    if (Object.hasOwn(record, TAG)) {
        const name = record[TAG];
        if (keys.length !== 1 || typeof name !== "string" || !SPECIAL_NAMES.includes(name)) throw new MalformedAnswer("a malformed tag");
        return specialOf(name);
    }
    const out = {};
    for (const key of keys) ownData(out, key.startsWith(TAG) ? key.slice(TAG.length) : key, fromWire(record[key], depth + 1));
    return out;
};

const encode = (value: unknown): string => JSON.stringify(toWire(value, 0));

const safeMessage = (error: unknown): string => {
    try {
        return error instanceof Error ? String(error.message) : String(error);
    } catch {
        return "an error that can't be printed";
    }
};

/**
 * Guest side: `[decode, encode, describe]`, made from builtins captured before any guest code runs. Payloads become
 * null-prototype objects (a helper reading an absent key gets `undefined`, never an inherited value); results are
 * written by hand from own data properties (an accessor, a hole or a non-plain value is refused); `describe` gives a
 * thrown value's message and stack as text, reading own data properties only.
 */
const TRANSPORT = `(function () {
    "use strict";
    var TAG = ${JSON.stringify(TAG)}, MAX = ${MAX_DEPTH};
    var uncurry = Function.prototype.bind.bind(Function.prototype.call);
    var parse = JSON.parse, quote = JSON.stringify, isArray = Array.isArray, toText = String;
    var names = Object.getOwnPropertyNames, describe = Object.getOwnPropertyDescriptor, hasOwn = Object.hasOwn, define = Object.defineProperty, create = Object.create;
    var startsWith = uncurry(String.prototype.startsWith), slice = uncurry(String.prototype.slice);
    var Refused = TypeError;
    function special(name) {
        switch (name) {
            case "undefined": return void 0;
            case "NaN": return 0 / 0;
            case "Infinity": return 1 / 0;
            case "-Infinity": return -1 / 0;
            case "-0": return -0;
        }
        throw new Refused("a malformed tag");
    }
    function fromWire(raw, depth) {
        if (depth > MAX) throw new Refused("nested too deeply");
        if (raw === null || typeof raw !== "object") return raw;
        var out, i;
        if (isArray(raw)) {
            out = [];
            for (i = 0; i < raw.length; i++) define(out, i, { __proto__: null, value: fromWire(raw[i], depth + 1), writable: true, enumerable: true, configurable: true });
            return out;
        }
        var keys = names(raw);
        if (hasOwn(raw, TAG)) {
            if (keys.length !== 1 || typeof raw[TAG] !== "string") throw new Refused("a malformed tag");
            return special(raw[TAG]);
        }
        out = create(null);
        for (i = 0; i < keys.length; i++) out[startsWith(keys[i], TAG) ? slice(keys[i], TAG.length) : keys[i]] = fromWire(raw[keys[i]], depth + 1);
        return out;
    }
    function dataOf(object, key) {
        var d = describe(object, key);
        if (d === undefined || !hasOwn(d, "value")) throw new Refused("not a data property: " + key);
        return d;
    }
    function toWire(v, depth) {
        switch (typeof v) {
            case "undefined": return '{"' + TAG + '":"undefined"}';
            case "number":
                if (v !== v) return '{"' + TAG + '":"NaN"}';
                if (v === 1 / 0) return '{"' + TAG + '":"Infinity"}';
                if (v === -1 / 0) return '{"' + TAG + '":"-Infinity"}';
                if (v === 0 && 1 / v < 0) return '{"' + TAG + '":"-0"}';
                return toText(v);
            case "string": return quote(v);
            case "boolean": return v ? "true" : "false";
            case "object": if (v === null) return "null"; break;
            default: throw new Refused("can't carry a " + typeof v);
        }
        if (depth > MAX) throw new Refused("nested too deeply");
        var out, i;
        if (isArray(v)) {
            var length = dataOf(v, "length").value;
            out = "[";
            for (i = 0; i < length; i++) out += (i === 0 ? "" : ",") + toWire(dataOf(v, toText(i)).value, depth + 1);
            return out + "]";
        }
        var keys = names(v), first = true;
        out = "{";
        for (i = 0; i < keys.length; i++) {
            var d = dataOf(v, keys[i]);
            if (!d.enumerable) continue;
            out += (first ? "" : ",") + quote(startsWith(keys[i], TAG) ? TAG + keys[i] : keys[i]) + ":" + toWire(d.value, depth + 1);
            first = false;
        }
        return out + "}";
    }
    function ownText(value, key) {
        var d = describe(value, key);
        return d !== undefined && hasOwn(d, "value") && typeof d.value === "string" ? d.value : "";
    }
    return [
        function (text) { return fromWire(parse(text), 0); },
        function (value) { return toWire(value, 0); },
        function (thrown) {
            var isObject = thrown !== null && (typeof thrown === "object" || typeof thrown === "function");
            var message = isObject ? ownText(thrown, "message") : typeof thrown === "symbol" ? "a symbol" : toText(thrown);
            return "[" + quote(message) + "," + quote(isObject ? ownText(thrown, "stack") : "") + "]";
        }
    ];
})()`;

/** Time to describe a thrown value after the run's own deadline passed. */
const DESCRIBE_TIMEOUT_MS = 200;

export class Sandbox {
    readonly #runtime: QuickJSRuntime;
    readonly #context: QuickJSContext;
    readonly #limits: SandboxLimits;
    readonly #decode: QuickJSHandle;
    readonly #encode: QuickJSHandle;
    readonly #describe: QuickJSHandle;
    readonly #functions = new Map<string, { fn: QuickJSHandle; owner: QuickJSHandle }>();
    readonly #held = new Map<number, QuickJSHandle>();
    #deadline = 0;
    #interrupted = false;
    #broken: string | undefined;

    private constructor(module: QuickJSWASMModule, limits: SandboxLimits) {
        this.#limits = limits;
        this.#runtime = module.newRuntime();
        this.#runtime.setMemoryLimit(limits.memoryBytes);
        this.#runtime.setMaxStackSize(limits.stackBytes);
        this.#runtime.setInterruptHandler(() => {
            if (Date.now() <= this.#deadline) return false;
            this.#interrupted = true;
            return true;
        });
        this.#context = this.#runtime.newContext();
        this.#arm(limits.timeoutMs);
        const transport = this.#context.evalCode(TRANSPORT, "transport.js", { type: "global" });
        if (transport.error !== undefined) {
            transport.error.dispose();
            this.#context.dispose();
            this.#runtime.dispose();
            throw new Error("sandbox setup failed: the transport didn't install");
        }
        this.#decode = this.#context.getProp(transport.value, 0);
        this.#encode = this.#context.getProp(transport.value, 1);
        this.#describe = this.#context.getProp(transport.value, 2);
        transport.value.dispose();
    }

    static async create(limits: SandboxLimits = DEFAULT_LIMITS, seed = DEFAULT_SEED): Promise<Sandbox> {
        return Sandbox.fromModule(await Sandbox.load(), limits, seed);
    }

    /** The QuickJS module sandboxes run in (loaded once, shared). */
    static load(): Promise<QuickJSWASMModule> {
        return quickjs();
    }

    /** A sandbox in an already loaded module: synchronous, for one made only when first needed. */
    static fromModule(module: QuickJSWASMModule, limits: SandboxLimits = DEFAULT_LIMITS, seed = DEFAULT_SEED): Sandbox {
        const sandbox = new Sandbox(module, limits);
        const setup = sandbox.run(determinism(seed));
        if (!setup.ok) throw new Error(`sandbox setup failed: ${setup.error}`);
        return sandbox;
    }

    get broken(): string | undefined {
        return this.#broken;
    }

    /** An abort kills the WASM instance it happened in; drop it so the next sandbox loads a fresh one. */
    #abort(error: unknown): RunResult {
        this.#broken = safeMessage(error);
        modulePromise = undefined;
        return { ok: false, error: `sandbox aborted: ${this.#broken}`, timedOut: false };
    }

    #arm(timeoutMs: number): void {
        this.#deadline = Date.now() + timeoutMs;
        this.#interrupted = false;
    }

    /** The value as the guest's `encode` writes it, read back on the host; frees the handle. */
    #copy(handle: QuickJSHandle): RunResult {
        const encoded = this.#context.callFunction(this.#encode, this.#context.undefined, handle);
        handle.dispose();
        if (encoded.error !== undefined) {
            const failure = this.#failure(encoded.error);
            return failure.ok ? failure : { ...failure, error: `couldn't copy the result out: ${failure.error}` };
        }
        const text = this.#context.typeof(encoded.value) === "string" ? this.#context.getString(encoded.value) : undefined;
        encoded.value.dispose();
        if (text === undefined) return { ok: false, error: "malformed answer: not text", timedOut: false };
        try {
            return { ok: true, value: fromWire(JSON.parse(text) as unknown, 0) };
        } catch (error) {
            return { ok: false, error: `malformed answer: ${safeMessage(error)}`, timedOut: false };
        }
    }

    /** Only a WASM abort breaks the sandbox; a value that can't be copied out is an ordinary error. */
    run(code: string, timeoutMs = this.#limits.timeoutMs): RunResult {
        return this.#evaluate(code, timeoutMs, true);
    }

    execute(code: string, timeoutMs = this.#limits.timeoutMs): RunResult {
        return this.#evaluate(code, timeoutMs, false);
    }

    #evaluate(code: string, timeoutMs: number, copy: boolean): RunResult {
        if (this.#broken !== undefined) return { ok: false, error: `sandbox aborted earlier: ${this.#broken}`, timedOut: false };
        try {
            this.#arm(timeoutMs);
            const result = this.#context.evalCode(code, "sandbox.js", { type: "global" });
            if (result.error !== undefined) return this.#failure(result.error);
            if (copy) return this.#copy(result.value);
            result.value.dispose();
            return { ok: true, value: undefined };
        } catch (error) {
            return this.#hostFailure(error);
        }
    }

    /**
     * Keep an expression's value host-side only, so helpers can't collide with or show up among program globals.
     * `filename` names its frames in guest stacks (`RunResult.at` looks for the program's).
     */
    hold(code: string, timeoutMs = this.#limits.timeoutMs, filename = "sandbox.js"): { readonly ok: true; readonly held: Held } | (RunResult & { readonly ok: false }) {
        if (this.#broken !== undefined) return { ok: false, error: `sandbox aborted earlier: ${this.#broken}`, timedOut: false };
        try {
            this.#arm(timeoutMs);
            const result = this.#context.evalCode(code, filename, { type: "global" });
            if (result.error !== undefined) return this.#failure(result.error) as RunResult & { readonly ok: false };
            const held = { id: this.#held.size + 1 };
            this.#held.set(held.id, result.value);
            return { ok: true, held };
        } catch (error) {
            return this.#hostFailure(error) as RunResult & { readonly ok: false };
        }
    }

    /** Call a guest function by property path from `base` (or the global object); payload and result cross as tagged JSON. */
    invoke(path: readonly string[], payload: unknown, timeoutMs = this.#limits.timeoutMs, base?: Held): RunResult {
        if (this.#broken !== undefined) return { ok: false, error: `sandbox aborted earlier: ${this.#broken}`, timedOut: false };
        const context = this.#context;
        try {
            this.#arm(timeoutMs);
            const target = this.#lookup(path, base);
            if (target === undefined) return { ok: false, error: `no guest function ${path.join(".")}`, timedOut: false };
            const text = context.newString(encode(payload));
            const argument = context.callFunction(this.#decode, context.undefined, text);
            text.dispose();
            if (argument.error !== undefined) return this.#failure(argument.error);
            const result = context.callFunction(target.fn, target.owner, argument.value);
            argument.value.dispose();
            if (result.error !== undefined) return this.#failure(result.error);
            return this.#copy(result.value);
        } catch (error) {
            return this.#hostFailure(error);
        }
    }

    #lookup(path: readonly string[], base?: Held): { fn: QuickJSHandle; owner: QuickJSHandle } | undefined {
        const key = `${base?.id ?? 0}:${path.join(".")}`;
        const cached = this.#functions.get(key);
        if (cached !== undefined) return cached;
        const context = this.#context;
        const start = base === undefined ? context.global : this.#held.get(base.id);
        if (start === undefined) return undefined;
        const own = (handle: QuickJSHandle): boolean => handle !== start;
        let owner: QuickJSHandle = start;
        for (const segment of path.slice(0, -1)) {
            const next = context.getProp(owner, segment);
            if (own(owner)) owner.dispose();
            owner = next;
        }
        const fn = context.getProp(owner, path.at(-1) ?? "");
        if (context.typeof(fn) !== "function") {
            fn.dispose();
            if (own(owner)) owner.dispose();
            return undefined;
        }
        const entry = { fn, owner: own(owner) ? owner : start };
        this.#functions.set(key, entry);
        return entry;
    }

    /** The thrown value as the guest's `describe` tells it (own data properties only); frees the handle. */
    #failure(handle: QuickJSHandle): RunResult & { readonly ok: false } {
        const timedOut = this.#interrupted;
        let message = "a failure the guest couldn't describe";
        let stack = "";
        try {
            this.#arm(DESCRIBE_TIMEOUT_MS);
            const described = this.#context.callFunction(this.#describe, this.#context.undefined, handle);
            if (described.error !== undefined) described.error.dispose();
            else {
                const text = this.#context.typeof(described.value) === "string" ? this.#context.getString(described.value) : "";
                described.value.dispose();
                const parsed: unknown = text === "" ? undefined : JSON.parse(text);
                if (Array.isArray(parsed) && typeof parsed[0] === "string" && typeof parsed[1] === "string") [message, stack] = parsed as [string, string];
            }
        } catch (error) {
            if (error instanceof WasmRuntimeError) return this.#abort(error) as RunResult & { readonly ok: false };
        } finally {
            if (handle.alive) handle.dispose();
        }
        const frame = /sandbox\.js:(\d+):(\d+)/.exec(stack);
        const at = frame === null ? undefined : { line: Number(frame[1]), column: Number(frame[2]) };
        return { ok: false, error: message, timedOut, ...(at === undefined ? {} : { at }) };
    }

    #hostFailure(error: unknown): RunResult {
        if (error instanceof WasmRuntimeError) return this.#abort(error);
        return { ok: false, error: `sandbox host error: ${safeMessage(error)}`, timedOut: false };
    }

    /** Free the sandbox. Never throws: a runtime QuickJS can't free cleanly only costs the WASM instance. */
    dispose(): void {
        if (this.#broken !== undefined) return;
        try {
            for (const { fn, owner } of this.#functions.values()) {
                fn.dispose();
                if (owner !== this.#context.global && owner.alive) owner.dispose();
            }
            this.#functions.clear();
            for (const handle of this.#held.values()) if (handle.alive) handle.dispose();
            this.#held.clear();
            this.#decode.dispose();
            this.#encode.dispose();
            this.#describe.dispose();
            this.#context.dispose();
            this.#runtime.dispose();
        } catch (error) {
            this.#abort(error);
        }
    }
}
