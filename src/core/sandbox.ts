import * as variantModule from "@jitl/quickjs-wasmfile-release-sync";
import { newQuickJSWASMModuleFromVariant, newVariant } from "quickjs-emscripten-core";
import type { CustomizeVariantOptions, QuickJSContext, QuickJSHandle, QuickJSRuntime, QuickJSSyncVariant, QuickJSWASMModule } from "quickjs-emscripten-core";

/**
 * A QuickJS (WASM) sandbox for running small pieces of the obfuscator's own runtime: the prelude helpers and calls
 * to them with constant arguments.
 *
 * Isolation: the guest gets QuickJS's standard builtins only. Nothing from the host is exposed (no fs, network,
 * process, require, console), and only plain values are copied out. Every run has a wall-clock deadline and the
 * runtime has a memory and stack limit, so hostile code can at worst fail its own run.
 *
 * Determinism: `Math.random` is replaced with a seeded generator, so runs are repeatable.
 */

export interface SandboxLimits {
    readonly memoryBytes: number;
    readonly stackBytes: number;
    /** Default deadline for one `run`. */
    readonly timeoutMs: number;
}

export const DEFAULT_LIMITS: SandboxLimits = { memoryBytes: 256 * 1024 * 1024, stackBytes: 1024 * 1024, timeoutMs: 2000 };

export type RunResult = { readonly ok: true; readonly value: unknown } | { readonly ok: false; readonly error: string; readonly timedOut: boolean };

/** A guest object only the host holds (see `Sandbox.hold`): no name in the guest reaches it. */
export interface Held {
    readonly id: number;
}

let modulePromise: Promise<QuickJSWASMModule> | undefined;
/** The variant package's typings describe its CommonJS shape (default nested once more); at runtime this is the variant. */
const baseVariant = variantModule.default as unknown as QuickJSSyncVariant;
/**
 * Emscripten prints aborts (`Aborted(Assertion failed ...)`) to the host's stderr before throwing; the library never
 * writes to the console, and the abort still reaches `run`/`dispose` as an exception. `print`/`printErr` are standard
 * Emscripten module options the loader passes through, missing from its typings.
 */
const silent = { print: () => {}, printErr: () => {} } as unknown as NonNullable<CustomizeVariantOptions["emscriptenModule"]>;
const syncVariant = newVariant(baseVariant, { emscriptenModule: silent });
const quickjs = (): Promise<QuickJSWASMModule> => (modulePromise ??= newQuickJSWASMModuleFromVariant(syncVariant));

/** Seeded mulberry32, installed as Math.random inside the guest. */
const DETERMINISM = `(() => {
    let a = 0x9e3779b9 | 0;
    Math.random = function random() {
        a = (a + 0x6d2b79f5) | 0;
        let t = Math.imul(a ^ (a >>> 15), 1 | a);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
})();`;

/**
 * Values cross between host and guest as JSON, with the values JSON can't carry tagged: `undefined`, `NaN`,
 * `Infinity`, `-Infinity` and `-0`. The guest side of this lives in `TRANSPORT` and must stay in step.
 */
const TAG = "$jsd";
const SPECIAL: Record<string, unknown> = { undefined: undefined, NaN: Number.NaN, Infinity: Number.POSITIVE_INFINITY, "-Infinity": Number.NEGATIVE_INFINITY, "-0": -0 };
const tagOf = (value: unknown): string | undefined => {
    if (value === undefined) return "undefined";
    if (typeof value !== "number") return undefined;
    if (Number.isNaN(value)) return "NaN";
    if (value === Number.POSITIVE_INFINITY) return "Infinity";
    if (value === Number.NEGATIVE_INFINITY) return "-Infinity";
    return Object.is(value, -0) ? "-0" : undefined;
};
const encode = (value: unknown): string =>
    JSON.stringify(value, function (this: Record<string, unknown>, key: string, raw: unknown) {
        // `raw` has been through JSON's own conversion (-0 is already 0); the holder still has the original.
        const tag = tagOf(this[key]);
        return tag === undefined ? raw : { [TAG]: tag };
    }) ?? JSON.stringify({ [TAG]: "undefined" });
const decode = (text: string): unknown =>
    JSON.parse(text, (_key, raw: unknown) => (typeof raw === "object" && raw !== null && TAG in raw ? SPECIAL[String((raw as Record<string, unknown>)[TAG])] : raw));

/** Guest half of the transport: `[decode, encode]`. */
const TRANSPORT = `(function () {
    var TAG = ${JSON.stringify(TAG)};
    var SPECIAL = { "undefined": undefined, "NaN": NaN, "Infinity": Infinity, "-Infinity": -Infinity, "-0": -0 };
    function tagOf(v) {
        if (v === undefined) return "undefined";
        if (typeof v !== "number") return undefined;
        if (v !== v) return "NaN";
        if (v === Infinity) return "Infinity";
        if (v === -Infinity) return "-Infinity";
        return v === 0 && 1 / v < 0 ? "-0" : undefined;
    }
    return [
        function (text) {
            return JSON.parse(text, function (k, v) { return v !== null && typeof v === "object" && TAG in v ? SPECIAL[v[TAG]] : v; });
        },
        function (value) {
            var text = JSON.stringify(value, function (k, v) {
                var tag = tagOf(this[k]);
                if (tag === undefined) return v;
                var out = {};
                out[TAG] = tag;
                return out;
            });
            return text === undefined ? '{"' + TAG + '":"undefined"}' : text;
        }
    ];
})()`;

export class Sandbox {
    readonly #runtime: QuickJSRuntime;
    readonly #context: QuickJSContext;
    readonly #limits: SandboxLimits;
    /** Guest `JSON.stringify`, for copying strings out (see `#copy`). */
    readonly #quote: QuickJSHandle;
    /** Guest transport functions: tagged JSON text to value, value to tagged JSON text. */
    readonly #decode: QuickJSHandle;
    readonly #encode: QuickJSHandle;
    /** Guest functions `invoke` has looked up, by base and path. */
    readonly #functions = new Map<string, { fn: QuickJSHandle; owner: QuickJSHandle }>();
    /** Objects `hold` keeps, by id. */
    readonly #held = new Map<number, QuickJSHandle>();
    #deadline = 0;
    /** The interrupt handler stopped the current run (its deadline passed). */
    #interrupted = false;
    /** Set once the WASM instance aborted; every later call fails fast. */
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
        this.#quote = this.#context.unwrapResult(this.#context.evalCode("(function (v) { return JSON.stringify(v); })"));
        const transport = this.#context.unwrapResult(this.#context.evalCode(TRANSPORT));
        this.#decode = this.#context.getProp(transport, 0);
        this.#encode = this.#context.getProp(transport, 1);
        transport.dispose();
    }

    /**
     * Copy a guest value to the host. Strings go through the guest's `JSON.stringify`: copied directly they cross as C
     * strings and lose everything from the first NUL on (a decoded `"a\0b"` would arrive as `"a"`).
     */
    #copy(handle: QuickJSHandle): unknown {
        if (this.#context.typeof(handle) !== "string") return this.#context.dump(handle);
        const quoted = this.#context.unwrapResult(this.#context.callFunction(this.#quote, this.#context.undefined, handle));
        try {
            return JSON.parse(this.#context.getString(quoted)) as unknown;
        } finally {
            quoted.dispose();
        }
    }

    static async create(limits: SandboxLimits = DEFAULT_LIMITS): Promise<Sandbox> {
        const sandbox = new Sandbox(await quickjs(), limits);
        const setup = sandbox.run(DETERMINISM);
        if (!setup.ok) throw new Error(`sandbox setup failed: ${setup.error}`);
        return sandbox;
    }

    /** Why the sandbox stopped working, if it did. */
    get broken(): string | undefined {
        return this.#broken;
    }

    /** An abort kills the WASM instance it happened in; drop it so the next sandbox loads a fresh one. */
    #abort(error: unknown): RunResult {
        this.#broken = error instanceof Error ? error.message : String(error);
        modulePromise = undefined;
        return { ok: false, error: `sandbox aborted: ${this.#broken}`, timedOut: false };
    }

    /** Start a run's clock: the interrupt handler stops it `timeoutMs` from now. */
    #arm(timeoutMs: number): void {
        this.#deadline = Date.now() + timeoutMs;
        this.#interrupted = false;
    }

    /**
     * Evaluate `code` as a script in the guest's global scope and copy its completion value out. Only a WASM abort
     * breaks the sandbox; a host-side failure copying the value (e.g. a cyclic structure) is an ordinary error.
     */
    run(code: string, timeoutMs = this.#limits.timeoutMs): RunResult {
        return this.#evaluate(code, timeoutMs, true);
    }

    /** Evaluate `code` as a script in the guest's global scope for its effects: nothing but a thrown error is copied out. */
    execute(code: string, timeoutMs = this.#limits.timeoutMs): RunResult {
        return this.#evaluate(code, timeoutMs, false);
    }

    #evaluate(code: string, timeoutMs: number, copy: boolean): RunResult {
        if (this.#broken !== undefined) return { ok: false, error: `sandbox aborted earlier: ${this.#broken}`, timedOut: false };
        try {
            this.#arm(timeoutMs);
            const result = this.#context.evalCode(code, "sandbox.js", { type: "global" });
            const handle = result.error ?? result.value;
            try {
                if (result.error === undefined) return { ok: true, value: copy ? this.#copy(handle) : undefined };
                return this.#failure(handle);
            } finally {
                handle.dispose();
            }
        } catch (error) {
            return this.#hostFailure(error);
        }
    }

    /**
     * Evaluate `code`, an expression, and keep its value on the host side only: guest code finds it under no name, so
     * helper objects installed this way can't collide with the program's names or show up among the globals.
     */
    hold(code: string, timeoutMs = this.#limits.timeoutMs): { readonly ok: true; readonly held: Held } | (RunResult & { readonly ok: false }) {
        if (this.#broken !== undefined) return { ok: false, error: `sandbox aborted earlier: ${this.#broken}`, timedOut: false };
        try {
            this.#arm(timeoutMs);
            const result = this.#context.evalCode(code, "sandbox.js", { type: "global" });
            if (result.error !== undefined) return this.#failure(result.error, true) as RunResult & { readonly ok: false };
            const held = { id: this.#held.size + 1 };
            this.#held.set(held.id, result.value);
            return { ok: true, held };
        } catch (error) {
            return this.#hostFailure(error) as RunResult & { readonly ok: false };
        }
    }

    /**
     * Call a guest function, found by property path from `base` (a held object) or else the global object, with
     * `payload` as its one argument. Nothing is compiled: the payload and the result cross as data (tagged JSON, so
     * `undefined`, `NaN`, `-0` and NULs in strings survive). Guest functions are looked up once and kept.
     */
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
            if (argument.error) return this.#failure(argument.error, true);
            const result = context.callFunction(target.fn, target.owner, argument.value);
            argument.value.dispose();
            if (result.error) return this.#failure(result.error, true);
            const encoded = context.callFunction(this.#encode, context.undefined, result.value);
            result.value.dispose();
            if (encoded.error) return this.#failure(encoded.error, true);
            const json = context.getString(encoded.value);
            encoded.value.dispose();
            return { ok: true, value: decode(json) };
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
        /** Handles this lookup made (the start isn't one: the global object or a held object stays). */
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

    /** A guest exception as a failed result (disposing the handle when asked). */
    #failure(handle: QuickJSHandle, dispose = false): RunResult {
        try {
            const thrown: unknown = this.#copy(handle);
            const message = typeof thrown === "object" && thrown !== null && "message" in thrown ? String(thrown.message) : String(thrown);
            return { ok: false, error: message, timedOut: this.#interrupted };
        } finally {
            if (dispose) handle.dispose();
        }
    }

    #hostFailure(error: unknown): RunResult {
        // Emscripten aborts throw `WebAssembly.RuntimeError` (not declared in the project's type libs).
        if (error instanceof Error && error.name === "RuntimeError") return this.#abort(error);
        return { ok: false, error: `couldn't copy the result out: ${error instanceof Error ? error.message : String(error)}`, timedOut: false };
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
            this.#quote.dispose();
            this.#decode.dispose();
            this.#encode.dispose();
            this.#context.dispose();
            this.#runtime.dispose();
        } catch (error) {
            this.#abort(error);
        }
    }
}
