import * as variantModule from "@jitl/quickjs-wasmfile-release-sync";
import { newQuickJSWASMModuleFromVariant, newVariant } from "quickjs-emscripten-core";
import type { CustomizeVariantOptions, QuickJSContext, QuickJSHandle, QuickJSRuntime, QuickJSSyncVariant, QuickJSWASMModule } from "quickjs-emscripten-core";

/**
 * QuickJS (WASM) sandbox for the obfuscator's own runtime helpers. Guest gets standard builtins only, nothing from the
 * host; plain values are copied out. Deadline plus memory/stack limits bound hostile code; `Math.random` is seeded.
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

const DETERMINISM = `(() => {
    let a = 0x9e3779b9 | 0;
    Math.random = function random() {
        a = (a + 0x6d2b79f5) | 0;
        let t = Math.imul(a ^ (a >>> 15), 1 | a);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
})();`;

/** JSON with `undefined`/`NaN`/`±Infinity`/`-0` tagged. Must stay in step with the guest side in `TRANSPORT`. */
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
    readonly #quote: QuickJSHandle;
    readonly #decode: QuickJSHandle;
    readonly #encode: QuickJSHandle;
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
        this.#quote = this.#context.unwrapResult(this.#context.evalCode("(function (v) { return JSON.stringify(v); })"));
        const transport = this.#context.unwrapResult(this.#context.evalCode(TRANSPORT));
        this.#decode = this.#context.getProp(transport, 0);
        this.#encode = this.#context.getProp(transport, 1);
        transport.dispose();
    }

    /** Strings go through guest `JSON.stringify`: copied directly they cross as C strings and truncate at NUL. */
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

    get broken(): string | undefined {
        return this.#broken;
    }

    /** An abort kills the WASM instance it happened in; drop it so the next sandbox loads a fresh one. */
    #abort(error: unknown): RunResult {
        this.#broken = error instanceof Error ? error.message : String(error);
        modulePromise = undefined;
        return { ok: false, error: `sandbox aborted: ${this.#broken}`, timedOut: false };
    }

    #arm(timeoutMs: number): void {
        this.#deadline = Date.now() + timeoutMs;
        this.#interrupted = false;
    }

    /** Only a WASM abort breaks the sandbox; a host-side copy failure (e.g. cyclic value) is an ordinary error. */
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

    /** Keep an expression's value host-side only, so helpers can't collide with or show up among program globals. */
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

    #failure(handle: QuickJSHandle, dispose = false): RunResult {
        try {
            const thrown: unknown = this.#copy(handle);
            const message = typeof thrown === "object" && thrown !== null && "message" in thrown ? String(thrown.message) : String(thrown);
            const stack = typeof thrown === "object" && thrown !== null && "stack" in thrown ? String(thrown.stack) : "";
            const frame = /sandbox\.js:(\d+):(\d+)/.exec(stack);
            const at = frame === null ? undefined : { line: Number(frame[1]), column: Number(frame[2]) };
            return { ok: false, error: message, timedOut: this.#interrupted, ...(at === undefined ? {} : { at }) };
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
