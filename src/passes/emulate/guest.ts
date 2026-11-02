import type { Value } from "../../core/evaluate.js";
import type { Held, RunResult } from "../../core/sandbox.js";
import { DEFAULT_SEED, Sandbox } from "../../core/sandbox.js";
import { guestRuntime, HOST_MODEL } from "./guest-runtime.js";

/**
 * The runtime in the QuickJS sandbox. Guest side: a helper object held by the host only (no guest name reaches it);
 * host side: `Guest`, one method per helper, each a `Sandbox.invoke` with plain data. The only code the sandbox
 * compiles is the program's own statements (`run`).
 *
 * The program is an adversary: the helpers use builtins captured before it ran, never what it added or replaced, and
 * every answer is checked on the host; a malformed one counts as none.
 *
 * Environment reads: the guest is no browser (no `document`, its own time), so what a run computes from them a real
 * run may not (model 10). The guest notes the first such read since the last question: a web-platform global it lacks
 * (`WEB_GLOBALS`; also through `typeof`, `in` or the global object), `Date`, an error's stack, locale methods, and the
 * source text of functions it made itself (recorders, stand-ins). Helpers that run program code report it; answers
 * from such runs are not used. Math.random is no environment read but a second seed's check (`Guest`). Not seen: the
 * `stack` and `message` of errors the engine itself throws (own data properties QuickJS makes; only constructed
 * errors are covered).
 *
 * Paths are from the global object for builtins (`[]` is the global object), from the storage object for the runtime.
 * Keys are property keys as JS sees them (`G[593908]` has key `"593908"`).
 */

export type PropertyPath = readonly string[];

/**
 * `"static"`: `G.alias(a)` is `Owner.original(a)`; `"method"`: `G.alias(x, a)` is `x.original(a)`; `"call"`:
 * `G.alias(x, a)` is `Owner.original.call(x, a)`.
 */
export type CallStyle = "static" | "method" | "call";

/** A value the guest didn't copy: objects, functions, symbols and bigints by type only. */
export interface NonPrimitive {
    readonly nonPrimitive: string;
}

/**
 * With a `record` target, also guest identities (`idOf`) of the target's owner before the call and of the target before
 * and after (`null`: primitive or behind an accessor); a change is a write the call made to the target (e.g. a decoder
 * freezing).
 */
export interface LoggedCall {
    readonly key: string;
    readonly args: readonly (Value | NonPrimitive)[];
    readonly result: Value | NonPrimitive;
    readonly owner: number | null;
    readonly before: number | null;
    readonly after: number | null;
    /** For a number result: whether `Array.prototype`/`Object.prototype` had an index property right after the call. */
    readonly indexed?: boolean;
}

/**
 * The calls a statement's run made (the main lane's), the first environment read since the last take (see the module
 * comment), and whether the second lane, when it follows, saw otherwise (`disagreed`: what the run did is unknown).
 */
export interface RunRecord {
    readonly calls: readonly LoggedCall[];
    readonly env: string | undefined;
    readonly disagreed: boolean;
    /** Under the second lane it called, built or wrote a host global (a stub): an effect no lane sees. */
    readonly hostEffect: boolean;
}

/** Methods: functions in own data properties, by name. */
export interface BuiltIdentities {
    readonly holder: number;
    readonly methods: ReadonlyMap<string, number>;
}

/** `storage.path(...args)`, then optionally `[lookup[0]][lookup[1]]...` on the result. */
export interface ResolveRequest {
    readonly path: PropertyPath;
    readonly args: readonly Value[];
    readonly lookup?: PropertyPath;
}

export type ResolveResult =
    | { readonly ok: true; readonly value: Value; readonly repeatable: boolean }
    | { readonly ok: true; readonly nonPrimitive: "object" | "function" }
    /** `stale`: an earlier call in the batch changed the runtime's state; `env`: the call read the environment. */
    /** `seen`: with `env`, what the guest answered (never a value to use, at most a reason to refuse). */
    | { readonly ok: false; readonly error: string; readonly stale?: true; readonly env?: true; readonly seen?: Value };

/**
 * Since the baseline; entries are `[owner index, name, value]`, values as identities (`#3`) or typed primitives. Only
 * changes are copied out; `namesBefore` lists prior names of owners that gained a property.
 */
export interface OwnersChange {
    readonly same: boolean;
    readonly accessorsBefore: number;
    readonly accessorsAfter: number;
    /** Gone or changed. */
    readonly changed: readonly (readonly [number, string, string])[];
    /** New or changed. */
    readonly added: readonly (readonly [number, string, string])[];
    readonly namesBefore: Readonly<Record<string, readonly string[]>>;
}

/** What `aliasOf` found: the existing name the alias reads like, or the environment read that voids the answer. */
export type AliasAnswer = { readonly original: string } | { readonly env: string };

export type CallAliasAnswer = { readonly key: string; readonly owner: PropertyPath; readonly original: string; readonly style: CallStyle | undefined } | { readonly key: string; readonly env: string };

export const pathName = (path: PropertyPath): string => (path.length === 0 ? "globalThis" : path.join("."));

/** Where a function the program's source made starts: the run's file name, QuickJS's 1-based line and column (code points). */
export interface FunctionSite {
    readonly file: string;
    readonly line: number;
    readonly column: number;
}

/** A guest function's identity (`idOf`), and its site when program source made it. */
export interface FunctionRecord {
    readonly id: number;
    readonly site: FunctionSite | undefined;
}

export interface AccessorFunctions {
    readonly get: FunctionRecord | undefined;
    readonly set: FunctionRecord | undefined;
}

/** What `Guest.installed` tells after a statement: accessors by place (`path` `null`: the storage object), owners' names. */
export interface InstalledState {
    readonly accessors: readonly { readonly path: PropertyPath | null; readonly key: string; readonly accessor: AccessorFunctions | null }[];
    /** Each owner's own names, by owner index. */
    readonly names: readonly (readonly string[])[];
    /** Which of them are accessors. */
    readonly accessorNames: readonly (readonly string[])[];
}
/**
 * A property lookup on a builtin (`Guest.lookup`): `base` when the path doesn't reach an object by data properties;
 * otherwise where along the prototype chain it is found (`holder`: an owner index, -1 for another object). `owner` is
 * the value's owner index (-1: not an owner); `value` the primitive (`null` for objects, symbols and bigints).
 */
export type Lookup =
    | { readonly kind: "base" }
    | { readonly kind: "absent" }
    | { readonly kind: "accessor"; readonly holder: number }
    | { readonly kind: "data"; readonly holder: number; readonly owner: number; readonly type: string; readonly value: Value };

/** A timeout costs at most one chunk. */
const RESOLVE_CHUNK = 2000;
const RESOLVE_CHUNK_TIMEOUT_MS = 30_000;

// Shapes of the helpers' answers: the guest is the program's, so each is checked before use.
type Check<T> = (value: unknown) => value is T;
const isRecord = (value: unknown): value is Record<string, unknown> => typeof value === "object" && value !== null && !Array.isArray(value);
const isString = (value: unknown): value is string => typeof value === "string";
const isIndex = (value: unknown): value is number => typeof value === "number" && Number.isInteger(value) && value >= 0;
const isIdentity = (value: unknown): value is number | null => value === null || isIndex(value);
const isValue = (value: unknown): value is Value => value === null || value === undefined || typeof value === "string" || typeof value === "number" || typeof value === "boolean";
const isCarried = (value: unknown): value is Value | NonPrimitive => isValue(value) || (isRecord(value) && isString(value.nonPrimitive));
const arrayOf =
    <T>(check: Check<T>): Check<T[]> =>
    (value: unknown): value is T[] =>
        Array.isArray(value) && value.every((item) => check(item));
const isPath = arrayOf(isString);
const isEntry = (value: unknown): value is [number, string, string] => Array.isArray(value) && value.length === 3 && isIndex(value[0]) && isString(value[1]) && isString(value[2]);
const isLoggedCall = (value: unknown): value is LoggedCall =>
    isRecord(value) &&
    isString(value.key) &&
    arrayOf(isCarried)(value.args) &&
    isCarried(value.result) &&
    isIdentity(value.owner) &&
    isIdentity(value.before) &&
    isIdentity(value.after) &&
    (value.indexed === undefined || typeof value.indexed === "boolean");
const isOwnersChange = (value: unknown): value is OwnersChange =>
    isRecord(value) &&
    typeof value.same === "boolean" &&
    isIndex(value.accessorsBefore) &&
    isIndex(value.accessorsAfter) &&
    arrayOf(isEntry)(value.changed) &&
    arrayOf(isEntry)(value.added) &&
    isRecord(value.namesBefore) &&
    Object.entries(value.namesBefore).every(([index, names]) => /^\d+$/.test(index) && isPath(names));
const isResolveResult = (value: unknown): value is ResolveResult =>
    isRecord(value) &&
    (value.ok === true
        ? "nonPrimitive" in value
            ? value.nonPrimitive === "object" || value.nonPrimitive === "function"
            : "value" in value && isValue(value.value) && typeof value.repeatable === "boolean"
        : value.ok === false &&
          isString(value.error) &&
          (value.stale === undefined || value.stale === true) &&
          (value.env === undefined || value.env === true) &&
          (value.seen === undefined || isValue(value.seen)));
const isComparison = (value: unknown): value is { ok: true; value: boolean } | { ok: false; reason: string } =>
    isRecord(value) && (value.ok === true ? typeof value.value === "boolean" : value.ok === false && isString(value.reason));

const answer = <T>(result: RunResult, check: Check<T>): T | undefined => (result.ok && check(result.value) ? result.value : undefined);
const isTaken = (v: unknown): v is { calls: LoggedCall[]; env: string | null; disagreed?: true } =>
    isRecord(v) && arrayOf(isLoggedCall)(v.calls) && (v.env === null || isString(v.env)) && (v.disagreed === undefined || v.disagreed === true);
const isPair = (v: unknown): v is [string, number] => Array.isArray(v) && v.length === 2 && isString(v[0]) && isIndex(v[1]);
type Found = { key: string; owner: number; original: string; style: CallStyle | null } | { key: string; env: string };
const isFound = (v: unknown): v is Found =>
    isRecord(v) && isString(v.key) && (isString(v.env) || (isIndex(v.owner) && isString(v.original) && (v.style === null || v.style === "static" || v.style === "method" || v.style === "call")));
const isOwnerIndex = (value: unknown): value is number => typeof value === "number" && Number.isInteger(value) && value >= -1;
const isSite = (value: unknown): value is { file: string; line: number; column: number } => isRecord(value) && isString(value.file) && isIndex(value.line) && isIndex(value.column);
const isFunctionRecord = (value: unknown): value is { id: number; site: { file: string; line: number; column: number } | null } =>
    isRecord(value) && isIndex(value.id) && (value.site === null || isSite(value.site));
const isAccessorPair = (value: unknown): value is { get: unknown; set: unknown } | null =>
    value === null || (isRecord(value) && (value.get === null || isFunctionRecord(value.get)) && (value.set === null || isFunctionRecord(value.set)));
const isLookup = (value: unknown): value is Lookup =>
    isRecord(value) &&
    (value.kind === "base" ||
        value.kind === "absent" ||
        (value.kind === "accessor" && isOwnerIndex(value.holder)) ||
        (value.kind === "data" && isOwnerIndex(value.holder) && isOwnerIndex(value.owner) && isString(value.type) && isValue(value.value)));
const functionRecord = (value: unknown): FunctionRecord | undefined => (isFunctionRecord(value) ? { id: value.id, site: value.site === null ? undefined : value.site } : undefined);

/** One QuickJS guest: its sandbox and the helper object only the host holds (no program name reaches it). */
interface Lane {
    readonly sandbox: Sandbox;
    readonly api: Held;
}

type Operation =
    | { readonly kind: "run"; readonly source: string; readonly timeoutMs: number; readonly file: string }
    | { readonly kind: "invoke"; readonly helper: string; readonly payload: unknown; readonly timeoutMs: number | undefined };

/** How two lanes' answers to one helper combine: the main lane's where they agree. */
type Merge = (main: unknown, second: unknown) => unknown;

const SECOND_SEED = 0x2545f491;
const DISAGREE = "the guest answers differently under another Math.random seed";

/** Primitives by `Object.is`, arrays and plain objects by their own keys. */
const sameAnswer = (a: unknown, b: unknown): boolean => {
    if (typeof a !== "object" || a === null || typeof b !== "object" || b === null) return Object.is(a, b);
    if (Array.isArray(a) !== Array.isArray(b)) return false;
    const keys = Object.keys(a);
    const record = a as Record<string, unknown>;
    const other = b as Record<string, unknown>;
    return keys.length === Object.keys(b).length && keys.every((key) => Object.hasOwn(other, key) && sameAnswer(record[key], other[key]));
};

/** Lists answered item by item (`resolve`, `compare`): an item the lanes disagree on fails alone. */
const itemwise =
    (failure: unknown): Merge =>
    (main, second) =>
        Array.isArray(main) && Array.isArray(second) && main.length === second.length ? main.map((item: unknown, i) => (sameAnswer(item, second[i]) ? item : failure)) : undefined;

/** The loaded QuickJS module lanes are made in. */
type Module = Awaited<ReturnType<typeof Sandbox.load>>;

const install = (module: Module, seed: number, stubbed: boolean): Lane => {
    const sandbox = Sandbox.fromModule(module, undefined, seed);
    const host = sandbox.run(HOST_MODEL);
    const installed = host.ok ? sandbox.hold(guestRuntime(stubbed), undefined, "runtime.js") : host;
    if (installed.ok && "held" in installed) return { sandbox, api: installed.held };
    sandbox.dispose();
    throw new Error(`guest runtime install failed: ${installed.ok ? "no helper object" : installed.error}`);
};

/**
 * Two sources a real run answers otherwise without any being wrong: Math.random (the guest's sequence is one a real
 * run may draw, not the one it draws) and the host's globals (`WEB_GLOBALS`, absent in the guest). So from the first
 * answer after a run or helper that called Math.random or read such a global, a second lane (another seed, and every
 * such global present as a stub that answers any use with itself) replays every operation so far and then follows
 * the main one; answers are kept only where both lanes agree (objects by identity: equal operation sequences give
 * equal ids). Agreement is evidence, not proof (user decision 2026-11-02).
 */
export class Guest {
    readonly #main: Lane;
    /** For the second lane, installed only when first needed (most programs never need it). */
    readonly #module: Module;
    #second: Lane | undefined;
    /** Every operation on the main lane, with its result, until the second lane follows. */
    readonly #journal: { readonly op: Operation; readonly result: RunResult }[] = [];
    /** Why the second lane's replay didn't go as the main lane went (then it witnesses nothing). */
    #replayFailed: string | undefined;
    /** Every builtin object a name reached before the program ran; indexes are owner ids. */
    readonly owners: readonly PropertyPath[];
    /** Set when a batch of calls stopped partway. */
    #tainted: string | undefined;
    /** The second lane reported a host effect since the last `takeRun`. */
    #hostEffect = false;
    /**
     * Where the guest-side owner baseline stands: `"current"`, the owners' state now; `"spans"`, taken right before the
     * last `run` (what `ownersSince` measures); otherwise none `ownersSince` may use.
     */
    #baseline: "current" | "spans" | undefined;

    private constructor(main: Lane, module: Module, owners: readonly PropertyPath[]) {
        this.#main = main;
        this.#module = module;
        this.owners = owners;
    }

    static async create(): Promise<Guest> {
        const module = await Sandbox.load();
        const main = install(module, DEFAULT_SEED, false);
        const owners = answer(Guest.#call(main, { kind: "invoke", helper: "owners", payload: null, timeoutMs: undefined }).result, arrayOf(isPath));
        if (owners === undefined) {
            main.sandbox.dispose();
            throw new Error("guest runtime install failed: no owners");
        }
        return new Guest(main, module, owners);
    }

    get broken(): string | undefined {
        return this.#main.sandbox.broken ?? this.#second?.sandbox.broken ?? this.#tainted;
    }

    static #call(lane: Lane, op: Operation): { result: RunResult; check: boolean; effect: boolean } {
        if (op.kind === "run") return { result: lane.sandbox.execute(op.source, op.timeoutMs, op.file), check: false, effect: false };
        const raw = lane.sandbox.invoke([op.helper], op.payload, op.timeoutMs, lane.api);
        if (!raw.ok) return { result: raw, check: false, effect: false };
        const envelope = raw.value;
        if (!isRecord(envelope) || typeof envelope.check !== "boolean" || typeof envelope.effect !== "boolean" || !("value" in envelope))
            return { result: { ok: false, error: "malformed answer", timedOut: false }, check: false, effect: false };
        return { result: { ok: true, value: envelope.value }, check: envelope.check, effect: envelope.effect };
    }

    /** The main lane's answer, and whether the second lane (when it follows) answered alike. */
    #perform(op: Operation): { result: RunResult; second: RunResult | undefined } {
        const main = Guest.#call(this.#main, op);
        let second = this.#second;
        if (second === undefined) {
            if (!main.check) {
                this.#journal.push({ op, result: main.result });
                return { result: main.result, second: undefined };
            }
            try {
                second = install(this.#module, SECOND_SEED, true);
            } catch (error) {
                return { result: main.result, second: { ok: false, error: `no second lane: ${error instanceof Error ? error.message : String(error)}`, timedOut: false } };
            }
            // The replay must go as the main lane went, but for the statement whose environment read started the lane
            // (its run is followed by the `takeRun` that reports the read; their answers are compared there).
            // Otherwise the second lane witnesses nothing from here on.
            const trigger = op.kind === "invoke" && op.helper === "takeRun" ? this.#journal.findLastIndex((earlier) => earlier.op.kind === "run") : -1;
            for (const [index, earlier] of this.#journal.entries()) {
                if (this.#replayFailed !== undefined) break;
                const replayed = Guest.#call(second, earlier.op).result;
                if (index >= trigger && trigger !== -1) continue;
                const same = replayed.ok === earlier.result.ok && (!replayed.ok || !earlier.result.ok || earlier.op.kind === "run" || sameAnswer(replayed.value, earlier.result.value));
                if (!same) this.#replayFailed = `its replay of an earlier ${earlier.op.kind === "run" ? "statement" : earlier.op.helper} went otherwise`;
            }
            this.#journal.length = 0;
            this.#second = second;
        }
        if (this.#replayFailed !== undefined) return { result: main.result, second: { ok: false, error: `the second lane is no witness: ${this.#replayFailed}`, timedOut: false } };
        const other = Guest.#call(second, op);
        if (other.effect) this.#hostEffect = true;
        return { result: main.result, second: other.result };
    }

    /** Kept where both lanes agree; `merge` combines answers that differ (the main lane's otherwise fails). */
    #invoke(helper: string, payload: unknown, timeoutMs?: number, merge?: Merge): RunResult {
        const { result, second } = this.#perform({ kind: "invoke", helper, payload, timeoutMs });
        if (!result.ok || second === undefined || (second.ok && sameAnswer(result.value, second.value))) return result;
        const merged = merge?.(result.value, second.ok ? second.value : undefined);
        return merged === undefined ? { ok: false, error: second.ok ? DISAGREE : `${DISAGREE} (there: ${second.error})`, timedOut: false } : { ok: true, value: merged };
    }

    /**
     * In the guest's global scope, for its effects (nothing is copied out). `disagreed`: it ran to completion here but
     * not under the second lane, so what it did is unknown. `file` names the functions it makes (`functionSite`).
     */
    run(source: string, timeoutMs: number, file = "sandbox.js"): RunResult & { readonly disagreed?: true } {
        this.#baseline = this.#baseline === "current" ? "spans" : undefined;
        const { result, second } = this.#perform({ kind: "run", source, timeoutMs, file });
        return result.ok && second !== undefined && !second.ok ? { ...result, disagreed: true } : result;
    }

    globals(): string[] {
        return answer(this.#invoke("globals", null), isPath) ?? [];
    }

    /** Call after the root functions are declared. */
    bind(storage: string): boolean {
        return answer(this.#invoke("bind", storage), (value): value is true => value === true) ?? false;
    }

    snapshot(): (readonly string[])[] {
        return answer(this.#invoke("snapshot", this.owners), arrayOf(isPath)) ?? [];
    }

    /** Makes the owners' current state the baseline, unless it already is. */
    markOwners(): void {
        if (this.#baseline !== "current") this.#baseline = answer(this.#invoke("markOwners", this.owners), (value): value is true => value === true) === true ? "current" : undefined;
    }

    /**
     * What the last `run` changed in the owners, when `markOwners` came right before it (`undefined` otherwise, or with
     * no answer). The baseline then becomes the current state.
     */
    ownersSince(): OwnersChange | undefined {
        if (this.#baseline !== "spans") return undefined;
        const change = answer(this.#invoke("ownersSince", this.owners), isOwnersChange);
        this.#baseline = change === undefined ? undefined : "current";
        return change;
    }

    /** Observed in the guest: the only lookup that reached the global object's prototype chain. */
    globalReads(timeoutMs?: number): { key: string; name: string }[] {
        return (
            answer(
                this.#invoke("globalReads", null, timeoutMs),
                arrayOf((v): v is { key: string; name: string } => isRecord(v) && isString(v.key) && isString(v.name))
            ) ?? []
        );
    }

    /** Accessors whose getter hands out that property absent or present, and whose setter writes it. */
    hostAliases(names: readonly string[], timeoutMs?: number): { alias: string; name: string }[] {
        return (
            answer(
                this.#invoke("hostAliases", names, timeoutMs),
                arrayOf((v): v is { alias: string; name: string } => isRecord(v) && isString(v.alias) && isString(v.name))
            ) ?? []
        );
    }

    /** Replace `storage[key]` with a recorder (`takeRun`), tracking identities of `target` and its owner per call. */
    record(key: string, target?: PropertyPath): boolean {
        return answer(this.#invoke("record", { key, target: target ?? null }), (value): value is true => value === true) ?? false;
    }

    /** The calls and environment reads since the last take; `undefined` when the guest didn't answer (state unknown). */
    takeRun(): RunRecord | undefined {
        const taken = answer(
            this.#invoke("takeRun", null, undefined, (main) => (isRecord(main) ? { ...main, disagreed: true } : undefined)),
            isTaken
        );
        const hostEffect = this.#hostEffect;
        this.#hostEffect = false;
        return taken === undefined ? undefined : { calls: taken.calls, env: taken.env ?? undefined, disagreed: taken.disagreed === true, hostEffect };
    }

    /** `undefined`: not an object reached through data properties. */
    built(path: PropertyPath): BuiltIdentities | undefined {
        const found = answer(this.#invoke("built", path), (v): v is { holder: number; methods: [string, number][] } => isRecord(v) && isIndex(v.holder) && arrayOf(isPair)(v.methods));
        return found === undefined ? undefined : { holder: found.holder, methods: new Map(found.methods) };
    }

    /** `undefined`: no existing name reads the same (or no answer). Reading may run getters. */
    aliasOf(owner: PropertyPath, alias: string, candidates: readonly string[], timeoutMs?: number): AliasAnswer | undefined {
        return answer(
            this.#invoke("aliasOf", { owner, alias, candidates }, timeoutMs),
            (v): v is AliasAnswer => isRecord(v) && (isString(v.original) ? candidates.includes(v.original) : isString(v.env))
        );
    }

    /** `style` is `undefined` when not exactly one `CallStyle` holds; `env` when probing the getter read the environment. */
    callAliases(timeoutMs?: number): CallAliasAnswer[] {
        const found = answer(this.#invoke("callAliases", this.owners, timeoutMs), arrayOf(isFound)) ?? [];
        return found.flatMap((item): CallAliasAnswer[] => {
            if ("env" in item) return [item];
            const path = this.owners[item.owner];
            return path === undefined ? [] : [{ key: item.key, owner: path, original: item.original, style: item.style ?? undefined }];
        });
    }

    globalKeys(timeoutMs?: number): string[] {
        return answer(this.#invoke("globalKeys", null, timeoutMs), isPath) ?? [];
    }

    /** Each call is made twice, to see whether its result repeats. */
    resolve(requests: readonly ResolveRequest[]): ResolveResult[] {
        const results: ResolveResult[] = [];
        for (let start = 0; start < requests.length; start += RESOLVE_CHUNK) {
            const chunk = requests.slice(start, start + RESOLVE_CHUNK);
            if (this.broken !== undefined) {
                for (let i = 0; i < chunk.length; i++) results.push({ ok: false, error: `not asked: ${this.broken}` });
                continue;
            }
            const answered = this.#invoke("resolve", chunk, RESOLVE_CHUNK_TIMEOUT_MS, itemwise({ ok: false, error: DISAGREE, env: true }));
            const values = answer(answered, arrayOf(isResolveResult));
            if (values !== undefined && values.length === chunk.length) {
                for (const value of values) results.push(value);
                continue;
            }
            // The calls made may have moved the runtime's state, and nothing says which.
            const failure = answered.ok ? "malformed answer" : answered.error;
            this.#tainted = `a batch of calls failed partway (${failure}), leaving the guest's state unknown`;
            for (let i = 0; i < chunk.length; i++) results.push({ ok: false, error: failure });
        }
        return results;
    }

    compare(requests: readonly { left: PropertyPath; right: PropertyPath; op: string }[]): ({ ok: true; value: boolean } | { ok: false; reason: string })[] {
        const answered = this.#invoke("compare", requests, undefined, itemwise({ ok: false, reason: DISAGREE }));
        const values = answer(answered, arrayOf(isComparison));
        return values !== undefined && values.length === requests.length ? values : requests.map(() => ({ ok: false as const, reason: answered.ok ? "malformed answer" : answered.error }));
    }

    /** Objects by identity, primitives by value. */
    stateKey(path: PropertyPath): string | undefined {
        return answer(this.#invoke("stateKey", path), isString);
    }

    /** `data`: every step is a data property (reading runs no code). */
    inspect(path: PropertyPath): { type: string; data: boolean } | undefined {
        return answer(this.#invoke("inspect", path), (v): v is { type: string; data: boolean } => isRecord(v) && isString(v.type) && typeof v.data === "boolean");
    }

    /** Function values and getters. */
    ownCallables(): string[] | undefined {
        return answer(this.#invoke("ownCallables", null), isPath);
    }

    /** Own accessors by owner path (`null`: the storage object) and key, read without running them; `null` for none. */
    accessors(requests: readonly { path: PropertyPath | null; key: string }[]): (AccessorFunctions | null)[] | undefined {
        const found = answer(this.#invoke("accessors", requests), arrayOf(isAccessorPair));
        if (found === undefined || found.length !== requests.length) return undefined;
        return found.map((pair) => (pair === null ? null : { get: functionRecord(pair.get), set: functionRecord(pair.set) }));
    }

    /**
     * One query after a statement that installed accessors: the storage object's own accessors and the requested
     * owner ones (`accessors`), and every owner's own names (`snapshot`) with its accessors among them.
     */
    installed(requests: readonly { path: PropertyPath; key: string }[]): InstalledState | undefined {
        const found = answer(
            this.#invoke("installed", requests),
            (v): v is { requests: { path: PropertyPath | null; key: string }[]; accessors: unknown[]; names: string[][]; accessorNames: string[][] } =>
                isRecord(v) &&
                arrayOf((r): r is { path: PropertyPath | null; key: string } => isRecord(r) && (r.path === null || isPath(r.path)) && isString(r.key))(v.requests) &&
                arrayOf(isAccessorPair)(v.accessors) &&
                v.accessors.length === v.requests.length &&
                arrayOf(isPath)(v.names) &&
                arrayOf(isPath)(v.accessorNames)
        );
        if (found === undefined) return undefined;
        const accessors = found.requests.map((request, i) => {
            const pair = found.accessors[i] as { get: unknown; set: unknown } | null;
            return { ...request, accessor: pair === null ? null : { get: functionRecord(pair.get), set: functionRecord(pair.set) } };
        });
        return { accessors, names: found.names, accessorNames: found.accessorNames };
    }

    /** Whether each storage path holds the global object, read through data properties only. */
    holdsGlobal(paths: readonly PropertyPath[]): boolean[] | undefined {
        const found = answer(
            this.#invoke("holdsGlobal", paths),
            arrayOf((v): v is boolean => typeof v === "boolean")
        );
        return found?.length === paths.length ? found : undefined;
    }

    /** `path` is from the global object (see `Lookup`). Runs no program code. */
    lookup(path: PropertyPath, key: string): Lookup | undefined {
        const [found] = answer(this.#invoke("lookup", [{ path, key }]), arrayOf(isLookup)) ?? [];
        return found;
    }

    dispose(): void {
        this.#main.sandbox.dispose();
        this.#second?.sandbox.dispose();
    }
}
