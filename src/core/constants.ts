import type { Expression, FunctionLike, Node } from "./ast.js";
import { ConstantArrays } from "./constant-arrays.js";
import { BindingConstants } from "./constant-bindings.js";
import type { EvaluateEnv, Evaluation } from "./evaluate.js";
import { FAIL } from "./evaluate.js";
import { ExecutionOrder } from "./execution-order.js";
import { GlobalEscape } from "./global-escape.js";
import type { PassLog } from "./log.js";
import type { ScopeInfo, Variable } from "./scope.js";

export interface ConstantEnv extends EvaluateEnv {
    /** The function a reference holds for good where it is, if any. */
    readonly functionAt: (identifier: Node) => FunctionLike | undefined;
    /**
     * Whether code can reach the binding only by its name: always for one inside a function; for a script global,
     * when the program never spells the name as a property or string, has no `with` or direct `eval`, and uses the
     * global object only with keys that evaluate to other names (other scripts don't touch it: semantic model 2).
     */
    readonly onlyByName: (variable: Variable) => boolean;
}

/** The parts of one environment's analysis; they call each other, each through the ones it names. */
export interface Analysis {
    readonly scopes: ScopeInfo;
    readonly env: ConstantEnv;
    readonly log: PassLog | undefined;
    readonly order: ExecutionOrder;
    readonly globals: GlobalEscape;
    readonly bindings: BindingConstants;
    readonly arrays: ConstantArrays;
    memo<K, V>(cache: Map<K, V | undefined>, key: K, compute: () => V | undefined): V | undefined;
}

/**
 * An evaluation environment that sees through constant bindings, constant `arguments`-array slots and constant arrays:
 *
 * - `var n = 1259;` makes later reads of `n` evaluate to 1259;
 * - `var s = "ab"; s += "cd";` makes reads of `s` after the append evaluate to "abcd";
 * - `var a = [arguments]; a[5] = "x";` makes later reads of `a[5]` evaluate to "x" (#13);
 * - `T = [(f(), "get"), "set"]; a[4] = T;` makes later reads of `a[4][1]` (and `T[1]`) evaluate to "set".
 *
 * A binding is constant when its only definition is a declarator whose initializer evaluates (or `var x;` and one
 * statement `x = v;`), it is never written again but by statements `x += w;` (with `w` constant) after it in the same
 * statement list, and the definition is a statement directly in its function (or program) body, so it runs exactly
 * once on entry (or in a nested list, for reads inside it). A slot is constant when its array is only ever used as
 * `a[constant]`, and the slot is written exactly once, by such a top-level statement, with a constant. Reads get the
 * value only when they come after the last write in execution order (`reachesAfter`).
 *
 * A constant array is a binding written exactly once, with an array literal, by a declarator or a plain assignment
 * statement directly in its body; its elements are what they evaluate to (a sequence: its last expression; the
 * others still run where the array is built), holes are `undefined`. Nothing may change its elements or length, so
 * every reference must be one of: a read `T[k]` (not written, not called: a method would get `T` as `this`) whose key
 * evaluates to an index or "length", or whose value is only converted or tested (`o[T[k]]`, `T[k] === x`,
 * `if (T[k])`: any other key may select an inherited getter returning `T` itself, and operators only read it,
 * semantic model 4), or a copy into a holder (a local variable, or an `arguments`-array slot) every read of which is
 * such a read. A holder written exactly once with the array (an alias) reads it: `a[4][k]` is element k when the read
 * comes after the copy and the copy after the array's definition. The keys a check evaluates may read the array
 * itself; they are evaluated assuming it unchanged, which is sound by induction over time: the first operation that
 * changed it would have to be one of these checked uses, none of which, with the array unchanged until then, changes
 * it or lets its value reach code that could. While assuming, a slot every write of which copies the array reads as
 * the array too (before the first copy it is `undefined`, and reading a key of it throws before any access).
 *
 * Script globals (`var` at the top of a script) are also properties of the global object, so they are refused when
 * code could reach one as a property: the program spells its name (`window.T`, `G[k].T`, `"T"`), uses `with` or a
 * direct `eval`, reads or writes the global object (`globalThis`, `window`, `self`, `this` at the top or in a sloppy
 * function) with a key that doesn't evaluate or evaluates to the name, or hands it on (`var g = window`, `f(this)`).
 * Other scripts don't touch them (semantic model 2).
 */
export const constantEnv = (scopes: ScopeInfo, log?: PassLog): ConstantEnv => {
    const cached = envs.get(scopes);
    if (cached !== undefined && cached.generation === scopes.generation) {
        cached.logRef.log = log;
        return cached.env;
    }
    const logRef: { log: PassLog | undefined } = { log };
    const { env } = new ConstantAnalysis(scopes, logRef);
    envs.set(scopes, { generation: scopes.generation, env, logRef });
    return env;
};

const envs = new WeakMap<ScopeInfo, { readonly generation: number; readonly env: ConstantEnv; readonly logRef: { log: PassLog | undefined } }>();

/** Builds one environment's parts and owns what they share: the memo's keys in progress and the log. */
class ConstantAnalysis implements Analysis {
    readonly scopes: ScopeInfo;
    readonly env: ConstantEnv;
    readonly order: ExecutionOrder;
    readonly globals: GlobalEscape;
    readonly bindings: BindingConstants;
    readonly arrays: ConstantArrays;
    readonly #logRef: { readonly log: PassLog | undefined };
    /** Keys being computed, per cache (one key may be in several: a variable is a constant and a table candidate). */
    readonly #pending = new Map<object, Set<unknown>>();

    constructor(scopes: ScopeInfo, logRef: { readonly log: PassLog | undefined }) {
        this.scopes = scopes;
        this.#logRef = logRef;
        this.order = new ExecutionOrder(scopes, (variable) => this.globals.safe(variable));
        this.globals = new GlobalEscape(this);
        this.bindings = new BindingConstants(this);
        this.arrays = new ConstantArrays(this);
        this.env = {
            ...globalsEnv(scopes),
            lookup: (node) => this.#lookup(node),
            functionAt: (identifier) => this.bindings.functionAt(identifier),
            onlyByName: (variable) => this.globals.safe(variable) === true,
        };
    }

    get log(): PassLog | undefined {
        return this.#logRef.log;
    }

    /**
     * `compute` once per key; `undefined` while it runs (`var a = b, b = a`). Never under another array's assumption,
     * and a success found while `runsAfter` assumes something isn't kept (it is recomputed when needed again).
     */
    memo<K, V>(cache: Map<K, V | undefined>, key: K, compute: () => V | undefined): V | undefined {
        if (cache.has(key)) return cache.get(key);
        let running = this.#pending.get(cache);
        if (running === undefined) {
            running = new Set();
            this.#pending.set(cache, running);
        }
        if (running.has(key)) return undefined;
        running.add(key);
        try {
            const result = this.arrays.unassumed(compute);
            if (!this.order.assuming || result === undefined || result === false) cache.set(key, result);
            return result;
        } finally {
            running.delete(key);
        }
    }

    #lookup(node: Expression): Evaluation {
        if (node.type === "Identifier") {
            const variable = this.scopes.variableOf(node);
            const constant = variable === undefined ? undefined : this.bindings.constantOf(variable);
            if (variable === undefined || constant === undefined) return FAIL;
            return this.order.reachesAfter(variable.scope.block as unknown as Node, constant.after, node) ? { ok: true, value: constant.value } : FAIL;
        }
        if (node.type !== "MemberExpression" || !("property" in node)) return FAIL;
        return this.arrays.read(node);
    }
}

/**
 * An evaluation environment that only knows which identifiers name the global `undefined`, `NaN` and `Infinity`:
 * an identifier the analysis doesn't know (created by a pass since) names the global when no scope declares it.
 */
export const globalsEnv = (scopes: ScopeInfo): EvaluateEnv => ({ isGlobal: (identifier: Node): boolean => scopes.namesGlobal(identifier) });
