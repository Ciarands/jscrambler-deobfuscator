import type { Expression, FunctionLike, IdentifierReference, MemberExpression, Node, Statement } from "../../core/ast.js";
import { isFunctionNode, isLoopNode, propertyKey } from "../../core/ast.js";
import type { JsValue } from "../../core/builtins.js";
import { Closure, getMember, GLOBALS, isCallable, Native, refuse } from "../../core/builtins.js";
import type { Value } from "../../core/evaluate.js";
import type { Held, OuterBinding } from "../../core/interpret.js";
import { Interpreter } from "../../core/interpret.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { scopeWithin } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { KeySet, KeySetAliases } from "../key-sets.js";
import { keySets, mayName } from "../key-sets.js";
import { parentsWithin, returnsOf } from "./builders.js";
import type { PropertyPath, CallAlias, RuntimeModel } from "./model.js";
import { pathName } from "./model.js";
import type { StorageMatcher } from "./storage.js";
import { timeline } from "./effects.js";
import { passedOn, rootStatements } from "./storage.js";

/** Steps for a decoder's builder (a big table's XOR loop takes some 25M) and for one call on it. */
const BUILD_STEPS = 200_000_000;
const CALL_STEPS = 1_000_000;

/** What building a decoder on the host reads the program and the runtime through. */
export interface HostContext {
    readonly runtime: RuntimeModel;
    readonly matcher: StorageMatcher;
    readonly scopes: ScopeInfo;
}

/**
 * A string decoder built on the host by `core/interpret.ts`: its holder `Q`, kept with its closures' state
 * (the table `T`, the counter `R`, `Q.m`) between calls.
 */
export class HostDecoder {
    readonly #interpreter: Interpreter;
    readonly #holder: JsValue;
    readonly #method: string;
    readonly #stage: JsValue;

    constructor(interpreter: Interpreter, holder: JsValue, method: string, stage: JsValue) {
        this.#interpreter = interpreter;
        this.#holder = holder;
        this.#method = method;
        this.#stage = stage;
    }

    /**
     * A call through one of its wrappers, `typeof G.k.m === "function" ? G.k.m.apply(O, arguments) : G.k.m` (the
     * template's functions never read `this`), or of `G.k.m` itself; then the reads `lookup` on its result.
     */
    call(args: readonly Value[], lookup: readonly string[] = []): Held {
        const interpreter = this.#interpreter;
        const method = interpreter.member(this.#holder, this.#method, CALL_STEPS);
        if (!method.ok) return method;
        let result: Held = isCallable(method.value) ? interpreter.callHeld(method.value, this.#holder, args, CALL_STEPS) : method;
        for (const key of lookup) {
            if (!result.ok) break;
            result = interpreter.member(result.value, key, CALL_STEPS);
        }
        return result;
    }

    /** Whether `G.k.m` is still the stage function the builder put there: no call has frozen it to the lookup. */
    get unfrozen(): boolean {
        const method = this.#interpreter.member(this.#holder, this.#method, CALL_STEPS);
        return method.ok && method.value === this.#stage;
    }
}

/** A builtin by its path from the global object, as the interpreter models it; `undefined` when it doesn't. */
const builtinAt = (path: PropertyPath): JsValue | undefined => {
    const [first, ...rest] = path;
    if (first === undefined || !GLOBALS.has(first)) return undefined;
    let value = GLOBALS.get(first);
    for (const key of rest) {
        if (!(value instanceof Native) || !value.members.has(key)) return undefined;
        value = value.members.get(key);
    }
    return value;
};

/**
 * `G.k(...)` as `aliases.ts` rewrites it (the getters behind call aliases are proven to answer so, `getters.ts`):
 * with no arguments the builtin itself; `static`: `Owner.original(...args)`; `call`: `Owner.original.call(receiver,
 * ...rest)`; `method`: `receiver.original(...rest)`, found on the receiver.
 */
const callAliasNative = (storage: string, alias: CallAlias): Native => {
    const original = builtinAt([...alias.owner, alias.original]);
    const owner = alias.owner.length === 0 ? undefined : builtinAt(alias.owner);
    return new Native(`${storage}.${alias.key}`, (self, args, run) => {
        if (alias.style === "method" && args.length > 0) return run.call(getMember(args[0], alias.original, run), args[0], args.slice(1));
        if (original === undefined) return refuse(`it calls ${storage}.${alias.key}, which hands out ${pathName(alias.owner)}.${alias.original}: not modelled`);
        if (args.length === 0) return original;
        return alias.style === "static" ? run.call(original, owner, args) : run.call(original, args[0], args.slice(1));
    });
};

/** Names the storage function may have before any code adds one: its own and inherited ones, in any engine (model 7). */
export const FUNCTION_NAMES: readonly string[] = [
    ...new Set([
        ...Object.getOwnPropertyNames(Function.prototype),
        ...Object.getOwnPropertyNames(Object.prototype),
        "length",
        "name",
        "prototype",
        "arguments",
        "caller",
        // Engines' own extras, past and present.
        "toSource",
        "watch",
        "unwatch",
        "eval",
        "isGenerator",
        "__count__",
        "__parent__",
        "__noSuchMethod__",
    ]),
];

/** Builtins the name probe may call: none changes anything the program can see (`Math.random` only advances its draws). */
const PROBE_BUILTINS: Readonly<Record<string, true>> = {
    "String.fromCharCode": true,
    "Math.random": true,
    "Array.prototype.sort": true,
    "Array.prototype.join": true,
    "Array.prototype.push": true,
};

/** What a root builder evaluated on the host sees, and the root function declarations nothing reassigns. */
export interface HostBindings {
    readonly outer: (identifier: IdentifierReference) => OuterBinding | string;
    readonly aliases: ReadonlyMap<string, ReadonlyMap<string, string>>;
    readonly rootFunction: (variable: Variable | undefined) => FunctionLike | undefined;
}

/**
 * The bindings a root builder `G.k = ...` sees when it runs (model 9: setup globals and aliases reached by name; model
 * 7: builtins intact): the setup's aliases and call aliases (all its statements come first), root function
 * declarations nothing reassigns, the storage `G` (a root function declaration) with its call aliases only, and the
 * builtins `core/builtins.ts` models. Any other name refuses.
 */
export const hostBindings = (cx: HostContext, statement: Statement): HostBindings | string => {
    const { runtime, scopes } = cx;
    const root = rootStatements(runtime.root);
    const index = root.indexOf(statement);
    if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || index < 0) return "its builder isn't a root assignment";
    if ([...runtime.setup].some((setup) => !(root.indexOf(setup as Statement) >= 0 && root.indexOf(setup as Statement) < index)))
        return "a setup call may run after its builder: the aliases it reads may not exist yet";
    const declaration = root.find((node) => node.type === "FunctionDeclaration" && node.id?.name === runtime.storage);
    const storageVariable = declaration?.type === "FunctionDeclaration" && declaration.id !== null ? scopes.variableOf(declaration.id) : undefined;
    if (storageVariable === undefined || storageVariable.defs.length !== 1 || scopes.staticReferences(storageVariable).some((reference) => reference.isWrite()))
        return `${runtime.storage} isn't a root function declaration nothing reassigns`;

    const storage = new Native(runtime.storage);
    for (const alias of runtime.callAliases.values()) storage.members.set(alias.key, callAliasNative(runtime.storage, alias));
    const aliases = new Map<string, Map<string, string>>();
    const globalAliases = new Map<string, string>();
    for (const { owner, alias, original } of runtime.aliases) {
        if (owner.length === 0) {
            globalAliases.set(alias, original);
            continue;
        }
        const name = owner.join(".");
        const map = aliases.get(name) ?? new Map<string, string>();
        map.set(alias, original);
        aliases.set(name, map);
    }
    const rootFunctions = new Set<Node>(root.filter((node) => node.type === "FunctionDeclaration"));
    const rootFunction = (variable: Variable | undefined): FunctionLike | undefined => {
        const def = variable?.defs[0];
        if (variable === undefined || variable.defs.length !== 1 || def?.type !== "FunctionName" || !rootFunctions.has(def.node as unknown as Node)) return undefined;
        return scopes.staticReferences(variable).some((reference) => reference.isWrite()) ? undefined : (def.node as unknown as FunctionLike);
    };
    const outer = (identifier: IdentifierReference): OuterBinding | string => {
        const variable = scopes.variableOf(identifier);
        if (variable !== undefined && variable === storageVariable) return { value: storage };
        const fn = rootFunction(variable);
        if (fn !== undefined) return { function: fn };
        if (variable !== undefined || !scopes.namesGlobal(identifier)) return `it reads ${identifier.name}, a binding of the program outside the builder`;
        const original = globalAliases.get(identifier.name) ?? identifier.name;
        return GLOBALS.has(original) ? { global: original } : `it reads the global ${identifier.name}${original === identifier.name ? "" : ` (${original})`}, which isn't modelled`;
    };
    return { outer, aliases, rootFunction };
};

/**
 * Builds a templated decoder's holder on the host from its one root builder `G.k = (function () {...})()`, with
 * `hostBindings`. Its name probe is replaced by the one value it can find (`probeValue`). `probe` tells what the probe
 * found, for the log.
 */
export const buildHostDecoder = (cx: HostContext, statement: Statement, method: string): { decoder: HostDecoder; probe: string } | string => {
    const { runtime } = cx;
    const bindings = hostBindings(cx, statement);
    if (typeof bindings === "string") return bindings;
    if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") return "its builder isn't a root assignment";
    const { outer, aliases, rootFunction } = bindings;
    const root = rootStatements(runtime.root);
    const index = root.indexOf(statement);
    const probes: string[] = [];
    const shapes = new Map<FunctionLike, ProbeShape | string | undefined>();
    let context: ProbeContext | undefined;
    const substitute = (fn: FunctionLike): { value: JsValue } | undefined => {
        let shape = shapes.get(fn);
        if (!shapes.has(fn)) {
            shape = probeShape(cx, fn);
            shapes.set(fn, shape);
        }
        if (shape === undefined) return undefined;
        if (typeof shape === "string") {
            probes.push(`a name probe isn't replaced: ${shape}`);
            return undefined;
        }
        context ??= probeContext(cx, root, index, statement);
        const found = probeValue(cx, context, shape, rootFunction);
        if (typeof found === "string") {
            probes.push(`a name probe isn't replaced: ${found}`);
            return undefined;
        }
        probes.push(`its name probe finds ${runtime.storage}.${found.key}`);
        const value = new Closure(found.fn, null);
        return { value: new Native(`${runtime.storage}.${found.key}`, () => value) };
    };
    const interpreter = new Interpreter({ outer, aliases, substitute });
    const built = interpreter.evaluate(statement.expression.right, BUILD_STEPS);
    const probe = [...new Set(probes)].join("; ");
    if (!built.ok) return `building it on the host refused: ${built.reason}${probe === "" ? "" : ` (${probe})`}`;
    const stage = interpreter.member(built.value, method, CALL_STEPS);
    if (!stage.ok) return `reading its ${method} on the host refused: ${stage.reason}`;
    return { decoder: new HostDecoder(interpreter, built.value, method, stage.value), probe };
};

/** The name probe's one read `G[X]`. */
interface ProbeShape {
    readonly read: MemberExpression;
}

const isEndless = (node: Node): boolean => (node.type === "WhileStatement" && node.test.type === "Literal" && node.test.value === true) || (node.type === "ForStatement" && node.test === null);

/** Whether a `break` may leave `loop` (labelled ones always may; unlabelled ones inside nested loops and switches leave those). */
const breaksOut = (loop: Node): boolean => {
    let found = false;
    traverse(loop, {
        enter(path) {
            if (path.node !== loop && isFunctionNode(path.node)) path.skip();
        },
        BreakStatement(path) {
            if (path.node.label === null) {
                for (let above: Path | null = path.parentPath; above !== null && above.node !== loop; above = above.parentPath) {
                    if (isLoopNode(above.node) || above.node.type === "SwitchStatement") return;
                }
            }
            found = true;
        },
    });
    return found;
};

/**
 * jscrambler's name probe: a function that returns `G[X]` once it is truthy, `X` a key it computes from its argument:
 *
 *     function (codes) { var c = []; ... c[i] = fromCharCode(codes[i] + d); ...
 *         do { x = c.sort(function () { return 0.5 - random(); }).join(""); found = G[x]; } while (!found);
 *         return found; }
 *
 * or `while (true) { ...; found = G[x]; if (found) { return found; } }`. `undefined` when `fn` reads no computed key
 * of `G`, the reason when it does but isn't one. Replaced by the value it finds, it must do nothing else: it writes
 * only its own locals (arrays and objects it made, by element), calls only `PROBE_BUILTINS` (also through aliases and
 * call aliases, model 7), reads `G` only there; and it only returns that truthy value. (Its `Math.random` calls only
 * order the permutations it tries: dropping them leaves later draws a sequence a real run could make too.)
 */
const probeShape = (cx: HostContext, fn: FunctionLike): ProbeShape | string | undefined => {
    const { matcher, scopes, runtime } = cx;
    const callAliasOf = (callee: Node): CallAlias | undefined =>
        callee.type === "MemberExpression" && matcher.isStorage(callee.object) ? runtime.callAliases.get(propertyKey(callee) ?? "") : undefined;
    const reads: MemberExpression[] = [];
    let other = false;
    let nested = false;
    let depth = 0;
    traverse(fn as unknown as Node, {
        enter(path) {
            if (path.node !== (fn as unknown as Node) && isFunctionNode(path.node)) depth++;
        },
        exit(path) {
            if (path.node !== (fn as unknown as Node) && isFunctionNode(path.node)) depth--;
        },
        Identifier(path) {
            const node = path.node;
            if (!matcher.isStorage(node) || matcher.isAliasBinding(node)) return;
            const parent = path.parent;
            const member = parent?.type === "MemberExpression" && path.key === "object" ? path.parentPath : null;
            if (member !== null && member.parent?.type === "CallExpression" && member.key === "callee" && callAliasOf(member.node) !== undefined) return;
            if (member !== null && parent?.type === "MemberExpression" && parent.computed && propertyKey(parent) === undefined && !member.isWriteTarget()) {
                reads.push(parent);
                if (depth > 0) nested = true;
            } else other = true;
        },
    });
    const [read] = reads;
    // A function whose computed read is in one it makes holds the probe; it isn't one.
    if (read === undefined || nested) return undefined;
    if (other || reads.length > 1) return `it uses ${runtime.storage} otherwise than by one computed read and call aliases`;

    const own = (variable: Variable | undefined): boolean => variable !== undefined && scopeWithin(variable.scope, fn as unknown as Node);
    /** A local of the probe given only what `allowed` accepts. */
    const localOf = (node: Node, allowed: (value: Node | null | undefined) => boolean): boolean => {
        const variable = node.type === "Identifier" ? scopes.variableOf(node) : undefined;
        return own(variable) && scopes.staticReferences(variable as Variable).every((reference) => !reference.isWrite() || allowed(reference.writeExpr as unknown as Node | null | undefined));
    };
    /** A local holding only arrays and objects the probe makes. */
    const fresh = (node: Node): boolean => localOf(node, (value) => value?.type === "ArrayExpression" || value?.type === "ObjectExpression");
    /** `Owner.name` through global and property aliases (model 9: setup globals reached by name). */
    const globalMember = (node: Node): string | undefined => {
        if (node.type !== "MemberExpression" || node.object.type !== "Identifier" || !scopes.namesGlobal(node.object)) return undefined;
        const name = node.object.name;
        const owner = runtime.aliases.find((alias) => alias.owner.length === 0 && alias.alias === name)?.original ?? name;
        const key = propertyKey(node);
        return key === undefined ? undefined : `${owner}.${runtime.aliases.find((alias) => pathName(alias.owner) === owner && alias.alias === key)?.original ?? key}`;
    };
    /** What a value names among the probe builtins: a call alias's handout or a global's member. */
    const builtinOf = (node: Node | null | undefined): string | undefined => {
        if (node === null || node === undefined) return undefined;
        const alias = node.type === "CallExpression" && node.arguments.length === 0 ? callAliasOf(node.callee) : undefined;
        return alias !== undefined ? `${pathName(alias.owner)}.${alias.original}` : globalMember(node);
    };
    const arrayMethod = (key: string | undefined): string | undefined =>
        key === undefined ? undefined : `Array.prototype.${runtime.aliases.find((alias) => pathName(alias.owner) === "Array.prototype" && alias.alias === key)?.original ?? key}`;
    /** An array the probe made, or one its sort gives back. */
    const arrayValued = (node: Node): boolean => {
        if (fresh(node)) return true;
        if (node.type !== "CallExpression") return false;
        const alias = callAliasOf(node.callee);
        const [receiver] = node.arguments;
        if (alias !== undefined) return pathName(alias.owner) === "Array.prototype" && alias.original === "sort" && alias.style !== "static" && receiver !== undefined && arrayValued(receiver);
        return node.callee.type === "MemberExpression" && arrayMethod(propertyKey(node.callee)) === "Array.prototype.sort" && arrayValued(node.callee.object);
    };
    /** The builtin a call calls, if one of the probe's. */
    const called = (node: Node & { type: "CallExpression" }): boolean => {
        const { callee } = node;
        if (callee.type === "Identifier") return localOf(callee, (value) => PROBE_BUILTINS[builtinOf(value) ?? ""] === true);
        const alias = callAliasOf(callee);
        if (alias !== undefined) {
            const name = `${pathName(alias.owner)}.${alias.original}`;
            const [receiver] = node.arguments;
            if (pathName(alias.owner) === "Array.prototype" && node.arguments.length > 0 && (alias.style === "static" || receiver === undefined || !arrayValued(receiver))) return false;
            return PROBE_BUILTINS[name] === true;
        }
        if (callee.type !== "MemberExpression") return false;
        const name = arrayValued(callee.object) ? arrayMethod(propertyKey(callee)) : globalMember(callee);
        return PROBE_BUILTINS[name ?? ""] === true;
    };
    let problem: string | undefined;
    traverse(fn as unknown as Node, {
        enter(path) {
            if (problem !== undefined) path.skip();
        },
        AssignmentExpression(path) {
            const target = path.node.left;
            if (target.type === "Identifier" ? !own(scopes.variableOf(target)) : target.type !== "MemberExpression" || !fresh(target.object)) problem = "it writes something other than its own locals";
        },
        UpdateExpression(path) {
            const target = path.node.argument;
            if (target.type !== "Identifier" || !own(scopes.variableOf(target))) problem = "it writes something other than its own locals";
        },
        UnaryExpression(path) {
            if (path.node.operator === "delete") problem = "it deletes a property";
        },
        CallExpression(path) {
            if (!called(path.node)) problem = "it calls something other than String.fromCharCode, Math.random and its arrays' sort, join and push";
        },
        NewExpression() {
            problem = "it constructs something";
        },
        TaggedTemplateExpression() {
            problem = "it calls a template tag";
        },
    });
    if (problem !== undefined) return problem;

    // Every return gives one local, written only by `found = G[x]`, when it is truthy; nothing runs off the end.
    const body = fn.body?.type === "BlockStatement" ? fn.body.body : undefined;
    const returns = returnsOf(fn as unknown as Node);
    const first = returns[0];
    const found = first?.type === "ReturnStatement" && first.argument?.type === "Identifier" ? scopes.variableOf(first.argument) : undefined;
    if (body === undefined || found === undefined || !own(found)) return "it doesn't return one of its locals";
    const parents = parentsWithin(fn as unknown as Node);
    const written = scopes.staticReferences(found).every((reference) => {
        if (!reference.isWrite()) return true;
        const assignment = parents.get(reference.identifier as unknown as Node);
        return assignment?.type === "AssignmentExpression" && assignment.operator === "=" && assignment.right === read;
    });
    if (!written) return `${found.name} is written otherwise than by its read of ${runtime.storage}`;
    const truthy = (ret: Node): boolean => {
        if (ret.type !== "ReturnStatement" || ret.argument?.type !== "Identifier" || scopes.variableOf(ret.argument) !== found) return false;
        const holder = parents.get(ret);
        // `if (found) { return found; }`
        const guard = holder?.type === "BlockStatement" && holder.body.length === 1 ? parents.get(holder) : holder;
        if (guard?.type === "IfStatement" && guard.alternate === null && guard.test.type === "Identifier" && scopes.variableOf(guard.test) === found) return true;
        // `do { ... } while (!found); return found;`
        const list = holder?.type === "BlockStatement" ? holder.body : undefined;
        const before = list?.[list.indexOf(ret as Statement) - 1];
        return (
            before?.type === "DoWhileStatement" &&
            before.test.type === "UnaryExpression" &&
            before.test.operator === "!" &&
            before.test.argument.type === "Identifier" &&
            scopes.variableOf(before.test.argument) === found
        );
    };
    if (!returns.every(truthy)) return "a return may give something other than a truthy read";
    const last = body.at(-1);
    if (last === undefined || !(last.type === "ReturnStatement" || (isEndless(last) && !breaksOut(last)))) return "it may run off its end";
    return { read };
};

/** What the probes of one builder may find: `G`'s keys by the time it runs, and what may have changed them. */
interface ProbeContext {
    /** Keys root statements before the builder assign, by key: those statements. */
    readonly assigned: ReadonlyMap<string, readonly Statement[]>;
    /** Other writes to `G` that may run before the builder; `key` is `undefined` for a computed one. */
    readonly writes: readonly { readonly key: string | undefined; readonly node: MemberExpression }[];
    /** Why `G` may have changed otherwise before the builder. */
    readonly otherwise: string | undefined;
    readonly keySetOf: (key: Expression) => KeySet | undefined;
}

/** Assignment operators that may leave their right side in their target. */
const STORING = new Set(["=", "||=", "&&=", "??="]);

/**
 * Code that may run before the builder (root statement `index`) finishes: root statements before it, and root
 * function declarations (they exist from the start); functions made in later statements can't. `G` changes only
 * through code naming its paths (model 3): writes there, `this` in its methods called there, a call it is handed to
 * there, a place it is stored at there; and the setup's keys (`setupKeys`).
 *
 * A value that may be `G` (`G` itself, `c ? G : y`, `x || G`, `(a, G)`) stored in a local, or at a static key of a
 * local array read only at static keys (`a[5] = G`), makes that place hold `G` maybe: its reads are uses of `G` too.
 * Stored anywhere else, or in an object or array literal, it may be reached by code the walk doesn't follow.
 *
 * Code that runs only while setup calls run (their top level, and functions every call of which comes from there:
 * `timeline`) was followed by the setup evaluation (`getters.ts`), which refuses writing `G`'s properties, reading
 * them, or handing `G` to code it doesn't follow; what such code does to `G` there is in `setupKeys`. What it leaves
 * in places later code may read is followed all the same.
 */
const probeContext = (cx: HostContext, root: readonly Statement[], index: number, builder: Statement): ProbeContext => {
    const { matcher, runtime, scopes } = cx;
    const assigned = new Map<string, Statement[]>();
    let writes: { key: string | undefined; node: MemberExpression }[] = [];
    let otherwise: string | undefined;
    const direct = new Set<Node>();
    for (const [i, statement] of root.entries()) {
        if (i >= index || statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") continue;
        const left = statement.expression.left;
        const key = left.type === "MemberExpression" && matcher.isStorage(left.object) ? propertyKey(left) : undefined;
        if (key === undefined) continue;
        assigned.set(key, [...(assigned.get(key) ?? []), statement]);
        direct.add(left);
    }

    const { timingOf } = timeline(runtime, scopes);
    /** The top level of root statement `at` (`fn` `undefined`) or `fn` runs only while setup calls run. */
    const setupRun = (fn: Node | undefined, at: number): boolean => {
        const timing = fn === undefined ? { kind: "prelude" as const, first: at, last: at } : timingOf(fn);
        if (timing.kind !== "prelude") return false;
        for (let i = timing.first; i <= timing.last; i++) if (!runtime.setup.has(root[i] as Node)) return false;
        return true;
    };
    /** Locals that may hold `G`; by local array, its static keys that may. */
    const held = new Set<Variable>();
    const slots = new Map<Variable, Set<string>>();
    const slotted = new Map<Variable, boolean>();
    /** `var a = [...]`, written by that alone and read only at static keys (`a[5]`, `a.length`). */
    const isSlotted = (variable: Variable): boolean => {
        let known = slotted.get(variable);
        if (known === undefined) {
            const definition = variable.defs.length === 1 ? (variable.defs[0]?.node as unknown as Node) : undefined;
            const references = scopes.references(variable);
            known =
                variable.scope.type !== "global" &&
                definition?.type === "VariableDeclarator" &&
                definition.init?.type === "ArrayExpression" &&
                references !== undefined &&
                references.every((reference) => {
                    const identifier = reference.identifier as unknown as Node;
                    if (reference.isWrite()) return identifier === definition.id && !reference.isRead();
                    const parent = scopes.parentOf(identifier);
                    return parent?.type === "MemberExpression" && parent.object === identifier && propertyKey(parent) !== undefined;
                });
            slotted.set(variable, known);
        }
        return known;
    };
    let grown = false;
    const store = (target: Node): void => {
        if (target.type === "Identifier") {
            const variable = scopes.staticVariableOf(target);
            if (variable !== undefined && variable.scope.type !== "global" && scopes.references(variable) !== undefined) {
                if (!matcher.aliases.has(variable) && !held.has(variable)) {
                    held.add(variable);
                    grown = true;
                }
                return;
            }
        } else if (target.type === "MemberExpression" && target.object.type === "Identifier") {
            const variable = scopes.staticVariableOf(target.object);
            const key = propertyKey(target);
            if (variable !== undefined && key !== undefined && isSlotted(variable)) {
                const keys = slots.get(variable) ?? new Set<string>();
                if (!keys.has(key)) {
                    keys.add(key);
                    slots.set(variable, keys);
                    grown = true;
                }
                return;
            }
        }
        otherwise ??= `${runtime.storage} is stored somewhere before the builder: code reaching it there may add keys`;
    };
    /** `G` handed to an IIFE's parameter: an alias, whose uses are `G`'s. */
    const toAlias = (call: Node, argument: Node): boolean => {
        if (call.type !== "CallExpression" || (call.callee.type !== "FunctionExpression" && call.callee.type !== "ArrowFunctionExpression")) return false;
        const param = call.callee.params[call.arguments.indexOf(argument as never)];
        return param !== undefined && matcher.isAliasBinding(param);
    };
    /** The value at `path` may be `G`; `during`: it runs only while setup calls run. */
    const use = (path: Path, during: boolean): void => {
        const member = path.parent?.type === "MemberExpression" && path.key === "object" ? (path.parentPath as Path<MemberExpression>) : null;
        if (member !== null) {
            if (during) return;
            if (member.isWriteTarget()) {
                if (!direct.has(member.node)) writes.push({ key: propertyKey(member.node), node: member.node });
            } else if (member.parent?.type === "CallExpression" && member.key === "callee") {
                const key = propertyKey(member.node);
                if (key === undefined || (!runtime.callAliases.has(key) && !runtime.wrappers.has(key)))
                    otherwise ??= `${runtime.storage}${key === undefined ? "[?]" : `.${key}`}() may run with ${runtime.storage} as this before the builder`;
            }
            return;
        }
        const { outer, literal } = passedOn(path);
        const holder = outer.parent;
        if (literal) otherwise ??= `${runtime.storage} is stored somewhere before the builder: code reaching it there may add keys`;
        else if (holder?.type === "AssignmentExpression" && outer.key === "right") {
            if (STORING.has(holder.operator)) store(holder.left);
        } else if ((holder?.type === "VariableDeclarator" && outer.key === "init") || (holder?.type === "AssignmentPattern" && outer.key === "right")) {
            store(holder.type === "VariableDeclarator" ? holder.id : holder.left);
        } else if ((holder?.type === "CallExpression" || holder?.type === "NewExpression") && outer.key === "arguments" && !during && !toAlias(holder, outer.node)) {
            otherwise ??= `${runtime.storage} is handed to a call before the builder, which may add keys`;
        }
    };

    do {
        grown = false;
        writes = [];
        otherwise = undefined;
        for (const [i, statement] of root.entries()) {
            if (statement === builder || (i >= index && statement.type !== "FunctionDeclaration")) continue;
            const during = [setupRun(undefined, i)];
            traverse(statement, {
                enter(path) {
                    if (isFunctionNode(path.node)) during.push(setupRun(path.node, i));
                },
                exit(path) {
                    if (isFunctionNode(path.node)) during.pop();
                },
                Identifier(path) {
                    const node = path.node;
                    if (matcher.isStorage(node)) {
                        if (!matcher.isAliasBinding(node) && !(path.parent?.type === "FunctionDeclaration" && path.key === "id")) use(path, during.at(-1) === true);
                        return;
                    }
                    if (held.size === 0) return;
                    const variable = scopes.staticVariableOf(node);
                    if (variable !== undefined && held.has(variable) && scopes.referenceOf(node)?.isRead() === true) use(path, during.at(-1) === true);
                },
                MemberExpression(path) {
                    const { object } = path.node;
                    const variable = slots.size === 0 || object.type !== "Identifier" ? undefined : scopes.staticVariableOf(object);
                    const key = propertyKey(path.node);
                    if (variable !== undefined && key !== undefined && slots.get(variable)?.has(key) === true && !path.isWriteTarget()) use(path, during.at(-1) === true);
                },
            });
        }
    } while (grown);
    return { assigned, writes, otherwise, keySetOf: keySets(scopes, parentsWithin(builder), keySetAliases(cx)) };
};

/** The setup's aliases and call aliases, for key sets found before the aliases pass. */
export const keySetAliases = (cx: HostContext): KeySetAliases => ({
    aliasOf: (owner, name) => cx.runtime.aliases.find((alias) => alias.owner.join(".") === owner && alias.alias === name)?.original,
    callAlias: (call) => {
        const callee = call.callee;
        if (callee.type !== "MemberExpression" || !cx.matcher.isStorage(callee.object)) return undefined;
        const alias = cx.runtime.callAliases.get(propertyKey(callee) ?? "");
        return alias === undefined ? undefined : { owner: alias.owner.join("."), original: alias.original, style: alias.style };
    },
});

/** Whether two key sets may name one key. */
const mayShare = (a: KeySet, b: KeySet): boolean =>
    [...a.strings].some((key) => mayName(b, key)) ||
    [...b.strings].some((key) => mayName(a, key)) ||
    (a.chars !== undefined && b.chars !== undefined && [...a.chars].some((char) => b.chars?.has(char) === true));

/**
 * The value the probe finds: its key set (`key-sets.ts`) may name exactly one key `G` has when the builder runs, given
 * by one root assignment `G.k = f` before it of a root function nothing reassigns (truthy). Refused when the set names
 * none, several, or a key whose value isn't that (inherited ones, the setup's, unproven aliases), or when a write or
 * another change of `G` before the builder may add one (`probeContext`).
 */
const probeValue = (
    cx: HostContext,
    context: ProbeContext,
    shape: ProbeShape,
    rootFunction: (variable: Variable | undefined) => FunctionLike | undefined
): { key: string; fn: FunctionLike } | string => {
    const { runtime, scopes } = cx;
    const keys = context.keySetOf(shape.read.property as Expression);
    if (keys === undefined) return "key-sets can't tell which keys it may read";
    if (context.otherwise !== undefined) return context.otherwise;
    for (const write of context.writes) {
        const theirs = write.key === undefined ? context.keySetOf(write.node.property as Expression) : { strings: new Set([write.key]), chars: undefined };
        if (theirs === undefined || mayShare(keys, theirs)) return `a write to ${runtime.storage}${write.key === undefined ? "[?]" : `.${write.key}`} before the builder may add a key it finds`;
    }
    const other = [...FUNCTION_NAMES, ...runtime.inheritedKeys, ...runtime.unprovenAliases, ...runtime.setupKeys].find((key) => mayName(keys, key));
    if (other !== undefined) return `it may find ${runtime.storage}.${other}, which no root assignment gives`;
    const candidates = [...context.assigned.keys()].filter((key) => mayName(keys, key));
    const [key] = candidates;
    if (key === undefined) return "no key it may read exists when the builder runs";
    if (candidates.length > 1) return `it may find any of ${candidates.map((name) => `${runtime.storage}.${name}`).join(", ")}`;
    const statements = context.assigned.get(key) ?? [];
    const [only] = statements;
    const right = only?.type === "ExpressionStatement" && only.expression.type === "AssignmentExpression" ? only.expression.right : undefined;
    const fn = statements.length === 1 && right?.type === "Identifier" ? rootFunction(scopes.variableOf(right)) : undefined;
    return fn === undefined ? `${runtime.storage}.${key} isn't given a root function nothing reassigns by one root assignment` : { key, fn };
};
