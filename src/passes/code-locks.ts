import type { Expression, Function as FunctionNode, MemberExpression, Node, Statement } from "../core/ast.js";
import { memberPath, propertyKey } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import type { Primitive } from "../core/build.js";
import type { ScopeInfo } from "../core/scope.js";
import type { Path } from "../core/traverse.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { Slot } from "./emulate/builders.js";
import { bodyOf, builderOf, definitionOf, returnsOf, sameSlot, slotOf, slotsOnly } from "./emulate/builders.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { Staleness, StorageEffects } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import type { RuntimeModel } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import type { StorageMatcher } from "./emulate/storage.js";
import { onlyTested, rootStatements } from "./emulate/storage.js";
import { localityOf } from "./locality.js";

type FastPath =
    | { readonly ok: true; readonly answer: Primitive; readonly method: FunctionNode; readonly cache: Slot; readonly parents: ReadonlyMap<Node, Node> }
    | { readonly ok: false; readonly reason: string; readonly node: Node };

const refused = (reason: string, node: Node): FastPath => ({ ok: false, reason, node });

const isPrimitiveLiteral = (node: Node | null | undefined): node is Node & { type: "Literal"; value: Primitive } =>
    node?.type === "Literal" && (node.value === null || typeof node.value === "string" || typeof node.value === "number" || typeof node.value === "boolean");

/**
 * The cached answer of the code lock `method` that `iife` builds, proven from its code:
 *
 *     G.k = function () { var S = [arguments]; S[j] = undefined; S[i] = {}; S[i].method = function () {
 *         var X = [arguments];
 *         if (S[j]) return L;                  // the answer, once the cache is set
 *         ...checks...; S[j] = 15; return 91;  // the first call: checks, sets the cache
 *     }; return S[i]; }();
 *
 * (or the methods in a returned object literal). The cache is a slot of an array the builder declares and keeps to
 * itself. Once set, nothing clears it (its only writes are the builder's own top-level statements, which ran once,
 * and truthy literals the method stores at its own top level), so every later call returns `L` and does nothing else.
 * The method's other returns are literals other than `L`: a call that answers `L` took the cached path.
 */
const fastPathOf = (iife: FunctionNode, method: string, scopes: ScopeInfo): FastPath => {
    const builder = builderOf(iife, scopes);
    if (typeof builder === "string") return refused(builder, iife);
    const fn = builder.methods.get(method);
    if (fn === undefined) return refused(`its builder gives it no plain function ${method}`, iife);
    if (fn.async || fn.generator) return refused(`${method} is async or a generator`, fn);

    // Its first effective statement reads the cache and returns the answer.
    const statements = bodyOf(fn);
    let first = 0;
    while (
        statements[first]?.type === "VariableDeclaration" &&
        (statements[first] as Statement & { type: "VariableDeclaration" }).declarations.every((d) => d.init === null || d.init.type === "ArrayExpression")
    )
        first++;
    const check = statements[first];
    if (check?.type !== "IfStatement" || check.alternate !== null) return refused(`${method} doesn't start with a cache check`, fn);
    const taken = check.consequent.type === "BlockStatement" && check.consequent.body.length === 1 ? check.consequent.body[0] : check.consequent;
    if (taken?.type !== "ReturnStatement" || !isPrimitiveLiteral(taken.argument)) return refused(`${method}'s cache check doesn't return a literal`, check);
    const answer = taken.argument.value;
    const cache = slotOf(check.test, scopes);
    if (cache === undefined || (cache.variable.scope.block as unknown as Node) !== iife || !slotsOnly(cache.variable, builder.parents)) {
        return refused(`${method}'s cache isn't a slot of an array its builder keeps to itself`, check.test);
    }

    // Writes to the cache: the builder's own statements, and truthy literals the method stores at its own top level.
    let clearable: Node | undefined;
    traverse(iife, {
        AssignmentExpression(path) {
            if (clearable !== undefined || !sameSlot(cache, slotOf(path.node.left, scopes))) return;
            const statement = path.parent;
            const inBuilder = statement?.type === "ExpressionStatement" && builder.statements.includes(statement);
            const setsAnswer =
                statement?.type === "ExpressionStatement" && statements.includes(statement) && path.node.operator === "=" && isPrimitiveLiteral(path.node.right) && Boolean(path.node.right.value);
            if (!inBuilder && !setsAnswer) clearable = path.node;
        },
        UpdateExpression(path) {
            if (clearable === undefined && sameSlot(cache, slotOf(path.node.argument, scopes))) clearable = path.node;
        },
    });
    if (clearable !== undefined) return refused(`${method}'s cache may be cleared`, clearable);

    // The other returns can't give the answer: answering it means the cache was read.
    const other = returnsOf(fn).find((r) => r !== taken && (r.type !== "ReturnStatement" || !isPrimitiveLiteral(r.argument) || Object.is(r.argument.value, answer)));
    if (other !== undefined) return refused(`${method} may answer ${String(answer)} without its cache`, other);
    return { ok: true, answer, method: fn, cache, parents: builder.parents };
};

/**
 * A no-argument call of a storage path `G.k.m` (or `G.w`): the reference to `G` it starts from, its statement when it
 * is one, whether its value is discarded (a statement, or not last in a sequence), and whether only its truthiness
 * is used.
 */
export interface CallSite {
    readonly call: Expression & { type: "CallExpression" };
    readonly site: Node;
    readonly statement: Statement | undefined;
    readonly discarded: boolean;
    readonly tested: boolean;
}

/** Whether only the truthiness of the value at `path` is used: a condition or `!` operand, possibly through `&&`/`||`. */
const onlyTruthiness = (path: Path): boolean => {
    let operand = path;
    while (operand.parent?.type === "LogicalExpression" && operand.parent.operator !== "??" && operand.parentPath !== null) operand = operand.parentPath;
    const parent = operand.parent;
    switch (parent?.type) {
        case "IfStatement":
        case "ConditionalExpression":
        case "WhileStatement":
        case "DoWhileStatement":
        case "ForStatement":
            return operand.key === "test";
        case "UnaryExpression":
            return parent.operator === "!";
        default:
            return false;
    }
};

/** A static reference `x.k`, the root statement it sits in, and the reference to `G` it starts from (when `x` is one). */
interface KeyReference {
    readonly node: Node;
    readonly root: Node | undefined;
    readonly site: Node | undefined;
}

/** What the program does with the storage object, from one walk. */
export interface Survey {
    /** No-argument calls of static paths `G.k.m` and `G.w`, by path. */
    readonly calls: Map<string, { path: PropertyPath; sites: CallSite[] }>;
    /** Where `G` (the reference `site`) is used as a value or read with a computed key: any key may be read there. */
    readonly dynamic: readonly { readonly node: Node; readonly site: Node }[];
}

export const survey = (program: Node, matcher: StorageMatcher, scopes: ScopeInfo): Survey => {
    const calls = new Map<string, { path: PropertyPath; sites: CallSite[] }>();
    const dynamic: { node: Node; site: Node }[] = [];
    /** `var s = G` with `s` a real alias (cleanup's rule): `s` holds G under a name the matcher follows. */
    const isAliasDeclarator = (node: Node | null): boolean => {
        if (node?.type !== "VariableDeclarator" || node.id.type !== "Identifier") return false;
        const variable = scopes.variableOf(node.id);
        return variable !== undefined && matcher.aliases.has(variable);
    };
    traverse(program, {
        CallExpression(path) {
            const call = path.node;
            if (call.arguments.length > 0 || call.callee.type !== "MemberExpression") return;
            const target = memberPath(call.callee as MemberExpression);
            if (target === undefined || target.keys.length === 0 || !matcher.isStorage(target.root)) return;
            const id = JSON.stringify(target.keys);
            const entry = calls.get(id) ?? { path: target.keys, sites: [] };
            const parent = path.parent;
            const statement = parent?.type === "ExpressionStatement" ? parent : undefined;
            const discarded = statement !== undefined || (parent?.type === "SequenceExpression" && parent.expressions.at(-1) !== call);
            entry.sites.push({ call, site: target.root, statement, discarded, tested: onlyTruthiness(path) });
            calls.set(id, entry);
        },
        MemberExpression(path) {
            const node = path.node;
            if (matcher.isStorage(node.object) && propertyKey(node) === undefined) dynamic.push({ node, site: node.object });
        },
        Identifier(path) {
            if (!matcher.isStorage(path.node)) return;
            const parent = path.parent;
            const asObject = parent?.type === "MemberExpression" && path.key === "object";
            const asDeclaration = parent?.type === "FunctionDeclaration" && path.key === "id";
            if (!asObject && !asDeclaration && !isAliasDeclarator(parent) && !path.isWriteTarget() && !onlyTested(path)) dynamic.push({ node: path.node, site: path.node });
        },
    });
    return { calls, dynamic };
};

/**
 * Every static member reference `x.k` with `k` one of `keys`, whatever `x` is (an alias the matcher can't follow, as
 * under a direct eval, or `this`, still names the key), by key.
 */
const keyReferences = (program: Node, runtime: RuntimeModel, matcher: StorageMatcher, keys: ReadonlySet<string>): Map<string, KeyReference[]> => {
    const references = new Map<string, KeyReference[]>();
    const roots = new Set<Node>(rootStatements(runtime.root));
    let root: Node | undefined;
    traverse(program, {
        enter(path) {
            if (roots.has(path.node)) root = path.node;
        },
        exit(path) {
            if (path.node === root) root = undefined;
        },
        MemberExpression(path) {
            const node = path.node;
            const key = propertyKey(node);
            if (key === undefined || !keys.has(key)) return;
            const reference = { node, root, site: matcher.isStorage(node.object) ? node.object : undefined };
            const list = references.get(key);
            if (list === undefined) references.set(key, [reference]);
            else list.push(reference);
        },
    });
    return references;
};

/**
 * Why a reference to the holder key `path[0]` may reach the lock other than through `sites`: it is none of them, isn't
 * in the builder's own statement or the definition of a wrapper of the lock nothing uses, and may run once the
 * builder has (before it, `G.k` isn't the lock yet).
 */
const strayReference = (lock: Lock, program: Node, runtime: RuntimeModel, matcher: StorageMatcher, effects: StorageEffects): Node | undefined => {
    const { path, sites, builder } = lock;
    const wrappers = [...runtime.wrappers.values()].filter((wrapper) => wrapper.target.length === path.length && wrapper.target.every((key, i) => key === path[i]));
    const references = keyReferences(program, runtime, matcher, new Set([path[0] as string, ...wrappers.map((wrapper) => wrapper.key)]));
    const unused = new Set(wrappers.filter((wrapper) => (references.get(wrapper.key) ?? []).every((reference) => reference.root === wrapper.definition)).map((wrapper) => wrapper.definition));
    const callees = new Set(sites.map(({ call }) => (call.callee as MemberExpression).object as Node));
    return references
        .get(path[0] as string)
        ?.find(({ node, root, site }) => !callees.has(node) && root !== builder && (root === undefined || !unused.has(root)) && (site === undefined || !effects.runsBefore(site, builder)))?.node;
};

/** What a call of a lock becomes: removed (a statement), replaced by the cached answer, or kept. */
type Disposition = "remove" | "answer" | "keep";

/** A proven lock, its calls, and what full mode would do with each. */
interface Lock {
    readonly path: PropertyPath;
    readonly sites: readonly CallSite[];
    readonly full: readonly Disposition[];
    readonly staleness: readonly (Staleness | undefined)[];
    readonly fast: FastPath & { ok: true };
    readonly builder: Statement;
}

/** `G.key()` with `key` a global-read getter (emulate's fact) the program never replaces: a read of that global property. */
const isGlobalRead = (call: Node, runtime: RuntimeModel, matcher: StorageMatcher, effects: StorageEffects): boolean => {
    if (call.type !== "CallExpression" || call.arguments.length > 0 || call.callee.type !== "MemberExpression") return false;
    const key = propertyKey(call.callee);
    return key !== undefined && runtime.globalReads.has(key) && matcher.isStorage(call.callee.object) && effects.staleAt(call.callee.object, [key]) === undefined;
};

/** Why the whole lock can't go (its first call included), if anything stops it. */
const fullModeRefusal = (
    lock: Lock,
    context: { program: Node; runtime: RuntimeModel; scopes: ScopeInfo; matcher: StorageMatcher; effects: StorageEffects; uses: Survey }
): { reason: string; node: Node } | undefined => {
    const { path, sites, full, staleness, fast, builder } = lock;
    const { program, runtime, scopes, matcher, effects, uses } = context;
    if (path.length !== 2) return { reason: "its holder isn't a key of the storage object itself", node: builder };
    const effect = localityOf(fast.method, fast.cache, scopes, fast.parents, (call) => isGlobalRead(call, runtime, matcher, effects));
    if (effect !== undefined) return { reason: `its checks may change more than their own objects: ${effect.reason}`, node: effect.node };
    const used = sites.findIndex(({ discarded }, i) => !discarded && full[i] !== "answer");
    if (used !== -1) return { reason: staleness[used]?.reason ?? "a call whose value is used runs in the prelude, where it may be the first call", node: (sites[used] as CallSite).call };
    const dynamic = uses.dynamic.find(({ node, site }) => !effects.runsBefore(site, builder) && !effects.keptAsGlobal(node));
    if (dynamic !== undefined) return { reason: `${runtime.storage} is used as a value or read with a computed key once the lock is built, which may reach it`, node: dynamic.node };
    const stray = strayReference(lock, program, runtime, matcher, effects);
    if (stray !== undefined) return { reason: `${runtime.storage}.${path[0]} is used other than by its calls, its builder and unused wrappers`, node: stray };
    return undefined;
};

/** Put in each call's replacement, then remove the call statements in `removals` (an empty statement where one must stay). */
export const rewriteCalls = (program: Node, replacements: ReadonlyMap<Node, Node>, removals: ReadonlySet<Node>): void => {
    replaceNodes(program, replacements);
    if (removals.size === 0) return;
    traverse(program, {
        ExpressionStatement(path) {
            if (!removals.has(path.node)) return;
            if (path.isInStatementList()) path.remove();
            else path.replace(at<Statement>({ type: "EmptyStatement" }, path.node));
        },
    });
};

/**
 * Code locks: jscrambler's environment checks (`G.k.m()`, usually through a wrapper the wrappers pass has inlined)
 * run once and then answer from a cache. The prelude makes the first call; every call after it takes the cached path:
 * no effect, the same answer.
 *
 * Proof per lock: its builder's code shows the cached path and that the cache, once set, stays set (`fastPathOf`);
 * one call in the guest, which ran the prelude, answers the cached value (so the cache is set); and each call site
 * reaches the lock the snapshot holds (nothing writes the path later, and a prelude call runs after the builder).
 *
 * Full mode (the whole lock goes): its first call, too, changes nothing but objects it creates and its cache
 * (`localityOf`), and the environment passes its checks (semantic model 5), so that call only sets the cache. Every
 * statement call goes, and a call whose value is discarded becomes the answer (as good as no call); a call whose
 * value is used becomes the answer only when it runs after the prelude (the prelude's calls may be the first one,
 * answering the checks' value). Nothing else can reach the lock: every static reference to its holder key (on any
 * object) is one of those calls, in the builder's own statement, in an unused wrapper's definition, or done before the
 * builder runs; and `G` is used as a value or read with a computed key only before the builder runs, in a condition,
 * or to keep it as a global the program never names again (other scripts don't read it: model 2). So no call made
 * later finds the cache unset, and cleanup removes the builder and the wrappers nothing reads. Otherwise partial mode:
 * only calls that run after the prelude go, the prelude's stay, so the checks run when the original's did.
 */
export const codeLocks: Pass = {
    name: "code-locks",
    description: "Remove cached environment checks: all their calls when their checks touch only their own objects, else the calls made after the prelude",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.guest.broken !== undefined) {
            log.info("no usable runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
        const programSurvey = survey(program, matcher, scopes);

        const replacements = new Map<Node, Node>();
        const removals = new Set<Node>();
        const counts = { locks: 0, full: 0, removed: 0, answered: 0, kept: 0 };
        for (const { path, sites } of programSurvey.calls.values()) {
            if (path.length < 2) continue; // a wrapper: inlined by now when its target is a function
            const name = `${runtime.storage}.${path.join(".")}`;
            const definition = definitionOf(runtime, matcher.isStorage, path.slice(0, -1));
            if (typeof definition === "string") continue; // not a code lock's shape at all: say nothing
            const fast = fastPathOf(definition.iife, path.at(-1) as string, scopes);
            if (!fast.ok) {
                log.debug(`${name} is no code lock: ${fast.reason}`, fast.node);
                continue;
            }
            const [probe] = runtime.guest.resolve([{ path, args: [] }]);
            if (probe === undefined || !probe.ok || "nonPrimitive" in probe || !probe.repeatable || !Object.is(probe.value, fast.answer)) {
                log.debug(`${name} looks like a code lock, but in the guest it doesn't answer ${String(fast.answer)} from its cache`, fast.method);
                continue;
            }
            counts.locks++;
            log.debug(`${name} is a code lock: after its first call it answers ${String(fast.answer)} and does nothing else`, fast.method);

            const staleness = sites.map(({ site }) => effects.staleAt(site, path));
            // A discarded call's answer is as good as no call; a used one may answer the cached value only after the prelude.
            const full = sites.map(({ statement, discarded, site }, i): Disposition =>
                staleness[i] !== undefined ? "keep" : statement !== undefined ? "remove" : discarded || effects.runsAfterPrelude(site) ? "answer" : "keep"
            );
            const partial = sites.map(({ statement, site }, i): Disposition =>
                staleness[i] !== undefined || !effects.runsAfterPrelude(site) ? "keep" : statement === undefined ? "answer" : "remove"
            );
            const refusal = fullModeRefusal({ path, sites, full, staleness, fast, builder: definition.statement }, { program, runtime, scopes, matcher, effects, uses: programSurvey });
            if (refusal === undefined) counts.full++;
            else log.debug(`${name}: partial mode, the prelude's calls stay: ${refusal.reason}`, refusal.node);

            const dispositions = refusal === undefined ? full : partial;
            const lock = { removed: 0, answered: 0, kept: 0 };
            for (const [i, { call, statement }] of sites.entries()) {
                const disposition = dispositions[i];
                if (disposition === "keep") {
                    lock.kept++;
                    const stale = staleness[i];
                    log.debug(`kept: ${stale?.reason ?? "the call runs in the prelude, which makes the first call"}`, stale?.node ?? call);
                } else if (disposition === "answer") {
                    replacements.set(call, valueToNode(fast.answer, call));
                    lock.answered++;
                } else {
                    removals.add(statement as Statement);
                    lock.removed++;
                }
            }
            const mode = refusal === undefined ? "full" : `partial: ${refusal.reason}`;
            log.info(`${name} (${mode}): removed ${lock.removed} call(s), answered ${lock.answered}, kept ${lock.kept}`, definition.statement);
            counts.removed += lock.removed;
            counts.answered += lock.answered;
            counts.kept += lock.kept;
        }

        rewriteCalls(program, replacements, removals);
        log.info(`${counts.locks} code lock(s), ${counts.full} removed in full: removed ${counts.removed} call(s), answered ${counts.answered}, kept ${counts.kept}`);
        return { changed: counts.removed + counts.answered, bindingsChanged: false, stats: counts };
    },
};
