import type { CallExpression, Expression, Node, Program, Statement } from "../../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../../core/ast.js";
import { sameReference } from "../../core/equal.js";
import { evaluate } from "../../core/evaluate.js";
import type { Value } from "../../core/evaluate.js";
import { printStatement } from "../../core/print.js";
import type { ScopeInfo } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import type { BuiltIdentities, LoggedCall, OwnersChange, PropertyPath } from "./guest.js";
import { Guest, pathName } from "./guest.js";
import type { Alias, CallAlias, Wrapper } from "./model.js";
import { RUNTIME } from "./model.js";

/** Per-statement deadlines. The runtime's own statements can be heavy (a decoder may XOR a >1 MB string). */
const RUNTIME_STATEMENT_TIMEOUT_MS = 15_000;
const OTHER_STATEMENT_TIMEOUT_MS = 500;
const TOTAL_BUDGET_MS = 60_000;

const isPrimitive = (value: unknown): value is Value => value === null || value === undefined || typeof value === "string" || typeof value === "number" || typeof value === "boolean";

/**
 * The statements that run at the top, and the node whose scope declares them: a lone top-level IIFE (after any
 * directives), or the program. The IIFE may be a function expression or a block-bodied arrow, called directly or
 * with `.call(this)`, under unary operators (`!function () {...}()`).
 */
const rootBody = (program: Program): { body: Statement[]; owner: Node } => {
    const statements = program.body.filter(
        (statement) => statement.type !== "EmptyStatement" && !(statement.type === "ExpressionStatement" && "directive" in statement && typeof statement.directive === "string")
    );
    const [only] = statements;
    let call: Node | undefined = statements.length === 1 && only?.type === "ExpressionStatement" ? only.expression : undefined;
    while (call?.type === "UnaryExpression") call = call.argument;
    if (call?.type !== "CallExpression") return { body: program.body, owner: program };
    let fn: Node = call.callee;
    // `(function () {...}).call(this)`: the same run, `this` being the script's own.
    if (fn.type === "MemberExpression" && propertyKey(fn) === "call" && call.arguments.length <= 1 && call.arguments.every((arg) => arg.type === "ThisExpression")) fn = fn.object;
    const block = (fn.type === "FunctionExpression" || fn.type === "ArrowFunctionExpression") && !fn.async && !fn.generator && fn.body?.type === "BlockStatement" ? fn.body : undefined;
    return block === undefined ? { body: program.body, owner: program } : { body: block.body, owner: fn };
};

/** `G[k] = ...` / `G.k = ...` as a statement: the storage identifier, the key and the value. */
const storageAssignment = (statement: Statement): { object: string; key: string; right: Expression } | undefined => {
    if (statement.type !== "ExpressionStatement") return undefined;
    const e = statement.expression;
    if (e.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "MemberExpression" || e.left.object.type !== "Identifier") return undefined;
    const key = propertyKey(e.left);
    return key === undefined ? undefined : { object: e.left.object.name, key, right: e.right };
};

/**
 * How a call changed the owners (builtins, the global object), judged against what jscrambler's setup function does:
 * every property they had is unchanged, and every new one is an alias (on its owner it reads the same as a property
 * the owner already had, getters included) or a global. New globals (alias holders, accessors forwarding to host
 * properties the guest lacks) go with the setup call, so cleanup removes it only while the program doesn't name them
 * (`RuntimeModel.setupGlobals`). Any other effect makes the call something cleanup must keep: `unexpected` names the
 * first.
 */
const setupEffects = (guest: Guest, change: OwnersChange): { unexpected: string | undefined; globals: string[] } => {
    const [changed] = change.changed;
    if (changed !== undefined) return { unexpected: `${pathName(guest.owners[changed[0]] ?? [])}.${changed[1]} changed`, globals: [] };
    const globals: string[] = [];
    const added = change.added.find(([index, name]) => {
        const owner = guest.owners[index];
        const was = change.namesBefore[index];
        if (owner === undefined || was === undefined) return true;
        if (index !== 0) return guest.aliasOf(owner, name, [...was]) === undefined;
        globals.push(name);
        return false;
    });
    return { unexpected: added === undefined ? undefined : `${pathName(guest.owners[added[0]] ?? [])}.${added[1]} added`, globals };
};

/** A static member chain rooted at the storage identifier, as its path on the storage object. */
const storagePath = (node: Node, storage: string): PropertyPath | undefined => {
    const path = memberPath(node);
    return path !== undefined && path.root.type === "Identifier" && path.root.name === storage ? path.keys : undefined;
};

/** `function () { return typeof T === "function" ? T.apply(O, arguments) : T; }` with T on the storage object. */
const wrapperOf = (fn: Expression, storage: string): Omit<Wrapper, "key" | "definition"> | undefined => {
    if (fn.type !== "FunctionExpression" || fn.body === null || fn.body.body.length !== 1) return undefined;
    const ret = fn.body.body[0];
    if (ret?.type !== "ReturnStatement" || ret.argument?.type !== "ConditionalExpression") return undefined;
    const { test, consequent, alternate } = ret.argument;
    if (test.type !== "BinaryExpression" || (test.operator !== "===" && test.operator !== "==")) return undefined;
    const typeofSide = [test.left, test.right].find((side) => side.type === "UnaryExpression" && side.operator === "typeof");
    if (typeofSide?.type !== "UnaryExpression" || consequent.type !== "CallExpression") return undefined;
    const target = storagePath(alternate, storage);
    if (target === undefined || !sameReference(typeofSide.argument, alternate)) return undefined;
    const callee = consequent.callee;
    if (callee.type !== "MemberExpression" || propertyKey(callee) !== "apply" || !sameReference(callee.object, alternate)) return undefined;
    const [receiver, args] = consequent.arguments;
    if (receiver === undefined || receiver.type === "SpreadElement" || args?.type !== "Identifier" || args.name !== "arguments") return undefined;
    return { target, receiver: storagePath(receiver, storage) };
};

/**
 * The runtime's storage object: jscrambler declares it as an empty root function (`function G() {}`) and fills it
 * through root assignments (`G.k = ...`, `G[123] = ...`), wrappers among them. Of the names root statements assign
 * properties of, the one with most evidence: that declaration first, then the most wrapper definitions, then the
 * most assignments. Never the first by source order alone: when the best two tie, there is none.
 */
const storageOf = (body: readonly Statement[]): string | { ambiguous: string[] } | undefined => {
    const evidence = new Map<string, { declared: number; wrappers: number; assignments: number }>();
    for (const statement of body) {
        const assignment = storageAssignment(statement);
        if (assignment === undefined) continue;
        const entry = evidence.get(assignment.object) ?? { declared: 0, wrappers: 0, assignments: 0 };
        entry.assignments++;
        if (wrapperOf(assignment.right, assignment.object) !== undefined) entry.wrappers++;
        evidence.set(assignment.object, entry);
    }
    for (const statement of body) {
        const entry = statement.type === "FunctionDeclaration" && statement.id !== null ? evidence.get(statement.id.name) : undefined;
        if (entry !== undefined && statement.type === "FunctionDeclaration" && statement.params.length === 0 && statement.body?.body.length === 0 && !statement.async && !statement.generator)
            entry.declared = 1;
    }
    const ranked = [...evidence].toSorted(([, a], [, b]) => b.declared - a.declared || b.wrappers - a.wrappers || b.assignments - a.assignments);
    const [best, second] = ranked;
    if (best === undefined) return undefined;
    const same = (a: typeof best, b: typeof best): boolean => a[1].declared === b[1].declared && a[1].wrappers === b[1].wrappers && a[1].assignments === b[1].assignments;
    return second !== undefined && same(best, second) ? { ambiguous: [best[0], second[0]] } : best[0];
};

/** Free names a statement needs from outside itself, split by whether the sandbox can provide them. */
const freeNames = (statement: Statement, scopes: ScopeInfo, rootScopeNodes: ReadonlySet<Node>): string[] => {
    const names = new Set<string>();
    traverse(statement, {
        Identifier: (path) => {
            const reference = scopes.referenceOf(path.node);
            if (reference === undefined) return;
            const variable = reference.resolved;
            if (variable === null) names.add(path.node.name);
            else if (rootScopeNodes.has(variable.scope.block as unknown as Node)) names.add(path.node.name);
        },
    });
    return [...names];
};

/**
 * Root bindings a statement reads while it runs: references outside nested function bodies (those only run when
 * called), not counting the names it declares. Through any of them a real run of the statement can reach the runtime.
 */
const evaluatedRootNames = (statement: Statement, scopes: ScopeInfo, rootScopeNodes: ReadonlySet<Node>): string[] => {
    const names = new Set<string>();
    traverse(statement, {
        enter(path) {
            if (path.node !== statement && isFunctionNode(path.node)) path.skip();
        },
        Identifier: (path) => {
            const reference = scopes.referenceOf(path.node);
            if (reference === undefined || reference.isWriteOnly()) return;
            const variable = reference.resolved;
            if (variable === null || rootScopeNodes.has(variable.scope.block as unknown as Node)) names.add(path.node.name);
        },
    });
    return [...names];
};

/**
 * Statements that are the obfuscator runtime setting itself up: assignments to the storage object
 * (`G.k = ...`, `G[1] = ...`, also chained like `G[1].x = G`), and calls of root functions given storage values
 * (`setup(G.R_)`).
 */
const isRuntimeStatement = (statement: Statement, storage: string, declared: ReadonlySet<string>): boolean => {
    if (statement.type !== "ExpressionStatement") return false;
    const e = statement.expression;
    if (e.type === "AssignmentExpression") {
        let target: Node = e.left;
        while (target.type === "MemberExpression") target = target.object;
        return target.type === "Identifier" && target.name === storage;
    }
    if (e.type === "CallExpression" && e.callee.type === "Identifier" && declared.has(e.callee.name)) {
        return e.arguments.some((arg) => storagePath(arg, storage) !== undefined);
    }
    return false;
};

/** The RUNTIME facts keyed by root statement, as emulate builds them. */
interface StatementFacts {
    readonly executed: Set<Node>;
    readonly pure: Set<Node>;
    readonly setup: Set<Node>;
    readonly built: Map<Node, BuiltIdentities>;
}

/**
 * Carry statement facts over to the statements that replaced their statements (see `Facts.replaced`), dropping them
 * from the originals that left. Running to completion carries over to every replacement when every original ran:
 * together the replacements did what the originals did, so each of them ran to completion. The others describe one
 * statement's whole effect (none outside the storage object, defining the aliases, what it stored): split over
 * several statements they say nothing about each part, so they carry over only from one statement to one.
 */
const carryStatementFacts = (statementFacts: StatementFacts, originals: readonly Node[], replacements: readonly Node[]): void => {
    const { executed, pure, setup, built } = statementFacts;
    const left = originals.filter((original) => !replacements.includes(original));
    if (originals.length > 0 && originals.every((original) => executed.has(original))) {
        for (const replacement of replacements) executed.add(replacement);
        for (const original of left) executed.delete(original);
    }
    const [original] = originals;
    const [replacement] = replacements;
    if (originals.length !== 1 || replacements.length !== 1 || original === undefined || replacement === undefined || original === replacement) return;
    for (const set of [pure, setup]) {
        if (set.delete(original)) set.add(replacement);
    }
    const identities = built.get(original);
    if (identities !== undefined && built.delete(original)) built.set(replacement, identities);
};

/**
 * Run the obfuscator's runtime prelude inside the QuickJS sandbox and record what it does.
 *
 * Runs right after `unflatten` and before anything that rewrites the runtime, so the sandbox sees the runtime
 * exactly as the obfuscator wrote it (only restructured). Produces the RUNTIME fact: the storage object, which of
 * its keys hold the global object, builtin aliases, wrapper functions, and the results of every wrapper call the
 * prelude made (those drive the string decoder's shuffle and decide the opaque predicates around them).
 * Changes no code itself.
 */
export const emulate: Pass = {
    name: "emulate",
    description: "Run the obfuscator's runtime prelude in a sandbox and record its results",
    async run({ program, log, scope, facts }: PassContext): Promise<PassResult> {
        const { body, owner: root } = rootBody(program);
        const candidate = storageOf(body);
        if (typeof candidate !== "string") {
            log.info(
                candidate === undefined ? "no runtime storage object found, nothing to emulate" : `no runtime storage object: ${candidate.ambiguous.join(" and ")} look alike, nothing to emulate`
            );
            return { changed: 0 };
        }
        const storage = candidate;
        log.info(`storage object: ${storage}`);

        const scopes = scope();
        const rootScopes = new Set<Node>([program]);
        if (root !== program) rootScopes.add(root);

        const guest = await Guest.create();
        facts.onDispose(() => guest.dispose());
        // Globals the guest has: builtins and the host model, plus whatever earlier statements define (the setup
        // function's global aliases), so read again (when next needed) after each statement that ran.
        let available: Set<string> | undefined;
        const before = guest.snapshot();

        // Hoisting: every root function exists before the first statement runs.
        const declared = new Set<string>();
        const functions = new Set<string>();
        for (const statement of body) {
            if (statement.type !== "FunctionDeclaration" || statement.id === null) continue;
            declared.add(statement.id.name);
            functions.add(statement.id.name);
            const result = guest.run(printStatement(statement), RUNTIME_STATEMENT_TIMEOUT_MS);
            if (!result.ok) log.debug(`declaring ${statement.id.name} failed: ${result.error}`, statement);
        }
        for (const statement of body) {
            if (statement.type === "VariableDeclaration") for (const d of statement.declarations) if (d.id.type === "Identifier") declared.add(d.id.name);
        }
        let bound = guest.bind(storage);

        const wrappers = new Map<string, Wrapper>();
        const callResults = new Map<Node, Value>();
        const unmappedCalls: LoggedCall[] = [];
        const siteCalls = new Map<Node, LoggedCall>();
        const preludeCalls: LoggedCall[] = [];
        const built = new Map<Node, BuiltIdentities>();
        const pure = new Set<Node>();
        const setup = new Set<Node>();
        const executed = new Set<Node>();
        const setupKeys = new Set<string>();
        const setupGlobals = new Set<string>();
        /** For log lines: the setup call that installed each storage key, and after which each builtin property first appeared. */
        const installedBy = new Map<string, Statement>();
        const appearedAfter = new Map<string, Statement>();
        let lastSnapshot = before;
        const counts = { executed: 0, skipped: 0, failed: 0, mapped: 0 };
        const started = Date.now();
        /** The first statement after which the guest may no longer match a real run: results stop being recorded. */
        let diverged: Statement | undefined;
        /** The guest's owner baseline is the state before the next statement (only running statements change owners). */
        let marked = false;

        for (const statement of body) {
            if (statement.type === "FunctionDeclaration") continue;
            if (Date.now() - started > TOTAL_BUDGET_MS) {
                log.warn(`emulation budget of ${TOTAL_BUDGET_MS}ms used up, stopping`, statement);
                break;
            }
            // The runtime's own statements always run: what they need (prototype getters, aliases from the setup
            // function) only exists once earlier ones have run, so free-name analysis can't judge them. Anything
            // else only runs when every free name is a builtin or a root declaration.
            const isRuntime = isRuntimeStatement(statement, storage, declared);
            if (!isRuntime) {
                const free = freeNames(statement, scopes, rootScopes);
                available ??= new Set(guest.globals());
                const globals = available;
                const unknown = free.filter((name) => !globals.has(name) && !declared.has(name));
                if (unknown.length > 0) {
                    counts.skipped++;
                    log.debug(`skipped: needs ${unknown.slice(0, 5).join(", ")}`, statement);
                    // In a real run this statement could call into the runtime; from here on the guest may differ.
                    if (diverged === undefined && evaluatedRootNames(statement, scopes, rootScopes).some((name) => name === storage || declared.has(name))) diverged = statement;
                    continue;
                }
            }

            const isCall = statement.type === "ExpressionStatement" && statement.expression.type === "CallExpression";
            if (bound && !marked) marked = guest.markOwners();
            const tracked: boolean = bound && marked;
            // What a setup call installs on the storage object: its getters (call aliases, probed or not).
            const callablesBefore = bound && isCall ? new Set(guest.ownCallables()) : undefined;
            const result = guest.run(printStatement(statement), isRuntime ? RUNTIME_STATEMENT_TIMEOUT_MS : OTHER_STATEMENT_TIMEOUT_MS);
            marked = false;
            if (!result.ok) {
                counts.failed++;
                log.debug(`failed: ${result.error}`, statement);
                // Calls it made before failing moved the runtime's state in a way no real run does; so may what it
                // wrote before failing (or before its deadline), if it can reach the runtime at all.
                const madeCalls = guest.takeCalls();
                if (madeCalls.length > 0) {
                    log.debug(`it made ${madeCalls.length} runtime call(s) first: ${madeCalls.map((c) => `${c.key}(${c.args.map((a) => JSON.stringify(a)).join(", ")})`).join(" ")}`, statement);
                    unmappedCalls.push(...madeCalls);
                }
                if (diverged === undefined && (madeCalls.length > 0 || evaluatedRootNames(statement, scopes, rootScopes).some((name) => name === storage || declared.has(name)))) diverged = statement;
                continue;
            }
            counts.executed++;
            executed.add(statement);
            available = undefined;
            if (!bound) bound = guest.bind(storage);

            // Effects outside the storage object decide what cleanup may remove later.
            const change: OwnersChange | undefined = tracked ? guest.ownersSince() : undefined;
            marked = change !== undefined;
            if (change !== undefined) {
                if (change.same) pure.add(statement);
                const installs = !change.same || change.accessorsAfter > change.accessorsBefore;
                const effects = isCall && installs ? setupEffects(guest, change) : undefined;
                if (effects?.unexpected !== undefined) log.debug(`not a setup call: ${effects.unexpected}`, statement);
                if (effects !== undefined && effects.unexpected === undefined) {
                    setup.add(statement);
                    for (const name of effects.globals) setupGlobals.add(name);
                    const installed = (guest.ownCallables() ?? []).filter((key) => callablesBefore?.has(key) === false);
                    for (const key of installed) {
                        setupKeys.add(key);
                        installedBy.set(key, statement);
                    }
                    if (log.debugging) {
                        const now = guest.snapshot();
                        for (const [index, names] of now.entries()) {
                            const was = new Set(lastSnapshot[index] ?? []);
                            for (const name of names) if (!was.has(name)) appearedAfter.set(`${index}:${name}`, statement);
                        }
                        lastSnapshot = now;
                    }
                    log.debug(`setup call: defines aliases${installed.length > 0 ? `, installs ${storage}.${installed.join(`, ${storage}.`)}` : ""}`, statement);
                }
            }

            const assignment = storageAssignment(statement);
            if (assignment !== undefined && assignment.object === storage) {
                const found = wrapperOf(assignment.right, storage);
                if (found !== undefined && guest.record(assignment.key, found.target)) {
                    wrappers.set(assignment.key, { key: assignment.key, ...found, definition: statement });
                    log.debug(`wrapper ${assignment.key} -> ${storage}.${found.target.join(".")}`, statement);
                }
                // A builder's result (`G.k = (function () {...})()`): what it stored, and its methods, as they are now.
                const { right } = assignment;
                if (right.type === "CallExpression" && right.arguments.length === 0 && (right.callee.type === "FunctionExpression" || right.callee.type === "ArrowFunctionExpression")) {
                    const identities = guest.built([assignment.key]);
                    if (identities !== undefined) built.set(statement, identities);
                }
            }

            // Map the wrapper calls this statement made back to their call sites, in completion order (post-order).
            // Sites inside nested functions don't count: those run again later, in another runtime state.
            const logged = guest.takeCalls();
            if (logged.length === 0) continue;
            if (diverged !== undefined) {
                unmappedCalls.push(...logged);
                continue;
            }
            preludeCalls.push(...logged);
            const sites: CallExpression[] = [];
            traverse(statement, {
                enter(path) {
                    if (path.node !== statement && isFunctionNode(path.node)) path.skip();
                },
                CallExpression: {
                    exit: (path) => {
                        const callee = path.node.callee;
                        if (callee.type !== "MemberExpression" || callee.object.type !== "Identifier" || callee.object.name !== storage) return;
                        const key = propertyKey(callee);
                        if (key !== undefined && wrappers.has(key)) sites.push(path.node);
                    },
                },
            });
            const lineUp =
                sites.length === logged.length &&
                sites.every((site, i) => {
                    const call = logged[i];
                    if (call === undefined || propertyKey(site.callee as Parameters<typeof propertyKey>[0]) !== call.key || site.arguments.length !== call.args.length) return false;
                    return site.arguments.every((arg, j) => {
                        const v = evaluate(arg);
                        return v.ok && Object.is(v.value, call.args[j]);
                    });
                });
            if (!lineUp) {
                log.debug(`${logged.length} wrapper call(s) ran but don't line up with the ${sites.length} call site(s); results not used`, statement);
                unmappedCalls.push(...logged);
                continue;
            }
            for (const [i, site] of sites.entries()) {
                const call = logged[i];
                if (call === undefined) continue;
                siteCalls.set(site, call);
                if (!isPrimitive(call.result)) continue;
                callResults.set(site, call.result);
                counts.mapped++;
                log.debug(`call result ${JSON.stringify(call.result)}`, site);
            }
        }
        if (diverged !== undefined) log.info("the emulated runtime may differ from a real run from here on; later call results weren't recorded", diverged);

        // Aliases: properties added to builtins whose value equals an existing property of the same owner.
        const after = guest.snapshot();
        const aliases: Alias[] = [];
        for (const [index, owner] of guest.owners.entries()) {
            const was = before[index] ?? [];
            const existed = new Set(was);
            for (const alias of after[index] ?? []) {
                if (existed.has(alias)) continue;
                const original = guest.aliasOf(owner, alias, was);
                if (original === undefined) continue;
                aliases.push({ owner, alias, original });
                log.debug(`alias ${pathName(owner)}.${alias} = ${pathName(owner)}.${original}`, appearedAfter.get(`${index}:${alias}`));
            }
        }

        // Call aliases: getters on the storage object returning a function whose zero-argument call gives a builtin.
        const callAliases = new Map<string, CallAlias>();
        if (bound) {
            for (const found of guest.callAliases()) {
                if (found.style === undefined) {
                    log.debug(
                        `call alias ${storage}.${found.key}(...) hands out ${pathName(found.owner)}.${found.original}, but passes arguments on in neither known way; left`,
                        installedBy.get(found.key)
                    );
                    continue;
                }
                callAliases.set(found.key, { key: found.key, owner: found.owner, original: found.original, style: found.style });
                const shape = found.style === "method" ? `x.${found.original}(...)` : `${pathName(found.owner)}.${found.original}(...)`;
                log.debug(`call alias ${storage}.${found.key}(...) = ${shape}`, installedBy.get(found.key));
            }
        }
        // Global reads: setup getters whose zero-argument call gives a global property the global object lacks (the
        // random names the code locks probe with `typeof`).
        const globalReads = new Map<string, string>();
        if (bound) {
            for (const { key, name } of guest.globalReads()) {
                if (callAliases.has(key) || !setupKeys.has(key)) continue;
                globalReads.set(key, name);
                log.debug(`global read ${storage}.${key}() = globalThis.${name}`, installedBy.get(key));
            }
        }
        // Host aliases: setup globals forwarding to a global property the guest lacks (`document`, `console`).
        const hostAliases = new Map<string, string>();
        if (setupGlobals.size > 0) {
            for (const { alias, name } of guest.hostAliases([...setupGlobals])) {
                hostAliases.set(alias, name);
                log.debug(`host alias ${alias} = globalThis.${name}`);
            }
        }
        const globalKeys = new Set(bound ? guest.globalKeys() : []);

        log.info(
            `ran ${counts.executed} statement(s), skipped ${counts.skipped}, failed ${counts.failed}; wrappers ${wrappers.size}, aliases ${aliases.length}, call aliases ${callAliases.size}, global keys [${[...globalKeys].join(", ")}], call results ${counts.mapped}`
        );
        facts.set(RUNTIME, {
            storage,
            root,
            globalKeys,
            aliases,
            callAliases,
            globalReads,
            hostAliases,
            wrappers,
            callResults,
            unmappedCalls,
            siteCalls,
            preludeCalls,
            built,
            pure,
            setup,
            setupKeys,
            setupGlobals,
            executed,
            guest,
        });
        facts.onReplace((originals, replacements) => carryStatementFacts({ executed, pure, setup, built }, originals, replacements));
        return {
            changed: 0,
            stats: { ...counts, wrappers: wrappers.size, aliases: aliases.length, callAliases: callAliases.size },
        };
    },
};
