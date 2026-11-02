import type { CallExpression, Expression, Node, Program, Statement } from "../../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../../core/ast.js";
import { sameReference } from "../../core/equal.js";
import { evaluate } from "../../core/evaluate.js";
import type { Value } from "../../core/evaluate.js";
import { pushAll } from "../../core/list.js";
import type { PassLog } from "../../core/log.js";
import { printStatement } from "../../core/print.js";
import type { PrintedFunctions } from "../../core/print.js";
import { DEFAULT_LIMITS } from "../../core/sandbox.js";
import type { RunResult } from "../../core/sandbox.js";
import type { ScopeInfo } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import type { AccessorFunctions, BuiltIdentities, InstalledState, LoggedCall, OwnersChange, PropertyPath, RunRecord } from "./guest.js";
import { Guest, pathName } from "./guest.js";
import type { AddedNames, Installed, ProofFailure } from "./getters.js";
import { GetterProofs } from "./getters.js";
import type { Alias, CallAlias, Wrapper } from "./model.js";
import { RUNTIME } from "./model.js";

/** Runtime statements can be heavy (a decoder may XOR a >1 MB string). */
const RUNTIME_STATEMENT_TIMEOUT_MS = 15_000;
const OTHER_STATEMENT_TIMEOUT_MS = 500;
/** For the statements and the alias probes after them; when it runs out, the rest is left unknown (partial output). */
const TOTAL_BUDGET_MS = 60_000;

const isPrimitive = (value: unknown): value is Value => value === null || value === undefined || typeof value === "string" || typeof value === "number" || typeof value === "boolean";

/**
 * A lone top-level IIFE (after directives; function or block-bodied arrow, direct or `.call(this)`, under unary
 * operators), or the program.
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
    if (fn.type === "MemberExpression" && propertyKey(fn) === "call" && call.arguments.length <= 1 && call.arguments.every((arg) => arg.type === "ThisExpression")) fn = fn.object;
    const block = (fn.type === "FunctionExpression" || fn.type === "ArrowFunctionExpression") && !fn.async && !fn.generator && fn.body?.type === "BlockStatement" ? fn.body : undefined;
    return block === undefined ? { body: program.body, owner: program } : { body: block.body, owner: fn };
};

/** Also `(X = G).k = ...`, which stores `G` somewhere first (keeping the runtime as a global): the member is still `G`'s. */
const storageAssignment = (statement: Statement): { object: string; key: string; right: Expression } | undefined => {
    if (statement.type !== "ExpressionStatement") return undefined;
    const e = statement.expression;
    if (e.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "MemberExpression") return undefined;
    const object = e.left.object.type === "AssignmentExpression" && e.left.object.operator === "=" ? e.left.object.right : e.left.object;
    const key = object.type === "Identifier" ? propertyKey(e.left) : undefined;
    return key === undefined || object.type !== "Identifier" ? undefined : { object: object.name, key, right: e.right };
};

/**
 * Judged against what the setup function does: every existing property unchanged, every new one an alias (reads the
 * same as an existing property, getters included) or a global. New globals go with the setup call, so cleanup removes
 * it only while the program doesn't name them (`RuntimeModel.setupGlobals`). `unexpected` names the first other effect.
 */
const setupEffects = (guest: Guest, change: OwnersChange, timeoutMs: number): { unexpected: string | undefined; globals: string[] } => {
    const [changed] = change.changed;
    if (changed !== undefined) return { unexpected: `${pathName(guest.owners[changed[0]] ?? [])}.${changed[1]} changed`, globals: [] };
    const globals: string[] = [];
    let why: string | undefined;
    const added = change.added.find(([index, name]) => {
        const owner = guest.owners[index];
        const was = change.namesBefore[index];
        if (owner === undefined || was === undefined) return true;
        if (index === 0) {
            globals.push(name);
            return false;
        }
        const alias = guest.aliasOf(owner, name, was, timeoutMs);
        if (alias !== undefined && "env" in alias) why = `reading it ${alias.env}`;
        return alias === undefined || "env" in alias;
    });
    return { unexpected: added === undefined ? undefined : `${pathName(guest.owners[added[0]] ?? [])}.${added[1]} added${why === undefined ? "" : ` (${why})`}`, globals };
};

const storagePath = (node: Node, storage: string): PropertyPath | undefined => {
    const path = memberPath(node);
    return path !== undefined && path.root.type === "Identifier" && path.root.name === storage ? path.keys : undefined;
};

/** An accessor's place: an owner's path, or `null` for the storage object. */
const installKey = (path: PropertyPath | null, key: string): string => JSON.stringify([path, key]);

/** `function () { return typeof T === "function" ? T.apply(O, arguments) : T; }` */
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
 * The root-assigned name with most evidence: an empty root function declaration (`function G() {}`), then most wrapper
 * definitions, then most assignments. Never by source order alone: when the best two tie, there is none.
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
 * Root bindings read outside nested function bodies, excluding its own declarations: through any of them a real run
 * can reach the runtime.
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

/** Storage assignments (also chained, `G[1].x = G`) and calls of root functions given storage values (`setup(G.R_)`). */
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

interface StatementFacts {
    readonly executed: Set<Node>;
    readonly pure: Set<Node>;
    readonly setup: Set<Node>;
    readonly built: Map<Node, BuiltIdentities>;
}

/**
 * See `Facts.replaced`. Running to completion carries to every replacement when every original ran: together they did
 * what the originals did. The other facts describe one statement's whole effect, so they carry only one-to-one.
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
 * The statement as the guest runs it, under its own file name: a function it makes is found in the printed text by
 * where it starts (`GetterProofs`), without printing it again.
 */
const fileFor = (files: PrintedFunctions[], statement: Statement): { source: string; file: string } => {
    const printed = printStatement(statement);
    return { source: printed.source, file: `program-${files.push(printed) - 1}.js` };
};

/** Declares the root functions in the guest. Returns every root declared name (functions and `var`s). */
const declareRoot = (guest: Guest, body: readonly Statement[], log: PassLog, files: PrintedFunctions[]): Set<string> => {
    const declared = new Set<string>();
    for (const statement of body) {
        if (statement.type !== "FunctionDeclaration" || statement.id === null) continue;
        declared.add(statement.id.name);
        const { source, file } = fileFor(files, statement);
        const result = guest.run(source, RUNTIME_STATEMENT_TIMEOUT_MS, file);
        if (!result.ok) log.debug(`declaring ${statement.id.name} failed: ${result.error}`, statement);
    }
    for (const statement of body) {
        if (statement.type === "VariableDeclaration") for (const d of statement.declarations) if (d.id.type === "Identifier") declared.add(d.id.name);
    }
    return declared;
};

/** One statement's run in the guest. */
interface StatementRun {
    readonly isCall: boolean;
    readonly source: string;
    readonly result: RunResult & { readonly disagreed?: true };
    /** `undefined`: the guest didn't tell which runtime calls the run made. */
    readonly taken: RunRecord | undefined;
    /** The storage object's callables before the run (calls only, once bound). */
    readonly callablesBefore: ReadonlySet<string> | undefined;
}

/** How a statement went: skipped (it needs a name the guest lacks), failed, or ran to completion. */
type Step =
    | { readonly kind: "skipped" }
    | { readonly kind: "failed"; readonly taken: RunRecord | undefined }
    | {
          readonly kind: "ran";
          readonly taken: RunRecord | undefined;
          /** It read the environment or the second lane saw it otherwise: what it did is unknown. */
          readonly unsure: boolean;
          /** Probing the aliases it set up made runtime calls (or didn't tell). */
          readonly probeCalls: boolean;
      };

/**
 * Whether the guest may no longer match a real run after `step` (then results stop being recorded); `reachesRuntime`:
 * whether a real run of the statement can reach the runtime. A run whose calls the guest didn't tell made unknown calls:
 * whatever they did to the runtime, no recorded call can be trusted after them.
 */
const diverges = (step: Step, reachesRuntime: () => boolean): boolean => {
    switch (step.kind) {
        // A real run of it could call into the runtime.
        case "skipped":
            return reachesRuntime();
        // Calls (and, if it can reach the runtime, writes) made before failing moved state as no real run does.
        case "failed":
            return step.taken === undefined || step.taken.calls.length > 0 || reachesRuntime();
        // A run that read the environment may write otherwise in a real run; the probes' calls are none a real run makes.
        case "ran":
            return step.taken === undefined || step.probeCalls || (step.taken.env !== undefined && reachesRuntime());
    }
};

interface EmulationScope {
    readonly guest: Guest;
    readonly log: PassLog;
    readonly storage: string;
    readonly scopes: ScopeInfo;
    readonly rootScopes: ReadonlySet<Node>;
    readonly declared: ReadonlySet<string>;
    /** The owners' names before the root functions were declared. */
    readonly before: readonly (readonly string[])[];
    /** What the guest ran, by file index (`fileFor`). */
    readonly files: PrintedFunctions[];
}

/** Runs the root statements in the guest, one by one, and collects what the RUNTIME fact records about them. */
class Emulation {
    readonly #guest: Guest;
    readonly #log: PassLog;
    readonly #storage: string;
    readonly #scopes: ScopeInfo;
    readonly #rootScopes: ReadonlySet<Node>;
    readonly #declared: ReadonlySet<string>;
    readonly #before: readonly (readonly string[])[];
    /** For the statements and the probes after them (`TOTAL_BUDGET_MS`). */
    readonly #started = Date.now();
    #outOfBudget = false;
    #bound: boolean;
    /** Grows with what earlier statements define (setup aliases): re-read after each statement that ran. */
    #available: Set<string> | undefined;
    /** From here on the guest may no longer match a real run: results stop being recorded. */
    #diverged: Statement | undefined;
    #lastSnapshot: readonly (readonly string[])[];
    readonly #installedBy = new Map<string, Statement>();
    readonly #appearedAfter = new Map<string, Statement>();
    readonly #files: PrintedFunctions[];
    /** Arguments of root calls that held the global object right before their statement ran. */
    readonly #globalArgs = new Set<Node>();
    /** Accessors setup calls installed, as each call left them (`installKey`). */
    readonly #installs = new Map<string, Installed>();
    /** Per setup call: what the program had added to builtins before it (`ProofContext.added`). */
    readonly #addedBefore = new Map<Statement, AddedNames>();
    /** Accessors as the statements left them, before the probes after them run getters (`#accessorsNow`). */
    #now: Map<string, AccessorFunctions | null> | undefined;
    #proofs: GetterProofs | undefined;

    readonly counts = { executed: 0, skipped: 0, failed: 0, tainted: 0, disagreed: 0, mapped: 0 };
    readonly wrappers = new Map<string, Wrapper>();
    readonly callResults = new Map<Node, Value>();
    readonly unmappedCalls: LoggedCall[] = [];
    readonly siteCalls = new Map<Node, LoggedCall>();
    readonly preludeCalls: LoggedCall[] = [];
    readonly built = new Map<Node, BuiltIdentities>();
    readonly pure = new Set<Node>();
    readonly setup = new Set<Node>();
    readonly executed = new Set<Node>();
    readonly setupKeys = new Set<string>();
    readonly setupGlobals = new Set<string>();
    /** Owner aliases whose getter isn't proven to stand for the builtin: not rewritten, so the setup call stays with them. */
    readonly unprovenAliases = new Set<string>();

    constructor({ guest, log, storage, scopes, rootScopes, declared, before, files }: EmulationScope) {
        this.#files = files;
        this.#guest = guest;
        this.#log = log;
        this.#storage = storage;
        this.#scopes = scopes;
        this.#rootScopes = rootScopes;
        this.#declared = declared;
        this.#before = before;
        this.#lastSnapshot = before;
        this.#bound = guest.bind(storage);
    }

    #budgetLeft(): number {
        return TOTAL_BUDGET_MS - (Date.now() - this.#started);
    }

    /** A guest call's deadline within what is left of the budget. */
    #within(timeoutMs: number): number {
        return Math.max(1, Math.min(timeoutMs, this.#budgetLeft()));
    }

    runStatements(body: readonly Statement[]): void {
        for (const statement of body) {
            if (statement.type === "FunctionDeclaration") continue;
            if (this.#budgetLeft() <= 0) {
                this.#log.warn(`emulation budget of ${TOTAL_BUDGET_MS}ms used up, stopping`, statement);
                break;
            }
            this.#statement(statement);
        }
        if (this.#diverged !== undefined) this.#log.info("the emulated runtime may differ from a real run from here on; later call results weren't recorded", this.#diverged);
    }

    #statement(statement: Statement): void {
        // Runtime statements always run: what they need only exists once earlier ones ran, so free-name analysis
        // can't judge them. Others run only when every free name is a builtin or a root declaration.
        const isRuntime = isRuntimeStatement(statement, this.#storage, this.#declared);
        const missing = isRuntime ? [] : this.#missing(statement);
        let step: Step;
        if (missing.length > 0) {
            this.counts.skipped++;
            this.#log.debug(`skipped: needs ${missing.slice(0, 5).join(", ")}`, statement);
            step = { kind: "skipped" };
        } else step = this.#execute(statement, isRuntime);
        const reachesRuntime = (): boolean => isRuntime || evaluatedRootNames(statement, this.#scopes, this.#rootScopes).some((name) => name === this.#storage || this.#declared.has(name));
        if (this.#diverged === undefined && diverges(step, reachesRuntime)) this.#diverged = statement;
        if (step.kind === "ran" && step.taken !== undefined) this.#mapCalls(statement, step.taken.calls, this.#diverged === undefined && !step.unsure);
    }

    /** Free names neither a guest global nor a root declaration. */
    #missing(statement: Statement): string[] {
        const free = freeNames(statement, this.#scopes, this.#rootScopes);
        this.#available ??= new Set(this.#guest.globals());
        const globals = this.#available;
        return free.filter((name) => !globals.has(name) && !this.#declared.has(name));
    }

    #run(statement: Statement, isRuntime: boolean): StatementRun {
        const isCall = statement.type === "ExpressionStatement" && statement.expression.type === "CallExpression";
        if (this.#bound) this.#noteGlobalArgs(statement);
        if (this.#bound) this.#guest.markOwners();
        const callables = this.#bound && isCall ? this.#guest.ownCallables() : undefined;
        const { source, file } = fileFor(this.#files, statement);
        const result = this.#guest.run(source, this.#within(isRuntime ? RUNTIME_STATEMENT_TIMEOUT_MS : OTHER_STATEMENT_TIMEOUT_MS), file);
        return { isCall, source, result, taken: this.#guest.takeRun(), callablesBefore: callables === undefined ? undefined : new Set(callables) };
    }

    /** For a call of a root function or a function expression (a setup call, maybe): which storage paths it passes hold the global object now. */
    #noteGlobalArgs(statement: Statement): void {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "CallExpression") return;
        const { callee, arguments: args } = statement.expression;
        if (!(callee.type === "Identifier" && this.#declared.has(callee.name)) && callee.type !== "FunctionExpression" && callee.type !== "ArrowFunctionExpression") return;
        const passed = args.flatMap((arg) => {
            const path = storagePath(arg, this.#storage);
            return path === undefined || path.length === 0 ? [] : [{ arg, path }];
        });
        if (passed.length === 0) return;
        const held = this.#guest.holdsGlobal(passed.map(({ path }) => path));
        for (const [i, { arg }] of passed.entries()) if (held?.[i] === true) this.#globalArgs.add(arg);
    }

    /** Runs the statement and records what it did, but its calls (`#mapCalls`, once divergence is decided). */
    #execute(statement: Statement, isRuntime: boolean): Step {
        const log = this.#log;
        const run = this.#run(statement, isRuntime);
        const { source, result, taken } = run;
        if (taken === undefined) log.debug("the guest didn't tell which runtime calls this statement made", statement);
        const env = taken?.env;
        if (env !== undefined) {
            // What it computed (and wrote) may differ in a real run: none of it is used, and its writes count as
            // ones the guest doesn't reflect (not `executed`).
            this.counts.tainted++;
            log.debug(`its run ${env}, which a real run may answer differently: nothing it did in the guest is used`, statement);
        }
        // The second lane (another Math.random seed, the host's globals present) saw it otherwise: what it did is
        // unknown, used as little as a tainted run's. Both lanes go on, and what comes after is kept only where
        // they agree, so nothing needs to stop here.
        const disagreed = result.disagreed === true || taken?.disagreed === true;
        if (disagreed) {
            this.counts.disagreed++;
            log.debug("under another Math.random seed with the host's globals present it ran otherwise: nothing it did in the guest is used", statement);
        }
        if (!result.ok) {
            this.counts.failed++;
            const where = result.at === undefined ? "" : ` at \`${(source.split("\n")[result.at.line - 1] ?? "").slice(Math.max(0, result.at.column - 21), result.at.column + 40).trim()}\``;
            log.debug(`failed: ${result.error}${where}`, statement);
            const calls = taken?.calls ?? [];
            if (calls.length > 0) {
                log.debug(`it made ${calls.length} runtime call(s) first: ${calls.map((c) => `${c.key}(${c.args.map((a) => JSON.stringify(a)).join(", ")})`).join(" ")}`, statement);
                pushAll(this.unmappedCalls, calls);
            }
            return { kind: "failed", taken };
        }
        this.#available = undefined;
        if (!this.#bound) this.#bound = this.#guest.bind(this.#storage);
        if (env === undefined) {
            this.counts.executed++;
            this.executed.add(statement);
        }
        const probeCalls = this.#collectFacts(statement, run);
        return { kind: "ran", taken, unsure: env !== undefined || disagreed, probeCalls };
    }

    /** Facts about a statement that ran: pure, setup call, wrapper, builder. Returns `Step.probeCalls`. */
    #collectFacts(statement: Statement, run: StatementRun): boolean {
        const { taken } = run;
        const change = this.#guest.ownersSince();
        // An effect on a host object (seen by the second lane's stubs) is outside what owners show.
        if (taken?.hostEffect === true) this.#log.debug("with the host's globals present it acts on them: neither pure nor a setup call", statement);
        const probeCalls = change !== undefined && taken?.env === undefined && taken?.hostEffect !== true ? this.#ownerFacts(statement, run, change) : false;
        this.#storageFacts(statement, taken?.env);
        return probeCalls;
    }

    /** Pure statements and setup calls, by what the run changed on the owners. Returns `Step.probeCalls`. */
    #ownerFacts(statement: Statement, { isCall, callablesBefore }: StatementRun, change: OwnersChange): boolean {
        const log = this.#log;
        if (change.same) this.pure.add(statement);
        const installs = !change.same || change.accessorsAfter > change.accessorsBefore;
        if (!isCall || !installs) return false;
        // Before the alias probes run its getters (one could replace itself). Only for a statement that installed
        // accessors: on the storage object, or among the names it added to owners (`entriesOf` marks them "get ...").
        const accessorEntries = change.added.filter(([, , value]) => value.startsWith("get "));
        const state =
            change.accessorsAfter > change.accessorsBefore || accessorEntries.length > 0
                ? this.#guest.installed(accessorEntries.flatMap(([index, key]) => (this.#guest.owners[index] === undefined ? [] : [{ path: this.#guest.owners[index] as PropertyPath, key }])))
                : undefined;
        const effects = setupEffects(this.#guest, change, this.#within(DEFAULT_LIMITS.timeoutMs));
        // Probing the aliases runs the program's getters: calls they made aren't the statement's.
        const probed = this.#guest.takeRun();
        const probeCalls = probed === undefined || probed.calls.length > 0;
        if (probeCalls) {
            log.debug("probing its aliases ran runtime calls a real run doesn't make", statement);
            pushAll(this.unmappedCalls, probed?.calls ?? []);
        }
        if (effects.unexpected !== undefined) {
            log.debug(`not a setup call: ${effects.unexpected}`, statement);
            return probeCalls;
        }
        this.setup.add(statement);
        for (const name of effects.globals) this.setupGlobals.add(name);
        const installed = (this.#guest.ownCallables() ?? []).filter((key) => callablesBefore?.has(key) === false);
        for (const key of installed) {
            this.setupKeys.add(key);
            this.#installedBy.set(key, statement);
        }
        if (state !== undefined) this.#noteInstalled(statement, state, new Set(installed), change);
        if (log.debugging) {
            const now = state?.names ?? this.#guest.snapshot();
            for (const [index, names] of now.entries()) {
                const was = new Set(this.#lastSnapshot[index] ?? []);
                for (const name of names) if (!was.has(name)) this.#appearedAfter.set(`${index}:${name}`, statement);
            }
            this.#lastSnapshot = now;
        }
        const storage = this.#storage;
        log.debug(`setup call: defines aliases${installed.length > 0 ? `, installs ${storage}.${installed.join(`, ${storage}.`)}` : ""}`, statement);
        return probeCalls;
    }

    /**
     * A setup call's accessors (on the storage object, only the keys it installed), and what the program had added to
     * builtins before it: the owners' names now, but the originals and the ones it added.
     */
    #noteInstalled(statement: Statement, state: InstalledState, installed: ReadonlySet<string>, change: OwnersChange): void {
        for (const { path, key, accessor } of state.accessors) {
            if (accessor !== null && (path !== null || installed.has(key))) this.#installs.set(installKey(path, key), { statement, accessor });
        }
        const own = new Set(change.added.map(([index, key]) => `${index}:${key}`));
        const names = new Set<string>();
        const accessors = new Set<string>();
        for (const [index, list] of state.names.entries()) {
            const original = new Set(this.#before[index] ?? []);
            const accessorNames = new Set(state.accessorNames[index] ?? []);
            for (const name of list) {
                if (original.has(name) || own.has(`${index}:${name}`)) continue;
                names.add(name);
                if (accessorNames.has(name)) accessors.add(name);
            }
        }
        this.#addedBefore.set(statement, { names, accessors });
    }

    /** The accessors at `places` as the statements left them: asked once, before any probe after them runs a getter. */
    #accessorsNow(places: readonly { path: PropertyPath | null; key: string }[]): Map<string, AccessorFunctions | null> {
        if (this.#now === undefined) {
            const requests = [...this.#installs.keys()].map((id) => {
                const [path, key] = JSON.parse(id) as [PropertyPath | null, string];
                return { path, key };
            });
            for (const place of places) if (!this.#installs.has(installKey(place.path, place.key))) requests.push(place);
            const found = requests.length === 0 ? [] : (this.#guest.accessors(requests) ?? []);
            this.#now = new Map(requests.map((request, i) => [installKey(request.path, request.key), found[i] ?? null]));
        }
        return this.#now;
    }

    /** The proofs that getters answer later as the probes saw (`getters.ts`), made when first needed. */
    get #getterProofs(): GetterProofs {
        this.#proofs ??= new GetterProofs({
            scopes: this.#scopes,
            guest: this.#guest,
            storage: this.#storage,
            rootBlocks: this.#rootScopes,
            owners: this.#guest.owners,
            before: this.#before.map((names) => new Set(names)),
            files: this.#files,
            globalArgs: this.#globalArgs,
            added: this.#addedBefore,
        });
        return this.#proofs;
    }

    /** Whether `failure` refused; logs why. */
    #refused(failure: ProofFailure, what: string, fallback: Node | undefined): boolean {
        if (failure === undefined) return false;
        this.#log.debug(`${what}: not taken, ${failure.reason}`, failure.node ?? fallback);
        return true;
    }

    /** Wrappers a storage assignment defines (recorded from here on), and what a builder it calls built. */
    #storageFacts(statement: Statement, env: string | undefined): void {
        const storage = this.#storage;
        const assignment = storageAssignment(statement);
        if (assignment === undefined || assignment.object !== storage) return;
        const found = wrapperOf(assignment.right, storage);
        if (found !== undefined && this.#guest.record(assignment.key, found.target)) {
            this.wrappers.set(assignment.key, { key: assignment.key, ...found, definition: statement });
            this.#log.debug(`wrapper ${assignment.key} -> ${storage}.${found.target.join(".")}`, statement);
        }
        const { right } = assignment;
        if (env === undefined && right.type === "CallExpression" && right.arguments.length === 0 && (right.callee.type === "FunctionExpression" || right.callee.type === "ArrowFunctionExpression")) {
            const identities = this.#guest.built([assignment.key]);
            if (identities !== undefined) this.built.set(statement, identities);
        }
    }

    /**
     * The statement's wrapper calls, matched to its call sites when `trusted`. Sites match calls in completion order
     * (post-order); sites in nested functions run later, in another state.
     */
    #mapCalls(statement: Statement, logged: readonly LoggedCall[], trusted: boolean): void {
        if (logged.length === 0) return;
        if (!trusted) {
            pushAll(this.unmappedCalls, logged);
            return;
        }
        pushAll(this.preludeCalls, logged);
        const sites: CallExpression[] = [];
        traverse(statement, {
            enter(path) {
                if (path.node !== statement && isFunctionNode(path.node)) path.skip();
            },
            CallExpression: {
                exit: (path) => {
                    const callee = path.node.callee;
                    if (callee.type !== "MemberExpression" || callee.object.type !== "Identifier" || callee.object.name !== this.#storage) return;
                    const key = propertyKey(callee);
                    if (key !== undefined && this.wrappers.has(key)) sites.push(path.node);
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
            this.#log.debug(`${logged.length} wrapper call(s) ran but don't line up with the ${sites.length} call site(s); results not used`, statement);
            pushAll(this.unmappedCalls, logged);
            return;
        }
        for (const [i, site] of sites.entries()) {
            const call = logged[i];
            if (call === undefined) continue;
            this.siteCalls.set(site, call);
            if (!isPrimitive(call.result)) continue;
            this.callResults.set(site, call.result);
            this.counts.mapped++;
            this.#log.debug(`call result ${JSON.stringify(call.result)}`, site);
        }
    }

    /** The probes after the statements run the program's getters too: they share the budget, and stop where it runs out. */
    #probeTimeout(): number | undefined {
        if (this.#budgetLeft() > 0) return this.#within(DEFAULT_LIMITS.timeoutMs);
        if (!this.#outOfBudget) this.#log.warn(`emulation budget of ${TOTAL_BUDGET_MS}ms used up: the remaining alias probes are skipped`);
        this.#outOfBudget = true;
        return undefined;
    }

    /** Names the program added to the owners that read like ones they had. */
    aliases(): Alias[] {
        const guest = this.#guest;
        const after = guest.snapshot();
        const added = guest.owners.map((owner, index) => {
            const existed = new Set(this.#before[index] ?? []);
            return (after[index] ?? []).filter((name) => !existed.has(name));
        });
        // Before the alias probes below run getters.
        const now = this.#accessorsNow(guest.owners.flatMap((path, index) => (added[index] ?? []).map((key) => ({ path, key }))));
        const aliases: Alias[] = [];
        for (const [index, owner] of guest.owners.entries()) {
            const was = this.#before[index] ?? [];
            for (const alias of added[index] ?? []) {
                const timeoutMs = this.#probeTimeout();
                if (timeoutMs === undefined) break;
                const found = guest.aliasOf(owner, alias, was, timeoutMs);
                if (found === undefined) continue;
                const appeared = this.#appearedAfter.get(`${index}:${alias}`);
                if ("env" in found) {
                    this.#log.debug(`${pathName(owner)}.${alias}: reading it ${found.env}; not taken as an alias`, appeared);
                    continue;
                }
                // A data property reads as written; an accessor reads as its getter answers, every time.
                const accessor = now.get(installKey(owner, alias));
                if (
                    accessor !== null &&
                    this.#refused(
                        accessor === undefined
                            ? { reason: "the guest doesn't tell what it is", node: undefined }
                            : this.#getterProofs.alias(owner, alias, this.#installs.get(installKey(owner, alias)), accessor),
                        `alias ${pathName(owner)}.${alias}`,
                        appeared
                    )
                ) {
                    this.unprovenAliases.add(alias);
                    continue;
                }
                aliases.push({ owner, alias, original: found.original });
                this.#log.debug(`alias ${pathName(owner)}.${alias} = ${pathName(owner)}.${found.original}`, appeared);
            }
        }
        return aliases;
    }

    callAliases(): Map<string, CallAlias> {
        const storage = this.#storage;
        const log = this.#log;
        const callAliases = new Map<string, CallAlias>();
        const timeoutMs = this.#bound ? this.#probeTimeout() : undefined;
        for (const found of timeoutMs === undefined ? [] : this.#guest.callAliases(timeoutMs)) {
            if ("env" in found) {
                log.debug(`${storage}.${found.key}: probing its getter ${found.env}; not taken as a call alias`, this.#installedBy.get(found.key));
                continue;
            }
            if (found.style === undefined) {
                log.debug(
                    `call alias ${storage}.${found.key}(...) hands out ${pathName(found.owner)}.${found.original}, but passes arguments on in neither known way; left`,
                    this.#installedBy.get(found.key)
                );
                continue;
            }
            if (
                this.#refused(
                    this.#getterProofs.callAlias(found.key, this.#installs.get(installKey(null, found.key)), this.#accessorsNow([]).get(installKey(null, found.key))),
                    `call alias ${storage}.${found.key}`,
                    this.#installedBy.get(found.key)
                )
            )
                continue;
            callAliases.set(found.key, { key: found.key, owner: found.owner, original: found.original, style: found.style });
            const shape = found.style === "method" ? `x.${found.original}(...)` : `${pathName(found.owner)}.${found.original}(...)`;
            log.debug(`call alias ${storage}.${found.key}(...) = ${shape}`, this.#installedBy.get(found.key));
        }
        return callAliases;
    }

    /** What setup keys and globals hand out of the global object; the storage keys holding it. */
    globalProbes(callAliases: ReadonlyMap<string, CallAlias>): { globalReads: Map<string, string>; hostAliases: Map<string, string>; globalKeys: Set<string> } {
        const guest = this.#guest;
        // Globals the global object lacks (the random names code locks probe with `typeof`).
        const globalReads = new Map<string, string>();
        const globalReadsTimeout = this.#bound ? this.#probeTimeout() : undefined;
        for (const { key, name } of globalReadsTimeout === undefined ? [] : guest.globalReads(globalReadsTimeout)) {
            if (callAliases.has(key) || !this.setupKeys.has(key)) continue;
            const now = this.#accessorsNow([]).get(installKey(null, key));
            if (this.#refused(this.#getterProofs.globalRead(key, name, this.#installs.get(installKey(null, key)), now), `global read ${this.#storage}.${key}()`, this.#installedBy.get(key))) continue;
            globalReads.set(key, name);
            this.#log.debug(`global read ${this.#storage}.${key}() = globalThis.${name}`, this.#installedBy.get(key));
        }
        const hostAliases = new Map<string, string>();
        const hostAliasesTimeout = this.setupGlobals.size > 0 ? this.#probeTimeout() : undefined;
        for (const { alias, name } of hostAliasesTimeout === undefined ? [] : guest.hostAliases([...this.setupGlobals], hostAliasesTimeout)) {
            if (
                this.#refused(this.#getterProofs.hostAlias(alias, name, this.#installs.get(installKey([], alias)), this.#accessorsNow([]).get(installKey([], alias))), `host alias ${alias}`, undefined)
            )
                continue;
            hostAliases.set(alias, name);
            this.#log.debug(`host alias ${alias} = globalThis.${name}`);
        }
        const globalKeysTimeout = this.#bound ? this.#probeTimeout() : undefined;
        const globalKeys = new Set(globalKeysTimeout === undefined ? [] : guest.globalKeys(globalKeysTimeout));
        return { globalReads, hostAliases, globalKeys };
    }

    /** Setup keys whose calls provably never use `G` as `this` (`GetterProofs.thisFree`); the others may. */
    thisFreeKeys(): Set<string> {
        const keys = new Set<string>();
        for (const key of this.setupKeys) {
            const failure = this.#getterProofs.thisFree(key, this.#installs.get(installKey(null, key)), this.#accessorsNow([]).get(installKey(null, key)));
            if (failure === undefined) keys.add(key);
            else this.#log.debug(`${this.#storage}.${key}(...) may use ${this.#storage} as this: ${failure.reason}`, failure.node ?? this.#installedBy.get(key));
        }
        return keys;
    }
}

/**
 * Runs right after `unflatten` and before anything rewrites the runtime, so the sandbox sees it as the obfuscator wrote
 * it. Produces the RUNTIME fact; changes no code.
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
        const before = guest.snapshot();
        const files: PrintedFunctions[] = [];
        const declared = declareRoot(guest, body, log, files);
        const emulation = new Emulation({ guest, log, storage, scopes, rootScopes, declared, before, files });
        emulation.runStatements(body);
        const aliases = emulation.aliases();
        const callAliases = emulation.callAliases();
        const { globalReads, hostAliases, globalKeys } = emulation.globalProbes(callAliases);
        const thisFreeKeys = emulation.thisFreeKeys();

        const { counts, wrappers, callResults, unmappedCalls, siteCalls, preludeCalls, built, pure, setup, setupKeys, setupGlobals, unprovenAliases, executed } = emulation;
        log.info(
            `ran ${counts.executed} statement(s), skipped ${counts.skipped}, failed ${counts.failed}, read the environment ${counts.tainted}, ran otherwise under the second lane ${counts.disagreed}; wrappers ${wrappers.size}, aliases ${aliases.length}, call aliases ${callAliases.size}, global keys [${[...globalKeys].join(", ")}], call results ${counts.mapped}`
        );
        facts.set(RUNTIME, {
            storage,
            root,
            globalKeys,
            aliases,
            unprovenAliases,
            thisFreeKeys,
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
