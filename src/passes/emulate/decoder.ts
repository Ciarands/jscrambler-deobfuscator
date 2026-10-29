import type { Expression, Function as FunctionNode, Node, Statement, VariableDeclarator } from "../../core/ast.js";
import { propertyKey } from "../../core/ast.js";
import { evaluate } from "../../core/evaluate.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { factKey } from "../../pipeline/facts.js";
import { parentsWithin, returnsOf } from "./builders.js";
import type { LoggedCall, PropertyPath } from "./guest.js";
import { pathName } from "./guest.js";
import type { RuntimeModel } from "./model.js";
import type { StorageMatcher } from "./storage.js";
import { rootStatements } from "./storage.js";

/**
 * jscrambler's string decoder, as its builder writes it:
 *
 *     G.k = (function () {
 *         var Q = { m: (function (key) {
 *             ...T = ""; T += ...; T = T.split(sep);        // setup: decode the table T
 *             var R = 0;
 *             var S = function (x) {                        // the stage function
 *                 [if (R === n) { return L(x); }]
 *                 if (R === 0 && x === 134) { R += 1; T.unshift.apply(T, T.splice(-7, 7).splice(0, 5)); }
 *                 else if (...) { ... }
 *                 else { Q.m = L; return L(x); }            // freeze
 *                 return R;                                 // or `return R++`
 *             };
 *             var L = function (y) { return T[y]; };        // the lookup
 *             return S;
 *         })("key") };
 *         return Q;
 *     })();
 *
 * What the proof needs from the template, by variable: `Q` is the builder's holder, referenced only by its declaration,
 * `return Q` and the freeze writes `Q.m = L`; `S` only by its declaration and `return S`; `L` only by its declaration and
 * in S's lookup exits; `R` only by its declaration (a number), S's guards and S's increments (by positive constants, on
 * stage paths only); the parameter `x` only read by S's guards and lookup exits; `T` only by L's read, by S's stage
 * bodies (shuffles) and by F's own top-level code before and in its last write, which splits a string.
 */
interface Template {
    readonly stages: readonly { readonly state: number; readonly argument: number | undefined }[];
    /** What a stage body adds to `R`, and how S's last statement returns it: `R`, `R++` (`post`), `++R` (`pre`). */
    readonly bodyStep: number;
    readonly tail: "after" | "post" | "pre";
}

/** The names S's template binds, as they're found. */
interface Bindings {
    readonly holder: Variable;
    readonly argument: Variable;
    state: Variable | undefined;
    lookup: Variable | undefined;
    table: Variable | undefined;
}

/** The declarator of a variable declared once, by a `var`/`let`/`const` statement in `body`. */
const declaratorIn = (variable: Variable, body: readonly Statement[]): VariableDeclarator | undefined => {
    const [def] = variable.defs;
    if (variable.defs.length !== 1 || def?.type !== "Variable" || !body.includes(def.parent as unknown as Statement)) return undefined;
    return def.node as unknown as VariableDeclarator;
};

/** Statements of a function with a block body (an arrow's included). */
const blockOf = (fn: Node): readonly Statement[] | undefined =>
    (fn.type === "FunctionExpression" || fn.type === "ArrowFunctionExpression") && fn.body?.type === "BlockStatement" ? fn.body.body : undefined;

/** `-3` or `3`. */
const numberOf = (node: Node): number | undefined => {
    if (node.type === "Literal" && typeof node.value === "number") return node.value;
    if (node.type === "UnaryExpression" && node.operator === "-" && node.argument.type === "Literal" && typeof node.argument.value === "number") return -node.argument.value;
    return undefined;
};

/** The conjuncts of `a && b && c`. */
const conjuncts = (test: Expression): Expression[] => (test.type === "LogicalExpression" && test.operator === "&&" ? [...conjuncts(test.left), ...conjuncts(test.right)] : [test]);

/** A plain (not async or generator) function expression or arrow. */
const plainFunction = (node: Node): FunctionNode | undefined =>
    (node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression") && !node.async && !node.generator ? (node as FunctionNode) : undefined;

/** The one function a local is bound to by its declaration in `body` (`var L = function (y) {...}`). */
const localFunction = (variable: Variable, body: readonly Statement[]): FunctionNode | undefined => {
    const init = declaratorIn(variable, body)?.init;
    return init === null || init === undefined ? undefined : plainFunction(init);
};

/** Two number arguments (a splice's start and count). */
const twoNumbers = (args: readonly Node[]): boolean => args.length === 2 && args.every((arg) => numberOf(arg) !== undefined);

const isStringLiteral = (node: Node | undefined): boolean => node?.type === "Literal" && typeof node.value === "string";

/** What the decoder proof found: recorded calls that were pure lookups, and the wrapper keys of settled decoders. */
export interface DecoderProof {
    readonly lookups: ReadonlySet<LoggedCall>;
    /**
     * Wrappers whose target is a decoder settled during the prelude and still in place after it (`G.k` is `Q`, `G.k.m`
     * is S or L): a later call of them is a pure lookup unless something writes `G.k` or `G.k.m` after the prelude.
     */
    readonly settled: ReadonlySet<string>;
    /**
     * Targets (`JSON.stringify` of `[k, m]`) that follow the template, settled or not: a call of one writes nothing but
     * the decoder's own state (`T`, `R`, `Q.m`), all reachable only through `G.k`.
     */
    readonly templated: ReadonlySet<string>;
    /** The recorded call that settled each decoder in `settled`: calls made after it can't drive a stage. */
    readonly settlingCalls: ReadonlySet<LoggedCall>;
}

/** The decoder proof resolve-calls made, for cleanup: stage calls of templated decoders only touch their own state. */
export const DECODER_PROOF = factKey<DecoderProof>("decoder proof");

/**
 * Which recorded calls of jscrambler's string decoders were pure table lookups (see `Template`), and which decoders
 * are settled once the prelude is done.
 *
 * Proof, per decoder `G.k.m`. The template makes `S` write only `T`, `R` (stage paths) and `Q.m` (lookup exits, only
 * ever to `L`), and return `L(x)`, which only reads `T[x]`, on every path but the stage paths; a stage path requires
 * `R === c` for one of the stage guards `c`, and `R` only grows. So once `R` exceeds every guard (the decoder is
 * settled), S and L are both `x => T[x]` with `T` fixed: T's array came fresh from `split` and only ever went to
 * builtins as their receiver (the shuffles), so nothing else holds it; the stage paths, the only code writing `T`
 * after the setup, can't run again. That holds wherever S or L got to, so no escape analysis is needed. (Relies on
 * model 7: builtins intact. `split`, `splice`, `unshift` and `apply`, reached by name, through the aliases the runtime
 * added or through its call aliases, are the standard ones: they return fresh arrays and keep no receiver.)
 *
 * The guest says when that happens: right after the builder ran, `G.k` is `Q` and `G.k.m` is `S` (identities). A
 * recorded call on S that left `G.k.m` alone, with an integer argument and a number result (and no index property on
 * `Array.prototype`/`Object.prototype`) took a stage path: L's `T[x]` gives the table's strings or `undefined`. Its
 * result tells `R` after it; when that exceeds every guard (and matches the stage table), the decoder is settled from
 * that call on. The call must have been made while the guest still matched a real run: then a real run settles at the
 * same point. Every recorded call made after it on `Q` (`G.k` still `Q`) that found S or L at `G.k.m` and left it
 * there wrote nothing: it is a pure lookup, whose value is what the guest saw. (A call that replaced S by L, the
 * freeze, is not: it wrote `Q.m`.) L's identity is what such a call left at `G.k.m`. A later call is a lookup too
 * when the prelude left `G.k` at `Q` and `G.k.m` at S or L (the guest's final state) and nothing writes them after it.
 */
export const decoderLookups = (runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, log: PassLog): DecoderProof => {
    const lookups = new Set<LoggedCall>();
    const settledKeys = new Set<string>();
    const templated = new Set<string>();
    const settlingCalls = new Set<LoggedCall>();
    const { storage, wrappers, aliases, callAliases } = runtime;
    const originals = new Map(aliases.map((alias) => [`${pathName(alias.owner)}.${alias.alias}`, alias.original]));
    /** The builtin `owner.name` stands for: an alias's original, or the name itself (relies on model 7: builtins intact). */
    const builtin = (owner: string, name: string | undefined): string | undefined => (name === undefined ? undefined : (originals.get(`${owner}.${name}`) ?? name));
    /** The call alias `G.key(...)` is, as `owner.original`. */
    const callAliasOf = (callee: Node): string | undefined => {
        if (callee.type !== "MemberExpression" || !matcher.isStorage(callee.object)) return undefined;
        const alias = callAliases.get(propertyKey(callee) ?? "");
        return alias === undefined ? undefined : `${pathName(alias.owner)}.${alias.original}`;
    };

    // Wrapper targets `G.k.m`, and the root statements assigning `G.k`.
    const targets = new Map<string, PropertyPath>();
    /** The target id (`JSON.stringify` of its path) each wrapper key calls. */
    const targetOf = new Map<string, string>();
    for (const wrapper of wrappers.values()) {
        if (wrapper.target.length !== 2) continue;
        const id = JSON.stringify(wrapper.target);
        targets.set(id, wrapper.target);
        targetOf.set(wrapper.key, id);
    }
    const assigned = new Map<string, Statement[]>();
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const target = statement.expression.left;
        const key = target.type === "MemberExpression" && matcher.isStorage(target.object) ? propertyKey(target) : undefined;
        if (key !== undefined) assigned.set(key, [...(assigned.get(key) ?? []), statement]);
    }
    const order = new Map(runtime.preludeCalls.map((call, index) => [call, index]));
    const recorded = [...runtime.preludeCalls, ...runtime.unmappedCalls.filter((call) => !order.has(call))];

    for (const [id, target] of targets) {
        const [key, method] = target as [string, string];
        const name = `${storage}.${target.join(".")}`;
        const statements = assigned.get(key) ?? [];
        const [statement] = statements;
        if (statement === undefined || statements.length !== 1) {
            log.debug(
                `${name}: not a string decoder of the known template, ${statements.length === 0 ? `no root statement assigns ${storage}.${key}` : `${statements.length} root statements assign ${storage}.${key}`}`
            );
            continue;
        }
        const template = templateOf(statement, method);
        if (typeof template === "string") {
            log.debug(`${name}: not a string decoder of the known template, ${template}`, statement);
            continue;
        }
        templated.add(id);
        const identities = runtime.built.get(statement);
        const stageId = identities?.methods.get(method);
        if (identities === undefined || stageId === undefined) {
            log.debug(`decoder ${name}: not proven, the guest didn't see what the builder stored`, statement);
            continue;
        }
        const holderId = identities.holder;
        const calls = recorded.filter((call) => targetOf.get(call.key) === id);
        const frozenTo = new Set(calls.filter((call) => call.owner === holderId && call.before === stageId && call.after !== stageId).map((call) => call.after));
        if (frozenTo.size > 1 || frozenTo.has(null)) {
            log.debug(`decoder ${name}: not proven, its calls left ${frozenTo.size} different values at ${name}`, statement);
            continue;
        }
        const [lookupId] = frozenTo;
        const settled = settlingCall(calls, order, template, holderId, stageId);
        if (settled === undefined) {
            log.debug(`decoder ${name}: not proven, no recorded call settled it while the guest followed a real run`, statement);
            continue;
        }
        const settledAt = order.get(settled) as number;
        let count = 0;
        for (const call of calls) {
            if ((order.get(call) ?? Number.POSITIVE_INFINITY) <= settledAt || call.owner !== holderId || call.before !== call.after) continue;
            if (call.before !== stageId && (lookupId === undefined || call.before !== lookupId)) continue;
            if (call.args.some((arg) => typeof arg === "object" && arg !== null) || (typeof call.result === "object" && call.result !== null)) continue;
            lookups.add(call);
            count++;
        }
        const stage = `${settled.key}(${settled.args.map((arg) => JSON.stringify(arg)).join(", ")})`;
        log.debug(
            `decoder ${name}: settled by its recorded call ${stage} = ${String(settled.result)}, which leaves its counter past all ${template.stages.length} stage guards; ${count} later recorded call(s) are pure lookups`,
            statement
        );
        // Later calls are lookups too while G.k is still Q and G.k.m still S or L: so the prelude must leave them there
        // (what may change them afterwards is the storage analysis' question, per call site).
        const current = runtime.guest.stateKey(target);
        if (runtime.guest.stateKey([key]) !== `o:${holderId}` || (current !== `o:${stageId}` && (lookupId === undefined || current !== `o:${lookupId}`))) {
            log.debug(
                `decoder ${name}: after the prelude, ${name} is no longer its stage function or lookup (or ${storage}.${key} no longer its holder): later calls aren't proven lookups`,
                statement
            );
            continue;
        }
        for (const [wrapperKey, wrapperTarget] of targetOf) if (wrapperTarget === id) settledKeys.add(wrapperKey);
        settlingCalls.add(settled);
    }
    if (settledKeys.size > 0) log.info(`${settledKeys.size} wrapper(s) of string decoders proven settled during the prelude; ${lookups.size} recorded call(s) on them were pure lookups`);
    return { lookups, settled: settledKeys, templated, settlingCalls };

    /** The template's facts, or why the builder statement doesn't follow it. */
    function templateOf(statement: Statement, method: string): Template | string {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=")
            return "its holder isn't assigned by a plain assignment";
        const built = statement.expression.right;
        const builder = built.type === "CallExpression" && built.arguments.length === 0 ? plainFunction(built.callee) : undefined;
        const builderBody = builder === undefined ? undefined : blockOf(builder);
        if (builder === undefined || builderBody === undefined) return "its holder isn't built by an immediately invoked function";
        const returned = returnsOf(builder);
        const last = builderBody.at(-1);
        if (returned.length !== 1 || last?.type !== "ReturnStatement" || last.argument?.type !== "Identifier") return "the builder doesn't end in its one return of a local";
        const holder = scopes.variableOf(last.argument);
        const holderDeclarator = holder === undefined ? undefined : declaratorIn(holder, builderBody);
        if (holder === undefined || holderDeclarator?.init?.type !== "ObjectExpression") return "the builder's result isn't an object literal its own code declares";
        const properties = holderDeclarator.init.properties;
        if (properties.some((p) => p.type !== "Property" || p.computed)) return "the holder literal has a computed or spread property";
        const methods = properties.filter((p) => p.type === "Property" && propertyName(p.key) === method);
        const [property] = methods;
        if (methods.length !== 1 || property?.type !== "Property" || property.kind !== "init" || property.method) return `the holder literal doesn't have exactly one plain property ${method}`;
        const setup = property.value.type === "CallExpression" ? plainFunction(property.value.callee) : undefined;
        const setupBody = setup === undefined ? undefined : blockOf(setup);
        if (setup === undefined || setupBody === undefined) return `${method} isn't the result of an immediately invoked function`;
        const setupReturns = returnsOf(setup);
        const setupLast = setupBody.at(-1);
        if (setupReturns.length !== 1 || setupLast?.type !== "ReturnStatement" || setupLast.argument?.type !== "Identifier") return "its setup function doesn't end in its one return of a local";
        const stageVariable = scopes.variableOf(setupLast.argument);
        const stageFn = stageVariable === undefined ? undefined : localFunction(stageVariable, setupBody);
        if (stageVariable === undefined || stageFn === undefined) return "the stage function isn't a function local to the setup";
        const [param] = stageFn.params;
        const argument = stageFn.params.length === 1 && param?.type === "Identifier" ? scopes.variableOf(param) : undefined;
        if (argument === undefined) return "the stage function doesn't take one plain parameter";

        const bindings: Bindings = { holder, argument, state: undefined, lookup: undefined, table: undefined };
        const accepted = new Set<Node>();
        const stage = matchStage(stageFn, method, setupBody, bindings, accepted);
        if (typeof stage === "string") return stage;
        const { state, lookup, table } = bindings;
        if (state === undefined || lookup === undefined || table === undefined) return "the stage function's names weren't all found";

        // Every reference to the template's names is one it allows.
        const only = (variable: Variable, allowed: (identifier: Node) => boolean): boolean =>
            scopes.staticReferences(variable).every((reference) => {
                const identifier = reference.identifier as unknown as Node;
                return accepted.has(identifier) || variable.identifiers.includes(identifier as never) || allowed(identifier);
            });
        if (!only(holder, (identifier) => identifier === last.argument)) return "the holder is used outside the template";
        if (!only(stageVariable, (identifier) => identifier === setupLast.argument)) return "the stage function is used outside the template";
        if (!only(lookup, () => false)) return "the lookup is used outside the stage function";
        if (!only(argument, () => false)) return "the stage function's parameter is used outside its guards and lookups";
        const stateInit = declaratorIn(state, setupBody)?.init;
        if (stateInit === null || stateInit === undefined || numberOf(stateInit) === undefined) return "the stage counter isn't a number the setup's own code declares";
        if (!only(state, () => false)) return "the stage counter is used outside the stage function";
        const tableProblem = checkTable(table, setup, setupBody, accepted);
        return tableProblem ?? stage;
    }

    /** S's statements: lookup exits, the stage chain, the tail return. Binds R, L and T on the way. */
    function matchStage(fn: FunctionNode, method: string, setupBody: readonly Statement[], bindings: Bindings, accepted: Set<Node>): Template | string {
        const body = blockOf(fn);
        const tail = body?.at(-1);
        const chain = body?.at(-2);
        if (body === undefined || tail?.type !== "ReturnStatement" || tail.argument === null || chain?.type !== "IfStatement")
            return "the stage function doesn't end in its stage chain and a return of its counter";
        // The tail return: `return R`, `return R++`, `return ++R`.
        const returned = tail.argument;
        const counter = returned.type === "UpdateExpression" && returned.operator === "++" ? returned.argument : returned;
        if (counter.type !== "Identifier") return "the stage function doesn't return its counter";
        bindings.state = scopes.variableOf(counter);
        if (bindings.state === undefined) return "the stage counter isn't a local";
        accepted.add(counter);
        const tailKind = returned.type === "UpdateExpression" ? (returned.prefix ? "pre" : "post") : "after";

        // The chain: stage branches, then the freeze (which names L, and through it T).
        const branches: { test: Expression; body: Node }[] = [];
        let link: Node = chain;
        while (link.type === "IfStatement") {
            branches.push({ test: link.test, body: link.consequent });
            if (link.alternate === null) return "the stage chain has no final freeze";
            link = link.alternate;
        }
        const freeze = lookupExit(link, method, bindings, accepted);
        if (freeze !== undefined) return freeze;
        const lookupFn = bindings.lookup === undefined ? undefined : localFunction(bindings.lookup, setupBody);
        const tableProblem = lookupFn === undefined ? "the lookup isn't a function local to the setup" : bindTable(lookupFn, bindings, accepted);
        if (tableProblem !== undefined) return tableProblem;

        for (const statement of body.slice(0, -2)) {
            if (statement.type !== "IfStatement" || statement.alternate !== null) return "the stage function has other statements than its exits, chain and return";
            const guard = guardOf(statement.test, bindings, accepted);
            if (typeof guard === "string") return guard;
            const exit = lookupExit(statement.consequent, method, bindings, accepted);
            if (exit !== undefined) return exit;
        }
        const stages: { state: number; argument: number | undefined }[] = [];
        let bodyStep: number | undefined;
        for (const branch of branches) {
            const guard = guardOf(branch.test, bindings, accepted);
            if (typeof guard === "string") return guard;
            if (guard.state === undefined) return "a stage branch isn't guarded by its counter";
            stages.push({ state: guard.state, argument: guard.argument });
            const step = stageBody(branch.body, bindings, accepted);
            if (typeof step === "string") return step;
            if (bodyStep !== undefined && step !== bodyStep) return "the stage branches step the counter by different amounts";
            bodyStep = step;
        }
        if (bodyStep === undefined || bodyStep + (tailKind === "after" ? 0 : 1) <= 0) return "the stages don't step the counter";
        return { stages, bodyStep, tail: tailKind };
    }

    /** `{ [Q.m = L;] [if (true) { Q.m = L; }] return L(x); }`: writes L to Q.m, then looks x up. */
    function lookupExit(node: Node, method: string, bindings: Bindings, accepted: Set<Node>): string | undefined {
        const statements = node.type === "BlockStatement" ? node.body : [node as Statement];
        const last = statements.at(-1);
        const call = last?.type === "ReturnStatement" ? last.argument : null;
        if (call?.type !== "CallExpression" || call.callee.type !== "Identifier" || call.arguments.length !== 1) return "an exit of the stage function doesn't return a lookup";
        const lookup = scopes.variableOf(call.callee);
        bindings.lookup ??= lookup;
        const [argument] = call.arguments;
        if (lookup === undefined || lookup !== bindings.lookup || argument?.type !== "Identifier" || scopes.variableOf(argument) !== bindings.argument)
            return "an exit of the stage function doesn't look its argument up";
        accepted.add(call.callee).add(argument);
        const freezeWrite = (statement: Node): boolean => {
            if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return false;
            const { left, right } = statement.expression;
            if (left.type !== "MemberExpression" || left.object.type !== "Identifier" || propertyKey(left) !== method || scopes.variableOf(left.object) !== bindings.holder) return false;
            if (right.type !== "Identifier" || scopes.variableOf(right) !== bindings.lookup) return false;
            accepted.add(left.object).add(right);
            return true;
        };
        for (const statement of statements.slice(0, -1)) {
            if (freezeWrite(statement)) continue;
            // `if (true) { Q.m = L; }`, as unflattening leaves it.
            if (statement.type === "IfStatement" && statement.alternate === null) {
                const test = evaluate(statement.test);
                const writes = statement.consequent.type === "BlockStatement" ? statement.consequent.body : [statement.consequent];
                if (test.ok && Boolean(test.value) && writes.every(freezeWrite)) continue;
            }
            return "an exit of the stage function does more than write the lookup to the holder";
        }
        return undefined;
    }

    /** L's body `return T[y]` (or `y => T[y]`): binds T. */
    function bindTable(fn: Node, bindings: Bindings, accepted: Set<Node>): string | undefined {
        const lookupFn = plainFunction(fn);
        const [param] = lookupFn?.params ?? [];
        const body = lookupFn?.body;
        const statements = body?.type === "BlockStatement" ? body.body : undefined;
        const only = statements?.length === 1 ? statements[0] : undefined;
        const read = body?.type === "BlockStatement" ? (only?.type === "ReturnStatement" ? only.argument : null) : body;
        if (
            lookupFn?.params.length !== 1 ||
            param?.type !== "Identifier" ||
            read?.type !== "MemberExpression" ||
            !read.computed ||
            read.object.type !== "Identifier" ||
            read.property.type !== "Identifier"
        )
            return "the lookup isn't `y => T[y]`";
        const index = scopes.variableOf(read.property);
        if (index === undefined || index !== scopes.variableOf(param) || !scopes.staticReferences(index).every((reference) => (reference.identifier as unknown as Node) === read.property))
            return "the lookup isn't `y => T[y]`";
        bindings.table = scopes.variableOf(read.object);
        if (bindings.table === undefined) return "the lookup's table isn't a local";
        accepted.add(read.object);
        return undefined;
    }

    /** `R === c && x === d` (either order, either side): the counter's guard and the argument it wants. */
    function guardOf(test: Expression, bindings: Bindings, accepted: Set<Node>): { state: number | undefined; argument: number | undefined } | string {
        let state: number | undefined;
        let argument: number | undefined;
        for (const conjunct of conjuncts(test)) {
            if (conjunct.type !== "BinaryExpression" || conjunct.operator !== "===") return "a guard in the stage function isn't a conjunction of strict comparisons";
            const [name, constant] = conjunct.left.type === "Identifier" ? [conjunct.left, conjunct.right] : [conjunct.right, conjunct.left];
            const value = numberOf(constant);
            const variable = name.type === "Identifier" ? scopes.variableOf(name) : undefined;
            if (value === undefined || variable === undefined) return "a guard in the stage function doesn't compare a name with a number";
            if (variable === bindings.state && state === undefined) state = value;
            else if (variable === bindings.argument && argument === undefined) argument = value;
            else return "a guard in the stage function compares other names";
            accepted.add(name);
        }
        return { state, argument };
    }

    /** A stage body: counter increments and table shuffles. What it adds to the counter, or why it isn't one. */
    function stageBody(node: Node, bindings: Bindings, accepted: Set<Node>): number | string {
        let step = 0;
        for (const statement of node.type === "BlockStatement" ? node.body : [node as Statement]) {
            if (statement.type !== "ExpressionStatement") return "a stage body has other statements than increments and shuffles";
            const e = statement.expression;
            const increment =
                e.type === "UpdateExpression" && e.operator === "++"
                    ? { name: e.argument, by: 1 }
                    : e.type === "AssignmentExpression" && e.operator === "+="
                      ? { name: e.left, by: numberOf(e.right) }
                      : undefined;
            if (increment !== undefined) {
                if (increment.name.type !== "Identifier" || scopes.variableOf(increment.name) !== bindings.state || increment.by === undefined || increment.by <= 0)
                    return "a stage body changes the counter otherwise than by a positive step";
                accepted.add(increment.name);
                step += increment.by;
                continue;
            }
            if (!shuffle(e, bindings, accepted)) return "a stage body has a statement other than the table shuffle";
        }
        return step;
    }

    /** `T` itself. */
    function isTable(node: Node, bindings: Bindings, accepted: Set<Node>): boolean {
        if (node.type !== "Identifier" || scopes.variableOf(node) !== bindings.table) return false;
        accepted.add(node);
        return true;
    }

    /** `X.splice(a, b)` / `G.splice(X, a, b)` with `X` as `inner` says (relies on model 7: builtins intact). */
    function splice(node: Node, inner: (node: Node) => boolean): boolean {
        if (node.type !== "CallExpression") return false;
        const { callee } = node;
        if (callee.type === "MemberExpression" && builtin("Array.prototype", propertyKey(callee)) === "splice") return twoNumbers(node.arguments) && inner(callee.object);
        const [receiver, ...rest] = node.arguments;
        return callAliasOf(callee) === "Array.prototype.splice" && receiver !== undefined && twoNumbers(rest) && inner(receiver);
    }

    /**
     * `T.unshift.apply(T, T.splice(a, b).splice(c, d))`, or with call aliases `G.apply(G.unshift(), T, G.splice(G.splice(T,
     * a, b), c, d))`: moves some of T's own elements to its front, and hands T to builtins only as their receiver
     * (relies on model 7: builtins intact).
     */
    function shuffle(node: Node, bindings: Bindings, accepted: Set<Node>): boolean {
        if (node.type !== "CallExpression") return false;
        const table = (n: Node): boolean => isTable(n, bindings, accepted);
        const spliced = (n: Node): boolean => splice(n, (inner) => splice(inner, table));
        const { callee } = node;
        if (callee.type === "MemberExpression" && builtin("Function.prototype", propertyKey(callee)) === "apply") {
            const unshift = callee.object;
            const [receiver, items] = node.arguments;
            return (
                node.arguments.length === 2 &&
                unshift.type === "MemberExpression" &&
                builtin("Array.prototype", propertyKey(unshift)) === "unshift" &&
                table(unshift.object) &&
                receiver !== undefined &&
                table(receiver) &&
                items !== undefined &&
                spliced(items)
            );
        }
        const [handout, receiver, items] = node.arguments;
        return (
            callAliasOf(callee) === "Function.prototype.apply" &&
            node.arguments.length === 3 &&
            handout?.type === "CallExpression" &&
            handout.arguments.length === 0 &&
            callAliasOf(handout.callee) === "Array.prototype.unshift" &&
            receiver !== undefined &&
            table(receiver) &&
            items !== undefined &&
            spliced(items)
        );
    }

    /**
     * T's references: L's read, the stage bodies' (accepted), and the setup's own top-level code up to its last write,
     * a top-level statement that splits T, until which T is a string (only string literals and `+=` write it).
     */
    function checkTable(table: Variable, setup: FunctionNode, setupBody: readonly Statement[], accepted: ReadonlySet<Node>): string | undefined {
        if (table.scope.block !== (setup as never)) return "the table isn't a local of the setup";
        const parents = parentsWithin(setup);
        /** The index of the setup's top-level statement a node is in (positions don't tell: passes before moved code). */
        const statementIndex = (node: Node): number => {
            let current: Node | undefined = node;
            while (current !== undefined && !setupBody.includes(current as Statement)) current = parents.get(current);
            return current === undefined ? -1 : setupBody.indexOf(current as Statement);
        };
        const own: { identifier: Node; index: number }[] = [];
        for (const reference of scopes.staticReferences(table)) {
            const identifier = reference.identifier as unknown as Node;
            if (accepted.has(identifier)) continue;
            if ((reference.from.variableScope.block as unknown as Node) !== setup) return "the table is used by another function";
            own.push({ identifier, index: statementIndex(identifier) });
        }
        const writeOf = (identifier: Node): Node | undefined => {
            const parent = parents.get(identifier);
            return (parent?.type === "AssignmentExpression" && parent.left === identifier) || (parent?.type === "VariableDeclarator" && parent.id === identifier) ? parent : undefined;
        };
        const writes = own.filter(({ identifier }) => writeOf(identifier) !== undefined);
        const lastIndex = Math.max(...writes.map(({ index }) => index));
        const last = writes.filter(({ index }) => index === lastIndex);
        const [final] = last;
        const write = final === undefined ? undefined : writeOf(final.identifier);
        const statement = setupBody[lastIndex];
        const value = write?.type === "AssignmentExpression" && write.operator === "=" ? write.right : write?.type === "VariableDeclarator" ? write.init : null;
        if (last.length !== 1 || write === undefined || statement === undefined || parents.get(write) !== statement || value === null || value === undefined || !splits(value, table))
            return "the table's last write in the setup isn't a top-level statement that splits it";
        for (const { identifier, index } of own) {
            if (index < 0 || index > lastIndex) return "the setup uses the table after splitting it";
            const other = writeOf(identifier);
            if (other === undefined || other === write) continue;
            const stringValue = other.type === "AssignmentExpression" ? (other.operator === "+=" ? true : other.right) : other.type === "VariableDeclarator" ? (other.init ?? true) : false;
            if (stringValue !== true && (stringValue === false || stringValue.type !== "Literal" || typeof stringValue.value !== "string"))
                return "the setup writes the table with something other than strings before splitting it";
        }
        return undefined;
    }

    /** `T.split(s)` / `G.split(T, s)` with `s` a string literal: a fresh array of strings (relies on model 7: builtins intact). */
    function splits(value: Node, table: Variable): boolean {
        if (value.type !== "CallExpression") return false;
        const isTableName = (node: Node | undefined): boolean => node?.type === "Identifier" && scopes.variableOf(node) === table;
        const { callee } = value;
        if (callee.type === "MemberExpression" && builtin("String.prototype", propertyKey(callee)) === "split")
            return isTableName(callee.object) && value.arguments.length === 1 && isStringLiteral(value.arguments[0]);
        return callAliasOf(callee) === "String.prototype.split" && value.arguments.length === 2 && isTableName(value.arguments[0]) && isStringLiteral(value.arguments[1]);
    }
};

/** The name a non-computed object-literal key gives its property. */
const propertyName = (key: Node): string | undefined => {
    if (key.type === "Identifier") return key.name;
    if (key.type === "Literal" && (typeof key.value === "string" || typeof key.value === "number")) return String(key.value);
    return undefined;
};

/**
 * The first recorded call, made while the guest followed a real run, that settled the decoder: a call on S (on the
 * holder the builder made) that left S in place, took a stage path (a number result: see `decoderLookups`) and left
 * the counter past every stage guard, consistently with the stage table.
 */
const settlingCall = (calls: readonly LoggedCall[], order: ReadonlyMap<LoggedCall, number>, template: Template, holderId: number, stageId: number): LoggedCall | undefined => {
    const highest = Math.max(...template.stages.map((stage) => stage.state));
    return calls.find((call) => {
        const [argument] = call.args;
        const { result } = call;
        if (!order.has(call) || call.owner !== holderId || call.before !== stageId || call.after !== stageId || call.indexed !== false) return false;
        if (typeof argument !== "number" || !Number.isInteger(argument) || argument < 0 || argument >= 2 ** 32 - 1 || typeof result !== "number") return false;
        const before = result - template.bodyStep - (template.tail === "pre" ? 1 : 0);
        const after = before + template.bodyStep + (template.tail === "after" ? 0 : 1);
        return after > highest && template.stages.some((stage) => stage.state === before && (stage.argument === undefined || stage.argument === argument));
    });
};
