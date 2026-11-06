import type { CallExpression, Expression, Function as FunctionNode, Node, Statement, VariableDeclarator } from "../../core/ast.js";
import { keyName, memberPath, propertyKey } from "../../core/ast.js";
import { isObject } from "../../core/builtins.js";
import type { Value } from "../../core/evaluate.js";
import { evaluate } from "../../core/evaluate.js";
import type { Held } from "../../core/interpret.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import { factKey } from "../../pipeline/facts.js";
import { keySets, mayName } from "../key-sets.js";
import type { KeySet } from "../key-sets.js";
import { parentsWithin, returnsOf } from "./builders.js";
import type { HostDecoder } from "./decoder-host.js";
import { buildHostDecoder, keySetAliases } from "./decoder-host.js";
import type { OrderContext } from "./decoder-order.js";
import { statementOrder } from "./decoder-order.js";
import { pathName } from "./model.js";
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
 * The proof needs: `Q` referenced only by its declaration, `return Q` and freeze writes `Q.m = L`; `S` only by its
 * declaration and `return S`; `L` only by its declaration and S's lookup exits; `R` only by its declaration (a number),
 * S's guards and S's increments (positive constants, stage paths only); `x` only read by S's guards and lookup exits;
 * `T` only by L's read, S's stage bodies (shuffles) and F's top-level code up to its last write, which splits a string.
 */
interface Template {
    readonly stages: readonly { readonly state: number; readonly argument: number | undefined }[];
    /** `bodyStep`: what a stage body adds to `R`; `tail`: S returns `R`, `R++` (`post`) or `++R` (`pre`). */
    readonly bodyStep: number;
    readonly tail: "after" | "post" | "pre";
}

interface Bindings {
    readonly holder: Variable;
    readonly argument: Variable;
    state: Variable | undefined;
    lookup: Variable | undefined;
    table: Variable | undefined;
}

/** What the template's matchers resolve names and builtins through. */
interface DecoderContext {
    readonly scopes: ScopeInfo;
    readonly matcher: StorageMatcher;
    readonly callAliases: RuntimeModel["callAliases"];
    /** Each alias's original, by `owner.alias`. */
    readonly originals: ReadonlyMap<string, string>;
}

const declaratorIn = (variable: Variable, body: readonly Statement[]): VariableDeclarator | undefined => {
    const [def] = variable.defs;
    if (variable.defs.length !== 1 || def?.type !== "Variable" || !body.includes(def.parent as unknown as Statement)) return undefined;
    return def.node as unknown as VariableDeclarator;
};

/** Arrows included. */
const blockOf = (fn: Node): readonly Statement[] | undefined =>
    (fn.type === "FunctionExpression" || fn.type === "ArrowFunctionExpression") && fn.body?.type === "BlockStatement" ? fn.body.body : undefined;

/** `-3` or `3`. */
const numberOf = (node: Node): number | undefined => {
    if (node.type === "Literal" && typeof node.value === "number") return node.value;
    if (node.type === "UnaryExpression" && node.operator === "-" && node.argument.type === "Literal" && typeof node.argument.value === "number") return -node.argument.value;
    return undefined;
};

const conjuncts = (test: Expression): Expression[] => (test.type === "LogicalExpression" && test.operator === "&&" ? [...conjuncts(test.left), ...conjuncts(test.right)] : [test]);

const plainFunction = (node: Node): FunctionNode | undefined =>
    (node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression") && !node.async && !node.generator ? (node as FunctionNode) : undefined;

const localFunction = (variable: Variable, body: readonly Statement[]): FunctionNode | undefined => {
    const init = declaratorIn(variable, body)?.init;
    return init === null || init === undefined ? undefined : plainFunction(init);
};

const twoNumbers = (args: readonly Node[]): boolean => args.length === 2 && args.every((arg) => numberOf(arg) !== undefined);

const isStringLiteral = (node: Node | undefined): boolean => node?.type === "Literal" && typeof node.value === "string";

/** An alias's original, or the name itself (relies on model 7: builtins intact). */
const builtin = (cx: DecoderContext, owner: string, name: string | undefined): string | undefined => (name === undefined ? undefined : (cx.originals.get(`${owner}.${name}`) ?? name));

/** As `owner.original`. */
const callAliasOf = (cx: DecoderContext, callee: Node): string | undefined => {
    if (callee.type !== "MemberExpression" || !cx.matcher.isStorage(callee.object)) return undefined;
    const alias = cx.callAliases.get(propertyKey(callee) ?? "");
    return alias === undefined ? undefined : `${pathName(alias.owner)}.${alias.original}`;
};

const templateOf = (cx: DecoderContext, statement: Statement, method: string): Template | string => {
    const { scopes } = cx;
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
    const methods = properties.filter((p) => p.type === "Property" && keyName(p.key) === method);
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
    const stage = matchStage(cx, stageFn, method, setupBody, bindings, accepted);
    if (typeof stage === "string") return stage;
    const { state, lookup, table } = bindings;
    if (state === undefined || lookup === undefined || table === undefined) return "the stage function's names weren't all found";

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
    const tableProblem = checkTable(cx, table, setup, setupBody, accepted);
    return tableProblem ?? stage;
};

const matchStage = (cx: DecoderContext, fn: FunctionNode, method: string, setupBody: readonly Statement[], bindings: Bindings, accepted: Set<Node>): Template | string => {
    const { scopes } = cx;
    const body = blockOf(fn);
    const tail = body?.at(-1);
    const chain = body?.at(-2);
    if (body === undefined || tail?.type !== "ReturnStatement" || tail.argument === null || chain?.type !== "IfStatement")
        return "the stage function doesn't end in its stage chain and a return of its counter";
    const returned = tail.argument;
    const counter = returned.type === "UpdateExpression" && returned.operator === "++" ? returned.argument : returned;
    if (counter.type !== "Identifier") return "the stage function doesn't return its counter";
    bindings.state = scopes.variableOf(counter);
    if (bindings.state === undefined) return "the stage counter isn't a local";
    accepted.add(counter);
    const tailKind = returned.type === "UpdateExpression" ? (returned.prefix ? "pre" : "post") : "after";

    const branches: { test: Expression; body: Node }[] = [];
    let link: Node = chain;
    while (link.type === "IfStatement") {
        branches.push({ test: link.test, body: link.consequent });
        if (link.alternate === null) return "the stage chain has no final freeze";
        link = link.alternate;
    }
    const freeze = lookupExit(cx, link, method, bindings, accepted);
    if (freeze !== undefined) return freeze;
    const lookupFn = bindings.lookup === undefined ? undefined : localFunction(bindings.lookup, setupBody);
    const tableProblem = lookupFn === undefined ? "the lookup isn't a function local to the setup" : bindTable(cx, lookupFn, bindings, accepted);
    if (tableProblem !== undefined) return tableProblem;

    for (const statement of body.slice(0, -2)) {
        if (statement.type !== "IfStatement" || statement.alternate !== null) return "the stage function has other statements than its exits, chain and return";
        const guard = guardOf(cx, statement.test, bindings, accepted);
        if (typeof guard === "string") return guard;
        const exit = lookupExit(cx, statement.consequent, method, bindings, accepted);
        if (exit !== undefined) return exit;
    }
    const stages: { state: number; argument: number | undefined }[] = [];
    let bodyStep: number | undefined;
    for (const branch of branches) {
        const guard = guardOf(cx, branch.test, bindings, accepted);
        if (typeof guard === "string") return guard;
        if (guard.state === undefined) return "a stage branch isn't guarded by its counter";
        stages.push({ state: guard.state, argument: guard.argument });
        const step = stageBody(cx, branch.body, bindings, accepted);
        if (typeof step === "string") return step;
        if (bodyStep !== undefined && step !== bodyStep) return "the stage branches step the counter by different amounts";
        bodyStep = step;
    }
    if (bodyStep === undefined || bodyStep + (tailKind === "after" ? 0 : 1) <= 0) return "the stages don't step the counter";
    return { stages, bodyStep, tail: tailKind };
};

/** `{ [Q.m = L;] [if (true) { Q.m = L; }] return L(x); }` */
const lookupExit = (cx: DecoderContext, node: Node, method: string, bindings: Bindings, accepted: Set<Node>): string | undefined => {
    const { scopes } = cx;
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
};

const bindTable = (cx: DecoderContext, fn: Node, bindings: Bindings, accepted: Set<Node>): string | undefined => {
    const { scopes } = cx;
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
};

/** `R === c && x === d`, either order and side. */
const guardOf = (cx: DecoderContext, test: Expression, bindings: Bindings, accepted: Set<Node>): { state: number | undefined; argument: number | undefined } | string => {
    const { scopes } = cx;
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
};

const stageBody = (cx: DecoderContext, node: Node, bindings: Bindings, accepted: Set<Node>): number | string => {
    const { scopes } = cx;
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
        if (!shuffle(cx, e, bindings, accepted)) return "a stage body has a statement other than the table shuffle";
    }
    return step;
};

const isTable = (cx: DecoderContext, node: Node, bindings: Bindings, accepted: Set<Node>): boolean => {
    if (node.type !== "Identifier" || cx.scopes.variableOf(node) !== bindings.table) return false;
    accepted.add(node);
    return true;
};

/** `X.splice(a, b)` / `G.splice(X, a, b)` (relies on model 7: builtins intact). */
const splice = (cx: DecoderContext, node: Node, inner: (node: Node) => boolean): boolean => {
    if (node.type !== "CallExpression") return false;
    const { callee } = node;
    if (callee.type === "MemberExpression" && builtin(cx, "Array.prototype", propertyKey(callee)) === "splice") return twoNumbers(node.arguments) && inner(callee.object);
    const [receiver, ...rest] = node.arguments;
    return callAliasOf(cx, callee) === "Array.prototype.splice" && receiver !== undefined && twoNumbers(rest) && inner(receiver);
};

/**
 * `T.unshift.apply(T, T.splice(a, b).splice(c, d))` or its call-alias form: hands T to builtins only as their
 * receiver (relies on model 7: builtins intact).
 */
const shuffle = (cx: DecoderContext, node: Node, bindings: Bindings, accepted: Set<Node>): boolean => {
    if (node.type !== "CallExpression") return false;
    const table = (n: Node): boolean => isTable(cx, n, bindings, accepted);
    const spliced = (n: Node): boolean => splice(cx, n, (inner) => splice(cx, inner, table));
    const { callee } = node;
    if (callee.type === "MemberExpression" && builtin(cx, "Function.prototype", propertyKey(callee)) === "apply") {
        const unshift = callee.object;
        const [receiver, items] = node.arguments;
        return (
            node.arguments.length === 2 &&
            unshift.type === "MemberExpression" &&
            builtin(cx, "Array.prototype", propertyKey(unshift)) === "unshift" &&
            table(unshift.object) &&
            receiver !== undefined &&
            table(receiver) &&
            items !== undefined &&
            spliced(items)
        );
    }
    const [handout, receiver, items] = node.arguments;
    return (
        callAliasOf(cx, callee) === "Function.prototype.apply" &&
        node.arguments.length === 3 &&
        handout?.type === "CallExpression" &&
        handout.arguments.length === 0 &&
        callAliasOf(cx, handout.callee) === "Array.prototype.unshift" &&
        receiver !== undefined &&
        table(receiver) &&
        items !== undefined &&
        spliced(items)
    );
};

/** T is a string (only literals and `+=` write it) until the setup's top-level statement that splits it. */
const checkTable = (cx: DecoderContext, table: Variable, setup: FunctionNode, setupBody: readonly Statement[], accepted: ReadonlySet<Node>): string | undefined => {
    const { scopes } = cx;
    if (table.scope.block !== (setup as never)) return "the table isn't a local of the setup";
    const parents = parentsWithin(setup);
    /** By containing statement: positions don't tell, as earlier passes moved code. */
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
    const lastIndex = writes.reduce((highest, { index }) => Math.max(highest, index), Number.NEGATIVE_INFINITY);
    const last = writes.filter(({ index }) => index === lastIndex);
    const [final] = last;
    const write = final === undefined ? undefined : writeOf(final.identifier);
    const statement = setupBody[lastIndex];
    const value = write?.type === "AssignmentExpression" && write.operator === "=" ? write.right : write?.type === "VariableDeclarator" ? write.init : null;
    if (last.length !== 1 || write === undefined || statement === undefined || parents.get(write) !== statement || value === null || value === undefined || !splits(cx, value, table))
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
};

/** With `s` a string literal: a fresh array of strings (relies on model 7: builtins intact). */
const splits = (cx: DecoderContext, value: Node, table: Variable): boolean => {
    const { scopes } = cx;
    if (value.type !== "CallExpression") return false;
    const isTableName = (node: Node | undefined): boolean => node?.type === "Identifier" && scopes.variableOf(node) === table;
    const { callee } = value;
    if (callee.type === "MemberExpression" && builtin(cx, "String.prototype", propertyKey(callee)) === "split")
        return isTableName(callee.object) && value.arguments.length === 1 && isStringLiteral(value.arguments[0]);
    return callAliasOf(cx, callee) === "String.prototype.split" && value.arguments.length === 2 && isTableName(value.arguments[0]) && isStringLiteral(value.arguments[1]);
};

/** Whether a stage call with `argument` that gave `result` and left S in place leaves the counter past every guard. */
const settles = (template: Template, argument: Value | undefined, result: Value): boolean => {
    if (typeof argument !== "number" || !Number.isInteger(argument) || argument < 0 || argument >= 2 ** 32 - 1 || typeof result !== "number") return false;
    const highest = template.stages.reduce((most, stage) => Math.max(most, stage.state), Number.NEGATIVE_INFINITY);
    const before = result - template.bodyStep - (template.tail === "pre" ? 1 : 0);
    const after = before + template.bodyStep + (template.tail === "after" ? 0 : 1);
    return after > highest && template.stages.some((stage) => stage.state === before && (stage.argument === undefined || stage.argument === argument));
};

/**
 * Where a decoder settles: its settling call, the root statement it is in, the calls of it there known to come after
 * it, and the storage keys holding its holder (`G.k`, and copies `G.x = G.k` root statements make).
 */
export interface Settling {
    readonly call: CallExpression;
    readonly statement: Statement;
    readonly after: ReadonlySet<Node>;
    readonly holders: ReadonlySet<string>;
}

export interface DecoderProof {
    /** Targets (`JSON.stringify` of `[k, m]`) following the template: a call writes only state reachable through `G.k`. */
    readonly templated: ReadonlySet<string>;
    /**
     * Root builder statements of templated decoders built on the host (`buildHostDecoder`). Building one changes
     * nothing but objects it made: the interpreter writes only plain objects and arrays, and none existed before the
     * build (the storage function, root function closures and builtins it reads through are no such objects, and it
     * refuses writing their properties); it assigns only variables the run declared; every call it ran was of code it
     * interpreted under the same rules, or of a modelled builtin (model 7). The real build runs alike: its name probe
     * finds the one value given it, drawing only `Math.random` on the way (which leaves no state the program reads).
     */
    readonly hostBuilt: ReadonlySet<Node>;
    /** Wrapper keys of decoders the prelude settles: a later call is a lookup on the final table (see `settling`). */
    readonly settled: ReadonlySet<string>;
    /** The decoders' calls the prelude makes in its proven order, up to the one that settles them: their values. */
    readonly stageCalls: ReadonlyMap<Node, Value>;
    /** By settled target (its path, `\0`-joined). */
    readonly settling: ReadonlyMap<string, Settling>;
    /** A call of a settled decoder's wrapper `key` on its final table, on the host; then the reads `keys` on its result. */
    readonly lookup: (key: string, args: readonly Value[], keys?: readonly string[]) => Held;
}

/** For cleanup: stage calls of templated decoders only touch their own state. */
export const DECODER_PROOF = factKey<DecoderProof>("decoder proof");

/** A reference to `G` with the member chain on it: its static keys (`undefined` for computed ones). */
interface StorageChain {
    readonly keys: readonly (string | undefined)[];
    /** The outermost member of the chain (or `G`), its parent and the key it has there. */
    readonly node: Node;
    readonly parent: Node | null;
    readonly key: string | null;
    readonly write: boolean;
    readonly statement: Statement | undefined;
}

const storageChains = (runtime: RuntimeModel, matcher: StorageMatcher): StorageChain[] => {
    const chains: StorageChain[] = [];
    for (const statement of rootStatements(runtime.root)) {
        traverse(statement, {
            Identifier(path) {
                const node = path.node;
                if (!matcher.isStorage(node) || matcher.isAliasBinding(node) || (path.parent?.type === "FunctionDeclaration" && path.key === "id")) return;
                const keys: (string | undefined)[] = [];
                let outer = path as typeof path | NonNullable<typeof path.parentPath>;
                while (outer.parent?.type === "MemberExpression" && outer.key === "object" && outer.parentPath !== null) {
                    keys.push(propertyKey(outer.parent));
                    outer = outer.parentPath;
                }
                const write = outer.isWriteTarget() || (outer.parent?.type === "UnaryExpression" && outer.parent.operator === "delete");
                chains.push({ keys, node: outer.node, parent: outer.parent, key: outer.key, write, statement });
            },
        });
    }
    return chains;
};

/** The receiver argument of `G.k.m.apply(G.k, ...)`/`.call(G.k, ...)`: what `this` the target gets. */
const isReceiverOf = (node: Node, parent: Node | null, holderKeys: ReadonlySet<string>, method: string, isStorage: (node: Node) => boolean): boolean => {
    if (parent?.type !== "CallExpression" || parent.arguments[0] !== node) return false;
    const callee = memberPath(parent.callee);
    const [first, second, third] = callee?.keys ?? [];
    return callee !== undefined && isStorage(callee.root) && callee.keys.length === 3 && holderKeys.has(first ?? "") && second === method && (third === "apply" || third === "call");
};

/** Root statements `G.x = G.k` (also of copies), by the copy's key. */
const holderCopies = (runtime: RuntimeModel, matcher: StorageMatcher, key: string): Map<string, Statement> => {
    const copies = new Map<string, Statement>();
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") continue;
        const { left, right } = statement.expression;
        const from = right.type === "MemberExpression" && matcher.isStorage(right.object) ? propertyKey(right) : undefined;
        const to = left.type === "MemberExpression" && matcher.isStorage(left.object) ? propertyKey(left) : undefined;
        if (from !== undefined && to !== undefined && (from === key || copies.has(from))) copies.set(to, statement);
    }
    return copies;
};

/**
 * How the program uses the holder `G.k` (and its `copies`): written only by its builder (and the copies), handed on
 * only as the receiver of `G.k.m.apply`, its method `G.k.m` only called (directly or by `apply`/`call`), read under
 * `typeof`, or read as a value (`valueReads`: S and L are the same lookup once it settled, but not the same function).
 * No other method of it is called with it as `this`, and no computed read of `G` that may select it (key sets, as
 * `cleanup` judges computed reads) reads or calls its members.
 */
const holderUses = (
    cx: { runtime: RuntimeModel; matcher: StorageMatcher; scopes: ScopeInfo },
    chains: readonly StorageChain[],
    target: readonly [string, string],
    builder: Statement,
    copies: ReadonlyMap<string, Statement>,
    keySetOf: (property: Node, statement: Statement | undefined) => KeySet | undefined
): { valueReads: Node[] } | string => {
    const { runtime, matcher } = cx;
    const [key, method] = target;
    const name = `${runtime.storage}.${key}`;
    const holderKeys = new Set([key, ...copies.keys()]);
    const valueReads: Node[] = [];
    for (const chain of chains) {
        const [first, second, third] = chain.keys;
        const { node, parent } = chain;
        if (first === undefined || !holderKeys.has(first)) continue;
        const depth = chain.keys.length;
        if (depth === 1) {
            if (chain.write) {
                if (node === assignedTarget(first === key ? builder : copies.get(first))) continue;
                return `${runtime.storage}.${first} is written outside its builder`;
            }
            if (
                parent?.type === "AssignmentExpression" &&
                chain.key === "right" &&
                [...copies.values()].some((statement) => statement.type === "ExpressionStatement" && statement.expression === parent)
            )
                continue;
            if (isReceiverOf(node, parent, holderKeys, method, matcher.isStorage)) continue;
            return `the holder ${name} is used as a value`;
        }
        if (second === undefined) return `a computed key of the holder ${name} is used`;
        if (second !== method) {
            if (depth === 2 && parent?.type === "CallExpression" && chain.key === "callee") return `${runtime.storage}.${first}.${second}() runs with the holder as this`;
            continue;
        }
        if (chain.write) return `${runtime.storage}.${first}.${method} is written`;
        const called = parent?.type === "CallExpression" && chain.key === "callee";
        if (depth === 2 && (called || (parent?.type === "UnaryExpression" && parent.operator === "typeof"))) continue;
        if (depth === 3 && (third === "apply" || third === "call") && called) continue;
        valueReads.push(node);
    }
    // Computed reads of `G` that may select the holder: but for a call of what one selects (the holder isn't callable,
    // so none of its methods runs) and reads of its other static keys, a key set must rule the holder out.
    for (const chain of chains) {
        const [first, next] = chain.keys;
        if (chain.keys.length === 0 || first !== undefined) continue;
        const called = chain.keys.length === 1 && chain.parent?.type === "CallExpression" && chain.key === "callee";
        const methodCall = chain.keys.length === 2 && chain.parent?.type === "CallExpression" && chain.key === "callee";
        if (called || (chain.keys.length >= 2 && next !== undefined && next !== method && !methodCall)) continue;
        const member = findComputed(chain.node, chain.keys.length);
        const keys = member === undefined ? undefined : keySetOf(member.property, chain.statement);
        if (keys === undefined || [...holderKeys].some((holder) => mayName(keys, holder))) return `a computed read of ${runtime.storage} may give the holder ${name}`;
    }
    return { valueReads };
};

/** The innermost member of a chain `depth` members deep ending at `outer` (the one on `G` itself). */
const findComputed = (outer: Node, depth: number): (Node & { type: "MemberExpression" }) | undefined => {
    let member: Node = outer;
    for (let i = 1; i < depth; i++) {
        if (member.type !== "MemberExpression") return undefined;
        member = member.object;
    }
    return member.type === "MemberExpression" ? member : undefined;
};

/**
 * Which templated string decoders the prelude settles, and their calls' values, on the host.
 *
 * Proof, per decoder `G.k.m`. The template makes `S` write only `T`, `R` (stage paths) and `Q.m` (lookup exits, only
 * ever to `L`), and return `L(x)`, which only reads `T[x]`, on every path but the stage paths; a stage path requires
 * `R === c` for one of the stage guards `c`, and `R` only grows. So once `R` exceeds every guard (the decoder is
 * settled), S and L are both `x => T[x]` with `T` fixed: T's array came fresh from `split` and only ever went to
 * builtins as their receiver (the shuffles), so nothing else holds it; the stage paths, the only code writing `T`
 * after the setup, can't run again. That holds wherever S or L got to. (Relies on model 7: builtins intact. `split`,
 * `splice`, `unshift` and `apply`, reached by name, through the aliases the runtime added or through its call aliases,
 * are the standard ones: they return fresh arrays and keep no receiver.)
 *
 * When that happens: its one root builder `G.k = ...` is built on the host (`buildHostDecoder`). Then the root
 * statements after it run in place (`statementOrder`; model 1: the prelude runs to completion, and no callback runs
 * before it did): nothing they do may call it or run code that could, but its calls made exactly once in that order
 * with constant arguments, through its wrappers (defined by then, not rewritten since) or of `G.k.m`. Those are made
 * on the host in that order until one leaves `S` in place with an integer argument and a number result that puts `R`
 * past every guard (`settles`: `L`'s `T[x]` gives the table's strings or `undefined`, model 7: no index properties on
 * the builtin prototypes); their values are exact, and they keep running (`stageCalls`). Calls that may run before it
 * settles but aren't in that order (in code the walk stops at, or in functions made earlier) can't be told: the walk
 * stops at the first, and the decoder isn't settled. From the settling call on every call of it is a lookup on the
 * final table (`lookup`), whatever its order. Dropping one may drop the call that freezes `G.k.m` to `L`: so the holder
 * must be used only in ways that can't tell `S` and `L` apart (`holderUses`), but for reads of `G.k.m` the walk passed
 * before the settling call (they get `S`). That `G.k` and `G.k.m` stay so after the prelude is the caller's to check
 * (`effects.ts`: only the builder writes them).
 */
export const proveDecoders = (runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, log: PassLog): DecoderProof => {
    const settled = new Set<string>();
    const templated = new Set<string>();
    const hostBuilt = new Set<Node>();
    const stageCalls = new Map<Node, Value>();
    const settling = new Map<string, Settling>();
    const decoders = new Map<string, HostDecoder>();
    const { storage, wrappers, aliases, callAliases } = runtime;
    const cx: DecoderContext = { scopes, matcher, callAliases, originals: new Map(aliases.map((alias) => [`${pathName(alias.owner)}.${alias.alias}`, alias.original])) };
    const host = { runtime, matcher, scopes };
    const root = rootStatements(runtime.root);

    const targets = new Map<string, readonly [string, string]>();
    const keysOf = new Map<string, string[]>();
    for (const wrapper of wrappers.values()) {
        if (wrapper.target.length !== 2) continue;
        const id = JSON.stringify(wrapper.target);
        targets.set(id, wrapper.target as [string, string]);
        keysOf.set(id, [...(keysOf.get(id) ?? []), wrapper.key]);
    }
    const assigned = new Map<string, Statement[]>();
    for (const statement of root) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const target = statement.expression.left;
        const key = target.type === "MemberExpression" && matcher.isStorage(target.object) ? propertyKey(target) : undefined;
        if (key !== undefined) assigned.set(key, [...(assigned.get(key) ?? []), statement]);
    }
    let chains: StorageChain[] | undefined;
    const keySetsByStatement = new Map<Statement, (key: Expression) => KeySet | undefined>();
    const keySetOf = (property: Node, statement: Statement | undefined): KeySet | undefined => {
        if (statement === undefined) return undefined;
        let of = keySetsByStatement.get(statement);
        if (of === undefined) {
            of = keySets(scopes, parentsWithin(statement), keySetAliases(host));
            keySetsByStatement.set(statement, of);
        }
        return of(property as Expression);
    };

    for (const [id, target] of targets) {
        const [key, method] = target;
        const name = `${storage}.${target.join(".")}`;
        const statements = assigned.get(key) ?? [];
        const [statement] = statements;
        if (statement === undefined || statements.length !== 1) {
            log.debug(
                `${name}: not a string decoder of the known template, ${statements.length === 0 ? `no root statement assigns ${storage}.${key}` : `${statements.length} root statements assign ${storage}.${key}`}`
            );
            continue;
        }
        const template = templateOf(cx, statement, method);
        if (typeof template === "string") {
            log.debug(`${name}: not a string decoder of the known template, ${template}`, statement);
            continue;
        }
        templated.add(id);
        const built = buildHostDecoder(host, statement, method);
        if (typeof built === "string") {
            log.debug(`decoder ${name}: not proven, ${built}`, statement);
            continue;
        }
        const { decoder } = built;
        hostBuilt.add(statement);
        log.debug(`decoder ${name}: built on the host; ${built.probe}`, statement);
        // The prelude's calls of it, in order, until one settles it; then until one freezes it.
        const copies = holderCopies(runtime, matcher, key);
        const wrapperKeys = new Set(keysOf.get(id));
        const holderKeys = new Set([key, ...copies.keys()]);
        const definitions = new Map([...wrapperKeys].map((wrapperKey) => [wrapperKey, wrappers.get(wrapperKey)?.definition]));
        const seen = new Set<Node>();
        const order: OrderContext = {
            scopes,
            matcher,
            runtime,
            decoderCall: (call: CallExpression) => {
                const callee = call.callee;
                if (callee.type === "MemberExpression" && matcher.isStorage(callee.object) && wrapperKeys.has(propertyKey(callee) ?? "")) return true;
                const path = memberPath(callee);
                return path !== undefined && matcher.isStorage(path.root) && path.keys.length === 2 && holderKeys.has(path.keys[0] as string) && path.keys[1] === method;
            },
            holder: (slot) => holderKeys.has(slot),
            guarded: (slot, write) => {
                if (holderKeys.has(slot)) return write === assignedTarget(copies.get(slot)) ? undefined : `it writes ${storage}.${slot}, which holds the decoder`;
                const definition = definitions.get(slot);
                return definition === undefined || write === assignedTarget(definition) ? undefined : `it writes ${storage}.${slot}, a wrapper of the decoder`;
            },
            seen,
        };
        const start = root.indexOf(statement);
        let settledBy: { statement: Statement; call: CallExpression } | undefined;
        let freeze: CallExpression | undefined;
        const after = new Set<Node>();
        let why: string | undefined;
        let replayed = 0;
        let seenBefore: ReadonlySet<Node> = new Set();
        statements: for (const [index, current] of root.entries()) {
            if (index <= start) continue;
            const walk = statementOrder(order, current);
            for (let step = walk.next(); step.done !== true;) {
                const event = step.value;
                if (event.kind === "stop") {
                    if (settledBy === undefined) why = `root statement ${index} ${event.reason} before it settles`;
                    break statements;
                }
                const wrapperKey = event.call.callee.type === "MemberExpression" && wrapperKeys.has(propertyKey(event.call.callee) ?? "") ? propertyKey(event.call.callee) : undefined;
                const definedAt = wrapperKey === undefined ? -1 : root.indexOf(definitions.get(wrapperKey) as Statement);
                if (wrapperKey !== undefined && !(definedAt >= 0 && definedAt < index)) {
                    why = `root statement ${index} calls ${storage}.${wrapperKey} before it is defined`;
                    break statements;
                }
                const unfrozen = decoder.unfrozen;
                const answer = decoder.call(event.args);
                if (!answer.ok || isObject(answer.value)) {
                    why = `its call at root statement ${index} ${answer.ok ? "gives an object" : `refused on the host: ${answer.reason}`}`;
                    break statements;
                }
                const value = answer.value as Value;
                if (settledBy === undefined) {
                    stageCalls.set(event.call, value);
                    replayed++;
                    if (unfrozen && decoder.unfrozen && settles(template, event.args[0], value)) {
                        settledBy = { statement: current, call: event.call };
                        seenBefore = new Set(seen);
                    }
                } else if (unfrozen && !decoder.unfrozen) {
                    // The call that freezes it to `L`: it keeps running, as the stage calls do.
                    stageCalls.set(event.call, value);
                    freeze = event.call;
                    break statements;
                } else after.add(event.call);
                step = walk.next(value);
            }
        }
        if (settledBy === undefined) {
            log.debug(`decoder ${name}: not proven, ${why ?? "no prelude call settles it"}${replayed > 0 ? ` (its ${replayed} call(s) before that keep running with their values)` : ""}`, statement);
            continue;
        }
        chains ??= storageChains(runtime, matcher);
        const uses = holderUses(host, chains, target, statement, copies, keySetOf);
        if (typeof uses === "string") {
            log.debug(`decoder ${name}: not proven, ${uses}`, statement);
            continue;
        }
        // Where no known call froze it, which later call does isn't known: then nothing may tell S from L but where it is S.
        const wrapperStatements = [...definitions.values()];
        const early =
            freeze === undefined
                ? uses.valueReads.find((read) => !seenBefore.has(read) && !wrapperStatements.some((definition) => definition !== undefined && within(scopes, definition, read)))
                : undefined;
        if (early !== undefined) {
            log.debug(`decoder ${name}: not proven, ${name} is read as a value where it may be either its stage function or its lookup`, early);
            continue;
        }
        for (const wrapperKey of wrapperKeys) settled.add(wrapperKey);
        settling.set(target.join("\u0000"), { call: settledBy.call, statement: settledBy.statement, after, holders: holderKeys });
        decoders.set(id, decoder);
        log.debug(
            `decoder ${name}: settled by the prelude's call ${replayed} of it, at root statement ${root.indexOf(settledBy.statement)}${freeze === undefined ? "" : ", frozen by a later one"}; later calls are lookups on its final table`,
            settledBy.call
        );
    }
    if (settled.size > 0) log.info(`${settled.size} wrapper(s) of string decoders proven settled during the prelude, on the host`);
    const lookup = (wrapperKey: string, args: readonly Value[], keys: readonly string[] = []): Held => {
        const target = wrappers.get(wrapperKey)?.target;
        const decoder = target === undefined ? undefined : decoders.get(JSON.stringify(target));
        return decoder === undefined ? { ok: false, reason: "not a settled decoder", steps: 0, exhausted: false } : decoder.call(args, keys);
    };
    return { templated, hostBuilt, settled, stageCalls, settling, lookup };
};

/** Whether `inner` is inside `outer`, by the parents of the last scope walk (positions don't tell: passes moved code). */
const within = (scopes: ScopeInfo, outer: Node, inner: Node): boolean => {
    for (let node: Node | undefined = inner; node !== undefined; node = scopes.parentOf(node)) if (node === outer) return true;
    return false;
};

/** The target of a statement `t = v`. */
const assignedTarget = (node: Node | undefined): Node | undefined => (node?.type === "ExpressionStatement" && node.expression.type === "AssignmentExpression" ? node.expression.left : undefined);
