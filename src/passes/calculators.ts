import type { CallExpression, Expression, Function as FunctionNode, Node, Statement } from "../core/ast.js";
import { isFunctionNode, isIndexKey, memberPath, propertyKey } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import { globalsEnv } from "../core/constants.js";
import type { EvaluateEnv, Value } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Path } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { bodyOf, builderOf, definitionOf } from "./emulate/builders.js";
import type { StorageEffects } from "./emulate/effects.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import type { RuntimeModel } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import { rootStatements } from "./emulate/storage.js";

/** One `case` of a calculation: its label, and the expression it computes (or why that can't be used). */
interface Case {
    readonly label: Value;
    readonly formula: Expression;
    readonly problem: string | undefined;
}

/**
 * A calculator object `G.k`: a selector method that stores its argument in the builder's state variable, and a
 * calculation that computes the case the state selects from its arguments.
 */
interface Calculator {
    readonly path: PropertyPath;
    readonly name: string;
    readonly selector: string;
    readonly calculation: string;
    readonly cases: readonly Case[];
    /** The calculation's `var a = arguments` local: `a[i]` in a formula is the call's argument `i`. */
    readonly args: Variable;
    readonly definition: Statement;
}

/** Where a node sits: its parent, and the field (and index, for lists) of the parent holding it. */
interface Place {
    readonly parent: Node;
    readonly key: string;
    readonly index: number | null;
}

/** A call of a calculator's selector or calculation, directly (`G.k.m(...)`) or through a wrapper (`G.w(...)`). */
interface Site {
    readonly call: CallExpression;
    readonly calculator: Calculator;
    readonly role: "selector" | "calculation";
    /** The reference to `G` the callee starts from. */
    readonly reference: Node;
    readonly wrapper: string | undefined;
    /** The call's places, from its own up to the function it is in. */
    readonly places: readonly Place[];
}

type Refusal = { readonly ok: false; readonly reason: string; readonly node: Node };

const refusal = (reason: string, node: Node): Refusal => ({ ok: false, reason, node });

const GETTER = "a property read (possible getter)";
const GLOBAL_READ = "a global read (possible getter)";

/** `void 0`: undefined, whatever the name `undefined` is bound to there. */
const voidZero = (position: Node): Expression => at<Expression>({ type: "UnaryExpression", operator: "void", prefix: true, argument: valueToNode(0, position) }, position);

const startsWith = (keys: readonly (string | undefined)[], prefix: PropertyPath): boolean => keys.length >= prefix.length && prefix.every((key, i) => key === keys[i]);

/** The state variable a selector method `function (p) { I = p; }` writes, and the identifier it writes through. */
const stateWrittenBy = (fn: FunctionNode, scopes: ScopeInfo): { variable: Variable; write: Node } | undefined => {
    const [param] = fn.params;
    const [only] = bodyOf(fn);
    if (fn.async || fn.generator || fn.params.length !== 1 || param?.type !== "Identifier" || bodyOf(fn).length !== 1 || only?.type !== "ExpressionStatement") return undefined;
    const set = only.expression;
    if (set.type !== "AssignmentExpression" || set.operator !== "=" || set.left.type !== "Identifier" || set.right.type !== "Identifier") return undefined;
    const variable = scopes.variableOf(set.left);
    const given = scopes.variableOf(param);
    return variable === undefined || given === undefined || variable === given || scopes.variableOf(set.right) !== given ? undefined : { variable, write: set.left };
};

/** Why a case's expression isn't a formula over the calculation's arguments: literals, `a[i]` and operators. */
const formulaProblem = (node: Node, args: Variable, scopes: ScopeInfo): string | undefined => {
    switch (node.type) {
        case "Literal":
            return undefined;
        case "MemberExpression":
            return node.computed && node.object.type === "Identifier" && scopes.variableOf(node.object) === args && node.property.type === "Literal" && isIndexKey(propertyKey(node) ?? "")
                ? undefined
                : "it reads something other than an argument";
        case "UnaryExpression":
            return node.operator === "delete" ? "it deletes" : formulaProblem(node.argument, args, scopes);
        case "BinaryExpression":
            return node.left.type === "PrivateIdentifier" ? "it tests a private name" : (formulaProblem(node.left, args, scopes) ?? formulaProblem(node.right, args, scopes));
        case "LogicalExpression":
            return formulaProblem(node.left, args, scopes) ?? formulaProblem(node.right, args, scopes);
        case "ConditionalExpression":
            return formulaProblem(node.test, args, scopes) ?? formulaProblem(node.consequent, args, scopes) ?? formulaProblem(node.alternate, args, scopes);
        default:
            return `it contains a ${node.type}`;
    }
};

/**
 * The cases of a calculation `function () { var r, a = arguments; switch (I) { case L: r = <formula>; break; ... } return r; }`
 * (one declaration or two, either order; the last case may end without `break`). Every label is a distinct constant
 * and every case sets `r` and leaves the switch, so a call returns the formula of the case whose label is `=== I`, or
 * `r`'s initial undefined when none is.
 */
const calculationOf = (fn: FunctionNode, state: Variable, scopes: ScopeInfo, env: EvaluateEnv): { cases: Case[]; args: Variable } | Refusal => {
    if (fn.async || fn.generator || fn.params.length > 0) return refusal("the calculation takes parameters, or is async or a generator", fn);
    const statements = bodyOf(fn);
    let result: Variable | undefined;
    let args: Variable | undefined;
    let i = 0;
    for (let statement = statements[0]; statement?.type === "VariableDeclaration"; statement = statements[++i]) {
        if (statement.kind !== "var") return refusal("the calculation declares a lexical local", statement);
        for (const declarator of statement.declarations) {
            const variable = declarator.id.type === "Identifier" ? scopes.variableOf(declarator.id) : undefined;
            const init = declarator.init;
            const ownArguments = init?.type === "Identifier" && init.name === "arguments" ? scopes.variableOf(init) : undefined;
            if (variable !== undefined && init === null && result === undefined) result = variable;
            else if (variable !== undefined && ownArguments !== undefined && ownArguments.defs.length === 0 && (ownArguments.scope.block as unknown as Node) === fn && args === undefined)
                args = variable;
            else return refusal("the calculation declares other locals than its result and its arguments", declarator);
        }
    }
    const [choice, exit] = statements.slice(i);
    if (result === undefined || args === undefined || result === args || statements.length !== i + 2 || choice?.type !== "SwitchStatement" || exit?.type !== "ReturnStatement") {
        return refusal("the calculation isn't `var r, a = arguments; switch (state) {...} return r;`", fn);
    }
    const discriminant = choice.discriminant;
    if (discriminant.type !== "Identifier" || scopes.variableOf(discriminant) !== state) return refusal("the calculation doesn't switch on the selector's state", discriminant);
    if (exit.argument?.type !== "Identifier" || scopes.variableOf(exit.argument) !== result) return refusal("the calculation doesn't return its result", exit);

    const cases: Case[] = [];
    for (const [index, clause] of choice.cases.entries()) {
        if (clause.test === null) return refusal("the calculation has a default case", clause);
        const label = evaluate(clause.test, env);
        if (!label.ok) return refusal("a case label isn't a constant", clause.test);
        if (cases.some((known) => known.label === label.value)) return refusal(`the case label ${String(label.value)} repeats`, clause.test);
        const [set, jump, ...rest] = clause.consequent;
        const ends = jump === undefined ? index === choice.cases.length - 1 : jump.type === "BreakStatement" && jump.label === null;
        const assignment = set?.type === "ExpressionStatement" ? set.expression : undefined;
        if (
            assignment?.type !== "AssignmentExpression" ||
            assignment.operator !== "=" ||
            assignment.left.type !== "Identifier" ||
            scopes.variableOf(assignment.left) !== result ||
            !ends ||
            rest.length > 0
        ) {
            return refusal(`case ${String(label.value)} doesn't just set the result and leave the switch`, clause);
        }
        cases.push({ label: label.value, formula: assignment.right, problem: formulaProblem(assignment.right, args, scopes) });
    }
    return { cases, args };
};

/** Cheap shape test before the full recognition (which logs its refusals): the builder returns a method with a switch. */
const looksLikeCalculator = (iife: FunctionNode): boolean => {
    const returned = bodyOf(iife).at(-1);
    return (
        returned?.type === "ReturnStatement" &&
        returned.argument?.type === "ObjectExpression" &&
        returned.argument.properties.some((p) => p.type === "Property" && p.value.type === "FunctionExpression" && bodyOf(p.value).some((s) => s.type === "SwitchStatement"))
    );
};

/**
 * The calculator `iife` builds: `function (I) { return { sel: function (p) { I = p; }, calc: function () {...} }; }`,
 * with `I` the builder's parameter or a local it declares. Nothing else is in the builder, the selector is that one
 * assignment, and the calculation's only identifiers besides its own locals are the switch's `I` (labels are constants,
 * formulas read only its arguments): so `I` is written only by the selector and read only by the switch, and a
 * calculation computes the case the latest selector call chose.
 */
const calculatorOf = (iife: FunctionNode, scopes: ScopeInfo, env: EvaluateEnv): Omit<Calculator, "path" | "name" | "definition"> | Refusal => {
    const builder = builderOf(iife, scopes);
    if (typeof builder === "string") return refusal(builder, iife);
    const body = bodyOf(iife);
    const returned = body.at(-1);
    if (returned?.type !== "ReturnStatement" || returned.argument?.type !== "ObjectExpression") return refusal("its builder doesn't end by returning an object literal", iife);
    if (!body.slice(0, -1).every((s) => s.type === "VariableDeclaration" && s.kind === "var" && s.declarations.every((d) => d.id.type === "Identifier" && d.init === null))) {
        return refusal("its builder does more than declare locals and return the object", iife);
    }
    if (returned.argument.properties.length !== 2 || builder.methods.size !== 2) return refusal("its object has other properties than a selector and a calculation", returned.argument);
    const methods = [...builder.methods];
    const selected = methods.map(([name, fn]) => ({ name, fn, state: stateWrittenBy(fn, scopes) }));
    const selector = selected.find((m) => m.state !== undefined);
    const calculation = selected.find((m) => m.state === undefined);
    if (selector?.state === undefined || calculation === undefined) return refusal("it has no selector `function (p) { I = p; }` next to a calculation", returned.argument);
    const { variable: state, write } = selector.state;
    if ((state.scope.block as unknown as Node) !== iife || state.defs.length !== 1) return refusal("the selector's state isn't a parameter or local of the builder", write);
    const shape = calculationOf(calculation.fn, state, scopes, env);
    if ("ok" in shape) return shape;
    return { selector: selector.name, calculation: calculation.name, cases: shape.cases, args: shape.args };
};

/** The function `node`'s code directly belongs to (`undefined` for the runtime root's top level), or `null` outside the root. */
const enclosingFunction = (places: readonly Place[], root: Node): Node | undefined | null => {
    for (const { parent } of places) if (isFunctionNode(parent)) return parent === root ? undefined : parent;
    return root.type === "Program" ? undefined : null;
};

/** The places of `path`'s node, up to its function (inclusive) or the program. */
const placesOf = (path: Path): Place[] => {
    const places: Place[] = [];
    for (let p: Path | null = path; p !== null && p.parent !== null && p.key !== null; p = p.parentPath) {
        places.push({ parent: p.parent, key: p.key, index: p.index });
        if (isFunctionNode(p.parent)) break;
    }
    return places;
};

/**
 * Calculator objects: `G.k.sel(3); x = G.k.calc(a, 7);` computes case 3 of the calculation's switch with `a` and 7 as
 * its arguments. Each calculation whose selector value is known becomes that case's expression, the arguments put in
 * (`a - 7`); constants then fold in simplify.
 *
 * Proof per calculation:
 * - the calculator (`calculatorOf`): built once by the prelude (`definitionOf`), its state written only by the selector
 *   and read only by the calculation's switch; `G.k.sel`, `G.k.calc` and the wrappers used hold the snapshot's methods
 *   when the call runs (one prelude write, data properties, `staleAt`);
 * - the selector value: the nearest selector call before the calculation in evaluation order, in the same function and
 *   on every path to it, with a constant argument, and no explicit code between the two (a call, `new`, a store that
 *   may hit a setter); getters and conversions there run code that doesn't use the calculator (model 8)
 *   (`selectorBefore`): so the state is that constant when the calculation reads it;
 * - the arguments: constants, safe locals and slot reads (`substitutable`): evaluating them has no effect, can't
 *   throw, and gives the same value in the case's expression, which keeps its structure. Model 8 doesn't cover a
 *   getter argument (it may have effects of its own, which dropping or moving it would change), nor conversions inside
 *   the case's expression (they run in the calculation, and may change a local a later argument reads): so a
 *   non-constant argument is only put where no conversion that could run code comes before it (`orderProblem`), and
 *   conversions still happen after every argument is read, in the same order. `a[i]` beyond the arguments is
 *   undefined (relies on model 7: builtins intact, so `Object.prototype` has no index accessors).
 * - a call through a wrapper applies the target with `Function.prototype.apply` (relies on model 7: builtins intact).
 *
 * Selector calls then only matter to calculations that remain. One goes when the next selector call overwrites its
 * value before anything can read it (`overwrittenAfter`: only quiet code in between, on every path). A calculation
 * whose selector call is proven (kept only for its arguments) reads exactly that call's value, whatever other code did
 * (model 8): so when every calculation that may run after the prelude is replaced or has a proven selector call, the
 * state is read after the prelude only by those calls' values, unless something else reaches the calculator: a
 * reference other than a call or its standard wrapper, or a computed `G[x]` access whose value may reach code running
 * after the prelude (`computedAccessKeeps`). Then every other selector call made after the prelude goes; the prelude's
 * own stay (its remaining calculations may read them).
 */
export const calculators: Pass = {
    name: "calculators",
    description: "Replace calculations of the runtime's calculator objects with the selected case's expression",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.guest.broken !== undefined) {
            log.info("no usable runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
        const env = globalsEnv(scopes);
        const found = recognize(runtime, matcher.isStorage, effects, scopes, env, log);
        if (found.length === 0) {
            log.info("no calculator objects");
            return { changed: 0 };
        }
        return new CalculatorRewrite(program, runtime, matcher.isStorage, effects, scopes, env, log, found).run();
    },
};

/** Calculators the prelude builds, each checked against the snapshot. */
const recognize = (runtime: RuntimeModel, isStorage: (node: Node) => boolean, effects: StorageEffects, scopes: ScopeInfo, env: EvaluateEnv, log: PassContext["log"]): Calculator[] => {
    const found: Calculator[] = [];
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const { left, right } = statement.expression;
        if (left.type !== "MemberExpression" || right.type !== "CallExpression" || right.callee.type !== "FunctionExpression" || !looksLikeCalculator(right.callee)) continue;
        const target = memberPath(left);
        if (target === undefined || !isStorage(target.root)) continue;
        const keys = target.keys;
        const name = `${runtime.storage}.${keys.join(".")}`;
        const definition = definitionOf(runtime, isStorage, keys);
        if (typeof definition === "string" || definition.statement !== statement) {
            log.debug(`${name} is no calculator: ${typeof definition === "string" ? definition : "it isn't the prelude's only definition"}`, statement);
            continue;
        }
        const shape = calculatorOf(definition.iife, scopes, env);
        if ("ok" in shape) {
            log.debug(`${name} is no calculator: ${shape.reason}`, shape.node);
            continue;
        }
        const unsure = [shape.selector, shape.calculation].find((method) => {
            const info = runtime.guest.inspect([...keys, method]);
            return info === undefined || !info.data || info.type !== "function" || effects.preludeWritesTo([...keys, method]) !== 1;
        });
        if (unsure !== undefined) {
            log.debug(`${name} looks like a calculator, but the snapshot's ${name}.${unsure} may not be the method its builder made (more prelude writes, or an accessor)`, statement);
            continue;
        }
        log.debug(`${name} is a calculator: ${name}.${shape.selector}(n) selects one of ${shape.cases.length} case(s) ${name}.${shape.calculation}(...) computes`, statement);
        found.push({ ...shape, path: keys, name, definition: statement });
    }
    return found;
};

/** Outcome of the search for the selector call a calculation follows. */
type Search = { readonly kind: "found"; readonly selector: Site } | { readonly kind: "stop"; readonly reason: string; readonly node: Node };

/** A calculation's replacement, decided before anything is rewritten. */
interface Resolution {
    readonly site: Site;
    readonly selected: Case | undefined;
    readonly args: readonly Expression[];
}

/** One run of the pass over the program: sites, decisions, rewrite. */
class CalculatorRewrite {
    readonly #sites = new Map<CallExpression, Site>();
    /** Per calculator, the first reference that isn't a call of its methods or a wrapper of one. */
    readonly #escapes = new Map<Calculator, Node>();
    /** Computed `G[x]` accesses (not writes), with their places. */
    readonly #computed: { member: Node; places: Place[] }[] = [];
    /** Variables some reference uses other than as `S[index]`. */
    readonly #unslotted = new Set<Variable>();
    readonly #slotArrays = new Map<Variable, boolean>();
    #cloned = 0;
    /** Per function: whether running it can't reach a selector call (see `#cannotReachSelector`). */
    readonly #isolated = new Map<Node, boolean>();
    /** Functions assumed by the running outermost `#cannotReachSelector` check. */
    #provisional: Node[] | undefined;

    constructor(
        readonly program: Node,
        readonly runtime: RuntimeModel,
        readonly isStorage: (node: Node) => boolean,
        readonly effects: StorageEffects,
        readonly scopes: ScopeInfo,
        readonly env: EvaluateEnv,
        readonly log: PassContext["log"],
        readonly found: readonly Calculator[]
    ) {}

    run(): PassResult {
        this.#collect();
        const counts = { calculators: this.found.length, resolved: 0, refused: 0, selectorsRemoved: 0, selectorsKept: 0 };
        const reasons = new Map<string, number>();
        const resolutions: Resolution[] = [];
        /** Calculators with a calculation that may run after the prelude and has no proven selector call. */
        const unproven = new Set<Calculator>();
        /** Calculators with a calculation that stays and may run in the prelude: it may read any selector call made there. */
        const preludeReaders = new Set<Calculator>();
        /** The proven selector calls of calculations that stay and may run after the prelude: what they read. */
        const read = new Set<CallExpression>();
        for (const site of this.#sites.values()) {
            if (site.role !== "calculation") continue;
            const resolution = this.#resolve(site);
            if ("ok" in resolution) {
                counts.refused++;
                const category = resolution.reason.split(":")[0] as string;
                reasons.set(category, (reasons.get(category) ?? 0) + 1);
                this.log.debug(`${site.calculator.name}: calculation kept: ${resolution.reason}`, resolution.node);
                if (!this.effects.runsAfterPrelude(site.reference)) {
                    preludeReaders.add(site.calculator);
                    continue;
                }
                if (resolution.selector === undefined) unproven.add(site.calculator);
                else read.add(resolution.selector.call);
                continue;
            }
            resolutions.push(resolution);
        }

        // Selector calls that go: those whose value the next selector call overwrites before anything reads it; and,
        // made after the prelude, those no calculation reads. A calculation whose selector call is proven reads exactly
        // that call's value (model 8), so when every calculation that may run after the prelude has one, the state is
        // read after the prelude only at those calculations: every other selector call made after the prelude is dead.
        const computedKeeps = this.#computedAccessKeeps();
        const resolved = new Map<Node, Resolution>(resolutions.map((resolution) => [resolution.site.call, resolution]));
        const removable = new Set<CallExpression>();
        for (const calculator of this.found) {
            const escape = this.#escapes.get(calculator);
            const keep =
                escape !== undefined
                    ? { reason: "a reference other than a call of its methods reaches it", node: escape }
                    : (computedKeeps ?? (unproven.has(calculator) ? { reason: "a calculation that may run after the prelude has no proven selector call", node: calculator.definition } : undefined));
            if (keep === undefined) this.log.debug(`${calculator.name}: after the prelude, only the selector calls of the calculations that stay are read`, calculator.definition);
            else this.log.debug(`${calculator.name}: selector calls stay unless overwritten before a read: ${keep.reason}`, keep.node);
            for (const site of this.#sites.values()) {
                if (site.calculator !== calculator || site.role !== "selector") continue;
                if (!site.call.arguments.every((arg) => arg.type !== "SpreadElement" && this.#substitutable(arg) === undefined))
                    this.log.debug("selector call kept: an argument may have effects", site.call);
                else if (read.has(site.call)) this.log.debug("selector call kept: a calculation that stays reads its value", site.call);
                else if (this.#overwrittenAfter(site, resolved)) {
                    this.log.debug("selector call removed: the next selector call overwrites its value before anything can read it", site.call);
                    removable.add(site.call);
                } else if (keep !== undefined) this.log.debug("selector call kept: a calculation may read its value", site.call);
                else if (!this.effects.runsAfterPrelude(site.reference) && preludeReaders.has(calculator))
                    this.log.debug("selector call kept: it runs in the prelude, where a calculation that stays may read it", site.call);
                else removable.add(site.call);
            }
        }

        for (const resolution of resolutions) {
            this.log.debug(
                `${resolution.site.calculator.name}: calculation resolved (case ${resolution.selected === undefined ? "none: undefined" : String(resolution.selected.label)})`,
                resolution.site.call
            );
        }
        counts.resolved = resolutions.length;
        counts.selectorsRemoved = this.#rewrite(resolved, removable);
        counts.selectorsKept = [...this.#sites.values()].filter((site) => site.role === "selector").length - counts.selectorsRemoved;

        const refusals = [...reasons].map(([reason, n]) => `${reason} ${n}`).join("; ");
        this.log.info(
            `${counts.calculators} calculator(s): resolved ${counts.resolved} calculation(s), kept ${counts.refused}${refusals === "" ? "" : ` (${refusals})`}; removed ${counts.selectorsRemoved} selector call(s), kept ${counts.selectorsKept}`
        );
        return { changed: counts.resolved + counts.selectorsRemoved, bindingsChanged: this.#cloned > 0, stats: counts };
    }

    /** One walk: calls of the calculators' methods (also through wrappers), other references, computed accesses, slot uses. */
    #collect(): void {
        const byFirstKey = new Map<string, Calculator[]>();
        for (const calculator of this.found) byFirstKey.set(calculator.path[0] as string, [...(byFirstKey.get(calculator.path[0] as string) ?? []), calculator]);
        const wrapperOf = new Map<string, { calculator: Calculator; method: string }>();
        const wrapperDefinitions = new Map<Node, Calculator>();
        for (const [key, wrapper] of this.runtime.wrappers) {
            const calculator = this.found.find((c) => wrapper.target.length === c.path.length + 1 && startsWith(wrapper.target, c.path));
            const receiver = wrapper.receiver;
            if (calculator === undefined || receiver === undefined || receiver.length !== calculator.path.length || !startsWith(receiver, calculator.path)) continue;
            // The call reads `G.w` (a data property holding the wrapper), and the wrapper applies its target to `G.k`
            // through `Function.prototype.apply` (relies on model 7: builtins intact).
            const info = this.runtime.guest.inspect([key]);
            if (info?.data !== true || info.type !== "function") continue;
            wrapperOf.set(key, { calculator, method: wrapper.target.at(-1) as string });
            wrapperDefinitions.set(wrapper.definition, calculator);
        }
        let inWrapperOf: Calculator | undefined;

        traverse(this.program, {
            enter: (path) => {
                const owner = wrapperDefinitions.get(path.node);
                if (owner !== undefined) inWrapperOf = owner;
            },
            exit: (path) => {
                if (wrapperDefinitions.has(path.node)) inWrapperOf = undefined;
            },
            Identifier: (path) => {
                const node = path.node;
                const reference = this.scopes.referenceOf(node);
                const member = path.parent;
                if (reference?.resolved != null && !reference.init && !(member?.type === "MemberExpression" && path.key === "object" && isIndexKey(propertyKey(member) ?? ""))) {
                    this.#unslotted.add(reference.resolved);
                }
                if (!this.isStorage(node)) return;
                let outer: Path = path;
                const keys: (string | undefined)[] = [];
                let optional = false;
                while (outer.parent?.type === "MemberExpression" && outer.key === "object" && outer.parentPath !== null) {
                    keys.push(propertyKey(outer.parent));
                    optional ||= outer.parent.optional;
                    outer = outer.parentPath;
                }
                const [first] = keys;
                if (keys.length === 0) return;
                if (first === undefined) {
                    // Only the first computed member matters; writes are the storage analysis' business.
                    const computed = path.parentPath as Path;
                    if (!computed.isWriteTarget()) this.#computed.push({ member: computed.node, places: placesOf(computed) });
                    return;
                }
                const call = outer.parent?.type === "CallExpression" && outer.key === "callee" && !outer.parent.optional && !optional ? outer.parent : undefined;
                for (const calculator of byFirstKey.get(first) ?? []) {
                    if (!startsWith(keys, calculator.path) || inWrapperOf === calculator) continue;
                    if (outer.node === (calculator.definition as Statement & { expression: { left: Node } }).expression.left) continue;
                    const method = keys.length === calculator.path.length + 1 ? keys.at(-1) : undefined;
                    const role = method === calculator.selector ? "selector" : method === calculator.calculation ? "calculation" : undefined;
                    if (call !== undefined && role !== undefined) this.#addSite(call, calculator, role, node, undefined, outer.parentPath as Path);
                    else this.#escape(calculator, outer.node);
                }
                const wrapped = wrapperOf.get(first);
                if (wrapped === undefined || inWrapperOf === wrapped.calculator) return;
                const role = wrapped.method === wrapped.calculator.selector ? "selector" : "calculation";
                if (call !== undefined && keys.length === 1) this.#addSite(call, wrapped.calculator, role, node, first, outer.parentPath as Path);
                else this.#escape(wrapped.calculator, outer.node);
            },
        });
    }

    #escape(calculator: Calculator, node: Node): void {
        if (!this.#escapes.has(calculator)) this.#escapes.set(calculator, node);
    }

    /** A call site, once its callee is known to hold the snapshot's method when it runs. */
    #addSite(call: CallExpression, calculator: Calculator, role: Site["role"], reference: Node, wrapper: string | undefined, callPath: Path): void {
        const method = role === "selector" ? calculator.selector : calculator.calculation;
        const stale = (wrapper === undefined ? undefined : this.effects.staleAt(reference, [wrapper])) ?? this.effects.staleAt(reference, [...calculator.path, method]);
        if (stale !== undefined) {
            this.log.debug(`${calculator.name}: this call may not reach ${calculator.name}.${method}: ${stale.reason}`, stale.node);
            this.#escape(calculator, call);
            return;
        }
        this.#sites.set(call, { call, calculator, role, reference, wrapper, places: placesOf(callPath) });
    }

    /**
     * The case a calculation computes and its arguments, or why that isn't proven; a refusal carries the selector call
     * the calculation surely reads, when that much is proven.
     */
    #resolve(site: Site): Resolution | (Refusal & { readonly selector?: Site }) {
        const { call } = site;
        if (call.arguments.some((arg) => arg.type === "SpreadElement")) return refusal("a spread argument", call);
        const args = call.arguments as Expression[];
        const search = this.#selectorBefore(site);
        if (search.kind === "stop") return refusal(search.reason, search.node);
        const outcome = this.#caseOf(site, search.selector, args);
        return "ok" in outcome ? { ...outcome, selector: search.selector } : outcome;
    }

    /** The case the selector call `selector` chooses for the calculation at `site`, with its arguments, if they can go in. */
    #caseOf(site: Site, selector: Site, args: readonly Expression[]): Resolution | Refusal {
        const { call, calculator } = site;
        const [chosen] = selector.call.arguments;
        if (chosen?.type === "SpreadElement") return refusal("the selector's argument is spread", selector.call);
        const value = chosen === undefined ? { ok: true as const, value: undefined } : evaluate(chosen, this.env);
        if (!value.ok) return refusal("the selector's argument isn't a constant", selector.call);
        // An argument evaluated after the selector call may also be a read that runs a getter: code between the selector
        // call and the calculation, which doesn't use the calculator (model 8). Its effects stay as they were when it is
        // read exactly once, in the order the arguments were passed (`#readOrderProblem`).
        const selectorAt = args.findLastIndex((arg) => this.#isOwnSelector(arg, calculator));
        const getters = new Set<number>();
        for (const [index, arg] of args.entries()) {
            const problem = this.#isOwnSelector(arg, calculator) ? undefined : this.#substitutable(arg);
            if (problem === undefined) continue;
            if (index > selectorAt && this.#readsOnly(arg)) getters.add(index);
            else return refusal(`an argument may have effects: ${problem}`, arg);
        }
        const selected = calculator.cases.find((c) => c.label === value.value);
        if (selected?.problem !== undefined) return refusal(`case ${String(selected.label)} can't be used: ${selected.problem}`, selected.formula);
        if (getters.size > 0) {
            const problem = this.#readOrderProblem(selected?.formula, args, getters, calculator);
            if (problem !== undefined) return refusal(`a getter argument ${problem}`, call);
        }
        if (selected !== undefined) {
            const problem = this.#orderProblem(selected.formula, args, calculator);
            if (problem !== undefined) return refusal(problem, call);
        }
        return { site, selected, args };
    }

    /** Only reads of names and properties, with literal or such keys: no call, store or operator of its own. */
    #readsOnly(node: Node): boolean {
        switch (node.type) {
            case "Literal":
            case "Identifier":
            case "ThisExpression":
                return true;
            case "MemberExpression":
                return node.object.type !== "Super" && this.#readsOnly(node.object) && (!node.computed || this.#readsOnly(node.property));
            default:
                return false;
        }
    }

    /**
     * Why putting getter arguments (`getters`, by index) into the case's expression would change what runs: the
     * calculation reads every argument once, in order, before computing. In place, each non-constant argument must
     * then be read once, in that order, and surely (no `&&`/`||`/`?:` to skip it): getters run as they did, and none
     * can change a local or slot read before or after it out of turn. (The formula's own conversions come after the
     * reads: `#orderProblem`.)
     */
    #readOrderProblem(formula: Expression | undefined, args: readonly Expression[], getters: ReadonlySet<number>, calculator: Calculator): string | undefined {
        if (formula === undefined) return "would not be read (no case is selected)";
        const reads: number[] = [];
        let branches = false;
        traverse(formula, {
            enter: (path) => {
                const node = path.node;
                if (node.type === "LogicalExpression" || node.type === "ConditionalExpression") branches = true;
                if (node.type !== "MemberExpression") return;
                const index = Number(propertyKey(node));
                const arg = args[index];
                if (arg !== undefined && !this.#isOwnSelector(arg, calculator) && !evaluate(arg, this.env).ok) reads.push(index);
            },
        });
        if (branches) return "might not be read (the case's expression branches)";
        if ([...getters].some((index) => !reads.includes(index))) return "would not be read";
        return reads.every((index, i) => i === 0 || index > (reads[i - 1] as number)) ? undefined : "would be read out of turn (twice, or before an earlier argument)";
    }

    #isOwnSelector(node: Node, calculator: Calculator): boolean {
        const site = node.type === "CallExpression" ? this.#sites.get(node) : undefined;
        return site !== undefined && site.calculator === calculator && site.role === "selector";
    }

    /**
     * Whether the value the selector call at `site` stores is overwritten before anything can read it: walking on in
     * evaluation order from the call, on every path (no branch, loop or function end), through quiet code only
     * (`#quiet`: it can't run code or throw, so control surely gets on), another selector call of the calculator comes.
     * Calculations `resolved` no longer read the state. Model 8 doesn't help here: a getter may throw, and then the
     * value stays in the state for whatever calculation runs next, which no selector call of ours precedes.
     */
    #overwrittenAfter(site: Site, resolved: ReadonlyMap<Node, Resolution>): boolean {
        const { calculator } = site;
        /** `true`: a selector call comes first; `false`: something else may run first; `undefined`: quiet, go on. */
        const pass = (node: Node | null | undefined): boolean | undefined => {
            if (node === null || node === undefined) return undefined;
            if (this.#isOwnSelector(node, calculator)) return after((node as CallExpression).arguments, 0) ?? true;
            const resolution = resolved.get(node);
            if (resolution?.site.calculator === calculator) return after(resolution.site.call.arguments, 0) ?? (this.#quietFormula(resolution) ? undefined : false);
            switch (node.type) {
                case "ExpressionStatement":
                    return pass(node.expression);
                case "SequenceExpression":
                    return after(node.expressions, 0);
                case "VariableDeclaration":
                    return node.declarations.every((d) => d.id.type === "Identifier")
                        ? after(
                              node.declarations.map((d) => d.init),
                              0
                          )
                        : false;
                case "EmptyStatement":
                case "FunctionDeclaration":
                    return undefined;
                default:
                    return this.#quiet(node, resolved) ? undefined : false;
            }
        };
        const after = (nodes: readonly (Node | null)[], start: number): boolean | undefined => {
            for (let i = start; i < nodes.length; i++) {
                const result = pass(nodes[i]);
                if (result !== undefined) return result;
            }
            return undefined;
        };
        for (const { parent, key, index } of site.places) {
            const next = (index ?? -1) + 1;
            let result: boolean | undefined;
            switch (parent.type) {
                case "CallExpression": {
                    result = key === "callee" ? after(parent.arguments, 0) : after(parent.arguments, next);
                    const resolution = resolved.get(parent);
                    if (result === undefined) result = resolution?.site.calculator === calculator && this.#quietFormula(resolution) ? undefined : false;
                    break;
                }
                case "SequenceExpression":
                    result = after(parent.expressions, next);
                    break;
                case "ArrayExpression":
                    result = parent.elements.some((element) => element?.type === "SpreadElement") ? false : after(parent.elements, next);
                    break;
                case "VariableDeclarator":
                    if (parent.id.type !== "Identifier") result = false;
                    break;
                case "ExpressionStatement":
                    break;
                case "VariableDeclaration": {
                    const rest = parent.declarations.slice(next);
                    result = rest.every((declarator) => declarator.id.type === "Identifier")
                        ? after(
                              rest.map((declarator) => declarator.init),
                              0
                          )
                        : false;
                    break;
                }
                case "AssignmentExpression":
                    // The value is stored after the right side: quiet when the target is a safe local or a slot.
                    result = parent.operator === "=" && key === "right" && this.#localStore(parent.left) ? undefined : false;
                    break;
                case "BlockStatement":
                    // Falling off its end goes on after it (in a block or an `if`; the next place decides).
                    result = after(parent.body, next);
                    break;
                case "StaticBlock":
                case "Program":
                    result = after(parent.body, next) ?? false;
                    break;
                case "SwitchCase":
                    result = key === "consequent" ? (after(parent.consequent, next) ?? false) : false;
                    break;
                case "IfStatement":
                    if (key === "test") result = false;
                    break;
                default:
                    result = false;
            }
            if (result !== undefined) return result;
        }
        return false;
    }

    /** A resolved calculation's case runs no code and can't throw: constant arguments, no `in`/`instanceof`. */
    #quietFormula({ site, selected, args }: Resolution): boolean {
        if (!args.every((arg) => this.#isOwnSelector(arg, site.calculator) || evaluate(arg, this.env).ok)) return false;
        let quiet = true;
        if (selected !== undefined) {
            traverse(selected.formula, {
                BinaryExpression(path) {
                    if (path.node.operator === "in" || path.node.operator === "instanceof") quiet = false;
                },
            });
        }
        return quiet;
    }

    /**
     * Code that runs no program code and can't throw: constants, safe locals and slot reads, stores into them, literals
     * and functions made of those, selector calls with such arguments, resolved calculations with constant ones, and
     * operators on those (arithmetic only on values known to be primitives other than BigInts: a BigInt mixed in, or
     * `in` on a primitive, throws). Slot stores rely on model 7: builtins intact (no index setters on
     * `Array.prototype`).
     */
    #quiet(node: Node, resolved: ReadonlyMap<Node, Resolution>): boolean {
        if (evaluate(node, this.env).ok) return true;
        switch (node.type) {
            case "Literal":
            case "ThisExpression":
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return true;
            case "Identifier":
                return this.#safeBinding(node);
            case "MemberExpression":
                return this.#isSlotRead(node);
            case "SequenceExpression":
                return node.expressions.every((e) => this.#quiet(e, resolved));
            case "LogicalExpression":
                return this.#quiet(node.left, resolved) && this.#quiet(node.right, resolved);
            case "ConditionalExpression":
                return this.#quiet(node.test, resolved) && this.#quiet(node.consequent, resolved) && this.#quiet(node.alternate, resolved);
            case "ArrayExpression":
                return node.elements.every((e) => e === null || (e.type !== "SpreadElement" && this.#quiet(e, resolved)));
            case "ObjectExpression":
                return node.properties.every((p) => p.type === "Property" && p.kind === "init" && !p.computed && this.#quiet(p.value, resolved));
            case "AssignmentExpression":
                return node.operator === "=" && this.#localStore(node.left) && this.#quiet(node.right, resolved);
            case "CallExpression": {
                const resolution = resolved.get(node);
                if (resolution !== undefined) return this.#quietFormula(resolution);
                return this.#sites.get(node)?.role === "selector" && node.arguments.every((arg) => arg.type !== "SpreadElement" && this.#quiet(arg, resolved));
            }
            default:
                return this.#quietPrimitive(node, resolved);
        }
    }

    /** Quiet code (`#quiet`) whose value is a primitive other than a BigInt. */
    #quietPrimitive(node: Node, resolved: ReadonlyMap<Node, Resolution>): boolean {
        if (evaluate(node, this.env).ok) return true;
        switch (node.type) {
            case "CallExpression": {
                const resolution = resolved.get(node);
                return resolution !== undefined && this.#quietFormula(resolution);
            }
            case "UnaryExpression":
                if (node.operator === "!" || node.operator === "typeof" || node.operator === "void") return this.#quiet(node.argument, resolved);
                return node.operator !== "delete" && this.#quietPrimitive(node.argument, resolved);
            case "BinaryExpression":
                return node.operator !== "in" && node.operator !== "instanceof" && this.#quietPrimitive(node.left, resolved) && this.#quietPrimitive(node.right, resolved);
            case "LogicalExpression":
                return this.#quietPrimitive(node.left, resolved) && this.#quietPrimitive(node.right, resolved);
            case "ConditionalExpression":
                return this.#quiet(node.test, resolved) && this.#quietPrimitive(node.consequent, resolved) && this.#quietPrimitive(node.alternate, resolved);
            default:
                return false;
        }
    }

    /**
     * The selector call the calculation at `site` follows: walking back in evaluation order from the call (its own
     * arguments first, then what its ancestors evaluate before it), staying in the function and on every path (no loop
     * bodies, no other branch, no `case` bodies). Explicit code (a call, `new`, a store that may hit a setter) stops
     * the search; code that runs implicitly (getters, `valueOf`/`toString` of converted objects) is passed: it doesn't
     * use the calculator (model 8), so the selector's value is still the state when the calculation reads it.
     */
    #selectorBefore(site: Site): Search {
        const { call, calculator } = site;
        const before = (nodes: readonly (Node | null)[], end: number): Search | undefined => {
            for (let i = end - 1; i >= 0; i--) {
                const node = nodes[i];
                const result = node === null || node === undefined ? undefined : this.#scanBack(node, calculator);
                if (result !== undefined) return result;
            }
            return undefined;
        };
        const own = before(call.arguments, call.arguments.length);
        if (own !== undefined) return own;
        // The callee is read before the arguments: storage data properties, nothing runs.
        for (const { parent, key, index } of site.places) {
            const stop = (reason: string): Search => ({ kind: "stop", reason, node: parent });
            let result: Search | undefined;
            switch (parent.type) {
                case "CallExpression":
                case "NewExpression":
                    if (key === "callee") break;
                    if (parent.arguments.some((arg) => arg.type === "SpreadElement")) return stop("a spread argument");
                    result = before(parent.arguments, index ?? 0) ?? this.#scanBack(parent.callee, calculator);
                    break;
                case "MemberExpression":
                    if (key === "property") result = this.#scanBack(parent.object, calculator);
                    break;
                case "BinaryExpression":
                case "LogicalExpression":
                    if (key === "right") result = this.#scanBack(parent.left, calculator);
                    break;
                case "ConditionalExpression":
                    if (key !== "test") result = this.#scanBack(parent.test, calculator);
                    break;
                case "AssignmentExpression":
                    // A destructuring target is evaluated after the right side; a plain one before it.
                    if (key === "right") result = parent.left.type === "ArrayPattern" || parent.left.type === "ObjectPattern" ? undefined : this.#targetBefore(parent.left, calculator);
                    else if (parent.left.type === "ArrayPattern") {
                        // `[a[calc]] = [x]`: the right side runs first; an array literal's iterator is the builtin
                        // one (model 7), anything else may run code between the elements.
                        if (parent.operator !== "=" || parent.right.type !== "ArrayExpression") return stop("destructuring of something that may not be an array");
                        result = this.#scanBack(parent.right, calculator);
                    }
                    break;
                case "ArrayPattern": {
                    // The elements before it are stored first: a store that isn't to a plain name may hit a setter.
                    const earlier = parent.elements.slice(0, index ?? 0);
                    if (earlier.some((element) => element !== null && element.type !== "Identifier")) return stop("a destructuring store before it");
                    break;
                }
                case "SequenceExpression":
                    result = before(parent.expressions, index ?? 0);
                    break;
                case "ArrayExpression":
                    if (parent.elements.some((element) => element?.type === "SpreadElement")) return stop("a spread element");
                    result = before(parent.elements, index ?? 0);
                    break;
                case "TemplateLiteral":
                    // Each earlier substitution is converted to a string right after it is evaluated (model 8).
                    result = before(parent.expressions, index ?? 0);
                    break;
                case "UnaryExpression":
                case "ExpressionStatement":
                case "ReturnStatement":
                case "ThrowStatement":
                case "SwitchStatement":
                case "LabeledStatement":
                    break;
                case "VariableDeclarator":
                    if (parent.id.type !== "Identifier") return stop("a destructuring declaration");
                    break;
                case "VariableDeclaration":
                    result = before(parent.declarations, index ?? 0);
                    break;
                case "IfStatement":
                    if (key !== "test") result = this.#scanBack(parent.test, calculator);
                    break;
                case "ForStatement":
                    if (key !== "init") return stop("the calculation is in a loop");
                    break;
                case "ForInStatement":
                case "ForOfStatement":
                    if (key !== "right") return stop("the calculation is in a loop");
                    break;
                case "TryStatement":
                    if (key !== "block") return stop("the calculation is in a catch or finally block");
                    break;
                case "SwitchCase":
                    // A case's statements run from its first one, whether its label matched or the case before fell through.
                    if (key !== "consequent") return stop("the calculation is in a case label");
                    result = before(parent.consequent, index ?? 0);
                    if (result === undefined) return stop("no selector call before it in its case");
                    break;
                case "BlockStatement":
                case "StaticBlock":
                case "Program":
                    result = before(parent.body, index ?? 0);
                    if (result === undefined && parent.type === "Program") return stop("no selector call before it");
                    break;
                default:
                    return isFunctionNode(parent) ? stop("no selector call before it in its function") : stop(`the calculation is inside a ${parent.type}`);
            }
            if (result !== undefined) return result;
        }
        return { kind: "stop", reason: "no selector call before it", node: call };
    }

    /**
     * What evaluating a whole node that runs before the calculation gives the search: the selector call (when the
     * node ends with it), a stop (it runs code explicitly), or nothing (it can be passed).
     */
    #scanBack(node: Node, calculator: Calculator): Search | undefined {
        if (node.type === "CallExpression") {
            const site = this.#sites.get(node);
            if (site !== undefined && site.calculator === calculator && site.role === "selector") return { kind: "found", selector: site };
        }
        switch (node.type) {
            case "ExpressionStatement":
                return this.#scanBack(node.expression, calculator);
            case "SequenceExpression":
                for (let i = node.expressions.length - 1; i >= 0; i--) {
                    const result = this.#scanBack(node.expressions[i] as Node, calculator);
                    if (result !== undefined) return result;
                }
                return undefined;
            case "VariableDeclaration":
                for (let i = node.declarations.length - 1; i >= 0; i--) {
                    const declarator = node.declarations[i] as Node & { type: "VariableDeclarator" };
                    if (declarator.id.type !== "Identifier") return { kind: "stop", reason: "a destructuring declaration", node: declarator };
                    const result = declarator.init === null ? undefined : this.#scanBack(declarator.init, calculator);
                    if (result !== undefined) return result;
                }
                return undefined;
            case "EmptyStatement":
            case "FunctionDeclaration":
                return undefined;
            case "IfStatement": {
                // A decided test (an answered detector, an opaque predicate): it runs, then only the branch it takes.
                const test = evaluate(node.test, this.env);
                if (!test.ok) return { kind: "stop", reason: "an IfStatement between the selector call and the calculation", node };
                const taken = test.value ? node.consequent : node.alternate;
                const statements = taken === null ? [] : taken.type === "BlockStatement" ? taken.body : [taken];
                for (let i = statements.length - 1; i >= 0; i--) {
                    const result = this.#scanBack(statements[i] as Node, calculator);
                    if (result !== undefined) return result;
                }
                return this.#scanBack(node.test, calculator);
            }
            default: {
                if (node.type.endsWith("Statement") || node.type.endsWith("Declaration")) return { kind: "stop", reason: `a ${node.type} between the selector call and the calculation`, node };
                const explicit = this.#explicitCode(node, calculator);
                return explicit === undefined ? undefined : { kind: "stop", reason: `${explicit.reason} between the selector call and the calculation`, node: explicit.node };
            }
        }
    }

    /**
     * What an assignment target evaluates before its right side: its object and key. Converting a computed key, and
     * the read a compound operator makes, run code only implicitly (model 8).
     */
    #targetBefore(target: Node, calculator: Calculator): Search | undefined {
        if (target.type === "Identifier") return undefined;
        if (target.type !== "MemberExpression") return { kind: "stop", reason: "a destructuring assignment", node: target };
        return this.#scanBack(target.object, calculator) ?? (target.computed ? this.#scanBack(target.property, calculator) : undefined);
    }

    /**
     * The first place evaluating `node` may run program code explicitly: a call, `new`, a store that may hit a setter,
     * a `delete`... Getters (property and global reads) and conversions of objects by operators run code implicitly,
     * which doesn't use the calculator (model 8). Selector calls of other calculators only write their own state, and
     * calculations only read it and convert their arguments (model 8 again): both are passed.
     */
    #explicitCode(node: Node, calculator: Calculator): { reason: string; node: Node } | undefined {
        const all = (nodes: readonly Node[]): { reason: string; node: Node } | undefined => {
            for (const child of nodes) {
                const explicit = this.#explicitCode(child, calculator);
                if (explicit !== undefined) return explicit;
            }
            return undefined;
        };
        switch (node.type) {
            case "Literal":
            case "ThisExpression":
            case "Identifier":
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return undefined;
            case "MemberExpression":
                if (node.object.type === "Super") return { reason: "a super property", node };
                return all(node.computed ? [node.object, node.property] : [node.object]);
            case "UnaryExpression":
                return node.operator === "delete" ? { reason: "a delete", node } : this.#explicitCode(node.argument, calculator);
            case "BinaryExpression":
                return node.left.type === "PrivateIdentifier" ? { reason: "a private name test", node } : all([node.left, node.right]);
            case "LogicalExpression":
                return all([node.left, node.right]);
            case "ConditionalExpression":
                return all([node.test, node.consequent, node.alternate]);
            case "SequenceExpression":
                return all(node.expressions);
            case "TemplateLiteral":
                return all(node.expressions);
            case "ArrayExpression":
                if (node.elements.some((element) => element?.type === "SpreadElement")) return { reason: "a spread element", node };
                return all(node.elements.filter((element): element is Expression => element !== null));
            case "ObjectExpression":
                if (!node.properties.every((p) => p.type === "Property" && p.kind === "init" && !p.computed)) return { reason: "an object literal with computed keys, accessors or spread", node };
                return all(node.properties.map((p) => (p as Node & { type: "Property" }).value));
            case "UpdateExpression":
                return this.#localStore(node.argument) ? undefined : { reason: "an update of a property or global (possible setter)", node };
            case "AssignmentExpression":
                // A compound operator's read and conversion of a local run code only implicitly (model 8).
                return this.#localStore(node.left) ? this.#explicitCode(node.right, calculator) : { reason: "a property or global write (possible setter)", node };
            case "CallExpression": {
                const site = this.#sites.get(node);
                const passed = site !== undefined && (site.role === "calculation" || site.calculator !== calculator) && node.arguments.every((arg) => arg.type !== "SpreadElement");
                if (passed || (node.arguments.every((arg) => arg.type !== "SpreadElement") && this.#quietCall(node))) return all(node.arguments as Expression[]);
                return { reason: "a call", node };
            }
            default:
                return { reason: `a ${node.type}`, node };
        }
    }

    /**
     * A call of a runtime function (`G.k.m(...)`, or a wrapper of one) whose code can't reach a selector call: the
     * snapshot's method is the one its builder made (one prelude write, a data property, `staleAt`), and nothing it
     * runs names the storage object or calls anything but local functions of the same kind (`#cannotReachSelector`).
     * Selector calls are only reached through storage paths (they're checked to have no other references), so such a
     * call leaves every selector's state alone.
     */
    #quietCall(call: CallExpression): boolean {
        if (call.callee.type !== "MemberExpression") return false;
        const path = memberPath(call.callee);
        if (path === undefined || !this.isStorage(path.root)) return false;
        const [first] = path.keys;
        const wrapper = path.keys.length === 1 && first !== undefined ? this.runtime.wrappers.get(first) : undefined;
        const target = wrapper?.target ?? path.keys;
        if (target.length !== 2 || (wrapper !== undefined && this.effects.staleAt(path.root, path.keys) !== undefined) || this.effects.staleAt(path.root, target) !== undefined) return false;
        const info = this.runtime.guest.inspect(target);
        if (info?.data !== true || info.type !== "function" || this.effects.preludeWritesTo(target) !== 1) return false;
        const definition = definitionOf(this.runtime, this.isStorage, target.slice(0, 1));
        if (typeof definition === "string") return false;
        const builder = builderOf(definition.iife, this.scopes);
        const fn = typeof builder === "string" ? undefined : builder.methods.get(target[1] as string);
        const quiet = fn !== undefined && this.#cannotReachSelector(fn);
        if (quiet) this.log.debug(`call passed: ${this.runtime.storage}.${target.join(".")} can't reach a selector call`, call);
        return quiet;
    }

    /**
     * Running `fn` can't reach a selector call: it is a plain function that makes no member, `new`, tagged or import
     * calls and calls only local functions (one binding, one function literal) that satisfy the same, checked
     * coinductively (a call cycle is only entered from outside it). A selector is a method, so reaching it takes a
     * member call somewhere (directly, or through `call`/`apply`). Property stores and deletes are refused too (a
     * setter could run). Getters and conversions run code that doesn't use the calculator (model 8). A function
     * assumed while it is being checked makes the answers found meanwhile provisional: they are kept only if the
     * outermost check succeeds (any failure inside it fails its callers, up to the outermost).
     */
    #cannotReachSelector(fn: Node): boolean {
        const known = this.#isolated.get(fn);
        if (known !== undefined) return known;
        if (!isFunctionNode(fn) || (fn as FunctionNode).async || (fn as FunctionNode).generator) return false;
        const outermost = this.#provisional === undefined;
        const provisional = (this.#provisional ??= []);
        this.#isolated.set(fn, true);
        provisional.push(fn);
        let isolated = true;
        traverse(fn, {
            enter: (path) => {
                const node = path.node;
                if (!isolated) return path.skip();
                if (node !== fn && isFunctionNode(node)) return path.skip();
                switch (node.type) {
                    case "NewExpression":
                    case "TaggedTemplateExpression":
                    case "ImportExpression":
                    case "Super":
                        isolated = false;
                        return;
                    case "CallExpression": {
                        const local = node.callee.type === "Identifier" ? this.#localFunction(node.callee) : undefined;
                        if (local === undefined || !this.#cannotReachSelector(local)) isolated = false;
                        return;
                    }
                    case "AssignmentExpression":
                        if (node.left.type !== "Identifier") isolated = false;
                        return;
                    case "UpdateExpression":
                        if (node.argument.type !== "Identifier") isolated = false;
                        return;
                    case "UnaryExpression":
                        if (node.operator === "delete") isolated = false;
                        return;
                    default:
                        return;
                }
            },
        });
        if (!isolated) this.#isolated.set(fn, false);
        if (outermost) {
            if (!isolated) for (const other of provisional) if (this.#isolated.get(other) === true) this.#isolated.delete(other);
            this.#provisional = undefined;
        }
        return isolated;
    }

    /** The one function a local name is bound to: a function declaration, or a `var` written once with a function. */
    #localFunction(identifier: Node): Node | undefined {
        const variable = this.scopes.variableOf(identifier);
        const [def] = variable?.defs ?? [];
        if (variable === undefined || variable.defs.length !== 1 || def === undefined) return undefined;
        if (def.type === "FunctionName") return def.node as unknown as Node;
        if (def.type !== "Variable" || variable.references.filter((reference) => reference.isWrite()).length !== 1) return undefined;
        const init = (def.node as unknown as Node & { type: "VariableDeclarator" }).init;
        return init !== null && isFunctionNode(init) ? init : undefined;
    }

    /** A store target that runs no setter: a safe local, or a slot of a slot array. */
    #localStore(target: Node): boolean {
        return target.type === "Identifier" ? this.#safeBinding(target) : this.#isSlotRead(target);
    }

    /** A binding whose read can't throw or run code: a `var`, parameter, function or catch name, or `arguments`. */
    #safeBinding(identifier: Node): boolean {
        const variable = this.scopes.variableOf(identifier);
        if (variable === undefined) return false;
        if (variable.defs.length === 0) return variable.name === "arguments" && variable.scope.type === "function";
        return variable.defs.every((def) => def.type === "Parameter" || def.type === "FunctionName" || def.type === "CatchClause" || (def.type === "Variable" && def.parent.kind === "var"));
    }

    /**
     * `S[i]` with `S` a slot array: a `var` declared once, as the first statement of its function (or program), by an
     * array literal of inert elements, and only ever used as `S[index]`. Every read of it finds that array (the code
     * reading it runs after the declaration), whose index properties are plain data: reading one runs nothing (an index
     * past its end looks up the prototypes: relies on model 7: builtins intact).
     */
    #isSlotRead(node: Node): boolean {
        if (node.type !== "MemberExpression" || node.object.type !== "Identifier" || !isIndexKey(propertyKey(node) ?? "")) return false;
        const variable = this.scopes.variableOf(node.object);
        if (variable === undefined) return false;
        const known = this.#slotArrays.get(variable);
        if (known !== undefined) return known;
        const [def] = variable.defs;
        const declarator = def?.node as unknown as Node | undefined;
        const block = variable.scope.block as unknown as Node;
        const body = block.type === "Program" ? block.body : bodyOf(block);
        const slots =
            variable.defs.length === 1 &&
            !this.#unslotted.has(variable) &&
            def?.type === "Variable" &&
            def.parent.kind === "var" &&
            declarator?.type === "VariableDeclarator" &&
            declarator.init?.type === "ArrayExpression" &&
            declarator.init.elements.every((element) => element?.type === "Identifier" || element?.type === "Literal") &&
            body[0] === (def.parent as unknown as Node);
        this.#slotArrays.set(variable, slots);
        return slots;
    }

    /** Why an argument can't be put into the case's expression (or dropped): `undefined` for constants, safe locals and slot reads. */
    #substitutable(node: Node): string | undefined {
        if (evaluate(node, this.env).ok) return undefined;
        if (node.type === "Identifier") return this.#safeBinding(node) ? undefined : GLOBAL_READ;
        if (node.type === "ThisExpression" || this.#isSlotRead(node)) return undefined;
        return node.type === "MemberExpression" ? GETTER : `a ${node.type}`;
    }

    /**
     * Why the case's expression can't take the arguments in place of `a[i]`: in the calculation every argument is
     * read before the expression runs; in place, a non-constant one is read where the expression reaches it. That is
     * the same as long as no conversion that could run code (an operator applied to a possible object) comes first.
     */
    #orderProblem(formula: Expression, args: readonly Expression[], calculator: Calculator): string | undefined {
        let converted = false;
        let problem: string | undefined;
        /** Whether the value may be an object. */
        const visit = (node: Node): boolean => {
            switch (node.type) {
                case "MemberExpression": {
                    const arg = args[Number(propertyKey(node))];
                    if (arg === undefined || this.#isOwnSelector(arg, calculator) || evaluate(arg, this.env).ok) return false;
                    if (converted) problem ??= "an argument would be read after a conversion that may run code";
                    return true;
                }
                case "UnaryExpression": {
                    const object = visit(node.argument);
                    if (object && ["-", "+", "~"].includes(node.operator)) converted = true;
                    return false;
                }
                case "BinaryExpression": {
                    const left = visit(node.left);
                    const right = visit(node.right);
                    if ((left || right) && node.operator !== "===" && node.operator !== "!==") converted = true;
                    return false;
                }
                case "LogicalExpression": {
                    const left = visit(node.left);
                    return visit(node.right) || left;
                }
                case "ConditionalExpression": {
                    visit(node.test);
                    const consequent = visit(node.consequent);
                    return visit(node.alternate) || consequent;
                }
                default:
                    return false;
            }
        };
        visit(formula);
        return problem;
    }

    /**
     * Whether a computed `G[x]` access may let code reach a calculator after the prelude (then every selector call
     * stays). One in code that runs only in the prelude can't, if its value stays there: it is only called or tested,
     * or held in a local of its function that is only called, tested or returned, and a returned value is only called
     * by its function's callers, in prelude code.
     */
    #computedAccessKeeps(): { reason: string; node: Node } | undefined {
        for (const { member, places } of this.#computed) {
            const fn = enclosingFunction(places, this.runtime.root);
            if (fn === null || !this.effects.runsOnlyInPrelude(fn)) return { reason: "a computed access to the storage object may run after the prelude", node: member };
            const escape = this.#leavesPrelude(member, places, fn);
            if (escape !== undefined) return { reason: `a computed access to the storage object in prelude code hands its value on (${escape.reason})`, node: escape.node };
            this.log.debug("computed access to the storage object: prelude code only, its value stays there", member);
        }
        return undefined;
    }

    #parents = new Map<Node, Map<Node, Node>>();

    /** Parents of the nodes in `block` (a function or the program), built once per block. */
    #parentsIn(block: Node): Map<Node, Node> {
        let parents = this.#parents.get(block);
        if (parents === undefined) {
            const built = new Map<Node, Node>();
            traverse(block, {
                enter(path) {
                    if (path.parent !== null) built.set(path.node, path.parent);
                },
            });
            this.#parents.set(block, built);
            parents = built;
        }
        return parents;
    }

    /** Where the value of `member` (in prelude-only `fn`) may get to code that isn't prelude-only. */
    #leavesPrelude(member: Node, places: readonly Place[], fn: Node | undefined): { reason: string; node: Node } | undefined {
        const [place] = places;
        if (place === undefined) return { reason: "used at the top", node: member };
        const { parent, key } = place;
        if (this.#calledOrTested(parent, member)) return undefined;
        const holder =
            parent.type === "AssignmentExpression" && key === "right" && parent.operator === "=" ? parent.left : parent.type === "VariableDeclarator" && key === "init" ? parent.id : undefined;
        if (holder?.type !== "Identifier" || fn === undefined) return { reason: `used in a ${parent.type}`, node: parent };
        const variable = this.scopes.variableOf(holder);
        if (variable === undefined || (variable.scope.block as unknown as Node) !== fn) return { reason: "held outside its function", node: holder };
        const parents = this.#parentsIn(fn);
        for (const reference of variable.references) {
            const identifier = reference.identifier as unknown as Node;
            if (reference.isWrite() && !reference.isRead()) continue;
            const above = parents.get(identifier);
            if (above !== undefined && this.#calledOrTested(above, identifier)) continue;
            if (above?.type === "ReturnStatement" && enclosingScopeFunction(reference.from) === fn) {
                const caller = this.#returnLeaves(fn);
                if (caller !== undefined) return caller;
                continue;
            }
            return { reason: "its local is used otherwise", node: identifier };
        }
        return undefined;
    }

    /** Whether `parent` only calls or tests its child `value` (`f()`, `!f`, `typeof f`, a condition). */
    #calledOrTested(parent: Node, value: Node): boolean {
        switch (parent.type) {
            case "CallExpression":
                return parent.callee === value;
            case "UnaryExpression":
                return parent.operator === "!" || parent.operator === "typeof";
            case "IfStatement":
            case "WhileStatement":
            case "DoWhileStatement":
            case "ForStatement":
            case "ConditionalExpression":
                return parent.test === value;
            default:
                return false;
        }
    }

    /** Where `fn`'s return value may get to: its binding's every use must be a call whose result is only called, in prelude code. */
    #returnLeaves(fn: Node): { reason: string; node: Node } | undefined {
        // `function f() {}`, or `var f = function () {}`: a variable of a scope around it, defined by that initializer.
        let variable = fn.type === "FunctionDeclaration" && fn.id !== null ? this.scopes.variableOf(fn.id) : undefined;
        for (
            let scope = fn.type === "FunctionDeclaration" ? null : this.scopes.scopeOf(fn)?.upper;
            variable === undefined && scope !== null && scope !== undefined;
            scope = scope.type === "function" ? null : scope.upper
        ) {
            variable = scope.variables.find((v) => v.defs.length === 1 && v.defs[0]?.type === "Variable" && (v.defs[0].node.init as unknown as Node | null) === fn);
        }
        if (variable === undefined || variable.defs.length !== 1) return { reason: "it returns it from a function not bound once", node: fn };
        const parents = this.#parentsIn(variable.scope.block as unknown as Node);
        for (const reference of variable.references) {
            if (reference.init) continue;
            const identifier = reference.identifier as unknown as Node;
            const call = parents.get(identifier);
            const outer = call === undefined ? undefined : parents.get(call);
            const caller = enclosingScopeFunction(reference.from);
            const where = caller === null ? null : caller === this.runtime.root ? undefined : caller;
            if (call?.type !== "CallExpression" || call.callee !== identifier || outer?.type !== "CallExpression" || outer.callee !== call)
                return { reason: "its function's result isn't only called", node: identifier };
            if (where === null || !this.effects.runsOnlyInPrelude(where)) return { reason: "its function is called after the prelude", node: identifier };
        }
        return undefined;
    }

    /** The replacement of a resolved calculation: the case's expression with the arguments in, after kept selector calls among them. */
    #replacement({ site, selected, args }: Resolution, removable: ReadonlySet<CallExpression>): Expression {
        const { call, calculator } = site;
        const used = new Set<number>();
        const put = (node: Expression): Expression => {
            switch (node.type) {
                case "MemberExpression": {
                    const index = Number(propertyKey(node));
                    const arg = args[index];
                    if (arg === undefined || this.#isOwnSelector(arg, calculator)) return voidZero(call);
                    if (!used.has(index)) {
                        used.add(index);
                        return arg;
                    }
                    if (arg.type !== "Literal") this.#cloned++;
                    return structuredClone(arg);
                }
                case "Literal":
                    return at<Expression>({ ...node }, call);
                case "UnaryExpression":
                    return at<Expression>({ type: "UnaryExpression", operator: node.operator, prefix: true, argument: put(node.argument) }, call);
                case "BinaryExpression":
                    return at<Expression>({ type: "BinaryExpression", operator: node.operator, left: put(node.left as Expression), right: put(node.right) }, call);
                case "LogicalExpression":
                    return at<Expression>({ type: "LogicalExpression", operator: node.operator, left: put(node.left), right: put(node.right) }, call);
                case "ConditionalExpression":
                    return at<Expression>({ type: "ConditionalExpression", test: put(node.test), consequent: put(node.consequent), alternate: put(node.alternate) }, call);
                default:
                    throw new TypeError(`calculators: unexpected ${node.type} in a checked formula`);
            }
        };
        const value = selected === undefined ? voidZero(call) : put(selected.formula);
        const kept = args.filter((arg): arg is CallExpression => this.#isOwnSelector(arg, calculator) && !removable.has(arg as CallExpression));
        return kept.length === 0 ? value : at<Expression>({ type: "SequenceExpression", expressions: [...kept, value] }, call);
    }

    /**
     * Replace the calculations and remove dead selector calls, at the places the walk recorded (no other walk: the
     * replacements don't move anything, and removals from lists happen last, per list). Returns how many selector
     * calls went.
     */
    #rewrite(resolved: ReadonlyMap<Node, Resolution>, removable: ReadonlySet<CallExpression>): number {
        const put = ({ parent, key, index }: Place, node: Node): void => {
            const holder = parent as unknown as Record<string, Node | Node[]>;
            const slot = holder[key];
            if (index !== null && Array.isArray(slot)) slot[index] = node;
            else holder[key] = node;
        };
        for (const resolution of resolved.values()) {
            const [place] = resolution.site.places;
            if (place !== undefined) put(place, this.#replacement(resolution, removable));
        }
        let removed = 0;
        /** Lists losing elements: statement lists and sequences (with the sequence's place, to unwrap a lone element). */
        const pruned = new Map<Node[], { gone: Set<Node>; sequenceAt: Place | undefined }>();
        const prune = (list: Node[], node: Node, sequenceAt: Place | undefined): void => {
            const entry = pruned.get(list) ?? { gone: new Set<Node>(), sequenceAt };
            entry.gone.add(node);
            pruned.set(list, entry);
        };
        for (const call of removable) {
            removed++;
            const [own, outer] = this.#sites.get(call)?.places ?? [];
            // An argument of a replaced calculation went with it.
            if (own === undefined || resolved.has(own.parent)) continue;
            const parent = own.parent;
            const inList = outer !== undefined && outer.index !== null && STATEMENT_LISTS[outer.parent.type] === true;
            if (parent.type === "ExpressionStatement" && inList) prune((outer.parent as unknown as Record<string, Node[]>)[outer.key] as Node[], parent, undefined);
            else if (parent.type === "ExpressionStatement" && outer !== undefined) put(outer, at<Statement>({ type: "EmptyStatement" }, parent));
            else if (parent.type === "SequenceExpression" && own.index !== null && own.index < parent.expressions.length - 1 && outer !== undefined) prune(parent.expressions, call, outer);
            else put(own, voidZero(call));
        }
        for (const [list, { gone, sequenceAt }] of pruned) {
            let length = 0;
            for (const node of list) if (!gone.has(node)) list[length++] = node;
            list.length = length;
            const [only] = list;
            if (sequenceAt !== undefined && length === 1 && only !== undefined) put(sequenceAt, only);
        }
        return removed;
    }
}

/** Nodes whose list of statements a statement can be removed from. */
const STATEMENT_LISTS: Record<string, true> = { Program: true, BlockStatement: true, StaticBlock: true, SwitchCase: true };

/** The function (or program) node a scope's code belongs to; `null` for class field or static block code. */
const enclosingScopeFunction = (scope: Variable["scope"] | null): Node | null => {
    for (let s = scope; s !== null; s = s.upper) {
        if (s.type === "function" || s.type === "global" || s.type === "module") return s.block as unknown as Node;
        if (s.type === "class-field-initializer" || s.type === "class-static-block") return null;
    }
    return null;
};
