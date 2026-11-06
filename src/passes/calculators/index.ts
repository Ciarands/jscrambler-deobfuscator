import type { CallExpression, Expression, Node, Statement } from "../../core/ast.js";
import { isFunctionNode, propertyKey } from "../../core/ast.js";
import { at, callOf, valueToNode } from "../../core/build.js";
import { globalsEnv } from "../../core/constants.js";
import type { EvaluateEnv } from "../../core/evaluate.js";
import { evaluate } from "../../core/evaluate.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import { parentsWithin } from "../runtime/builders.js";
import type { StorageEffects } from "../runtime/effects.js";
import { storageAnalysis } from "../runtime/effects.js";
import type { PropertyPath, RuntimeModel } from "../runtime/model.js";
import { RUNTIME } from "../runtime/model.js";
import { LocalReads } from "./locals.js";
import { EvaluationOrder } from "./order.js";
import { recognize } from "./recognize.js";
import type { Calculator, Place, Refusal, Resolution, Site } from "./sites.js";
import { isOwnSelector, placesOf, refusal } from "./sites.js";

const startsWith = (keys: readonly (string | undefined)[], prefix: PropertyPath): boolean => keys.length >= prefix.length && prefix.every((key, i) => key === keys[i]);

const enclosingFunction = (places: readonly Place[], root: Node): Node | undefined | null => {
    for (const { parent } of places) if (isFunctionNode(parent)) return parent === root ? undefined : parent;
    return root.type === "Program" ? undefined : null;
};

/**
 * Calculator objects: `G.k.sel(3); x = G.k.calc(a, 7);` becomes case 3's expression with the arguments put in (`a - 7`).
 *
 * Proof per calculation:
 * - the calculator (`calculatorOf`): built once by the prelude, its state written only by the selector and read only
 *   by the switch; the methods and wrappers used hold the snapshot's values when called (`staleAt`);
 * - the selector value: the nearest selector call before it in evaluation order, same function, every path, constant
 *   argument, no explicit code between; getters and conversions don't use the calculator (model 8) (`selectorBefore`);
 * - the arguments: constants, safe locals and slot reads (`substitutable`): no effect, can't throw, same value. Model 8
 *   doesn't cover getter arguments nor conversions inside the case's expression, so a non-constant argument is only
 *   put where no code-running conversion precedes it (`orderProblem`); otherwise the arguments are bound to an arrow's
 *   parameters first, as the calculation binds them to `arguments`. `a[i]` past the arguments is undefined and
 *   wrappers use `Function.prototype.apply` (model 7: builtins intact).
 *
 * A selector call goes when the next one overwrites it through quiet code only (`overwrittenAfter`). A proven selector
 * call is exactly what its calculation reads (model 8): once every post-prelude calculation is replaced or proven, and
 * nothing else reaches the calculator (escaping reference, or `computedAccessKeeps`), other post-prelude selector calls
 * go; the prelude's own stay.
 */
const calculatorsPass = (bindArguments: boolean): Pass => ({
    name: bindArguments ? "calculators-bound" : "calculators",
    description: bindArguments
        ? "Replace the calculations left, binding arguments a conversion could change first (after arguments-arrays)"
        : "Replace calculations of the runtime's calculator objects with the selected case's expression",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined) {
            log.info("no runtime, nothing to do");
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
        return new CalculatorRewrite(program, runtime, matcher.isStorage, effects, scopes, env, log, found, bindArguments).run();
    },
});

/**
 * Without binding arguments: a slot argument arguments-arrays turns into a plain local later may then go in directly,
 * so a calculation it would bind stays for that run.
 */
export const calculators = calculatorsPass(false);

export const calculatorsBound = calculatorsPass(true);

class CalculatorRewrite {
    readonly #sites = new Map<CallExpression, Site>();
    /** Per calculator, the first reference that isn't a call of its methods or a wrapper of one. */
    readonly #escapes = new Map<Calculator, Node>();
    readonly #computed: { member: Node; places: Place[] }[] = [];
    readonly #locals: LocalReads;
    readonly #order: EvaluationOrder;
    #parentLinks: ReadonlyMap<Node, Node> | undefined;
    #cloned = 0;

    constructor(
        readonly program: Node,
        readonly runtime: RuntimeModel,
        readonly isStorage: (node: Node) => boolean,
        readonly effects: StorageEffects,
        readonly scopes: ScopeInfo,
        readonly env: EvaluateEnv,
        readonly log: PassContext["log"],
        readonly found: readonly Calculator[],
        readonly bindArguments: boolean
    ) {
        this.#locals = new LocalReads(scopes, env, () => this.#parents());
        this.#order = new EvaluationOrder(this.#sites, this.#locals, { runtime, isStorage, effects, scopes, env, log });
    }

    run(): PassResult {
        this.#collect();
        const counts = { calculators: this.found.length, resolved: 0, bound: 0, refused: 0, selectorsRemoved: 0, selectorsKept: 0 };
        const reasons = new Map<string, number>();
        const resolutions: Resolution[] = [];
        const unproven = new Set<Calculator>();
        const preludeReaders = new Set<Calculator>();
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

        // A proven selector call is exactly what its calculation reads (model 8), so once every post-prelude
        // calculation has one, other post-prelude selector calls are dead.
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
                if (!site.call.arguments.every((arg) => arg.type !== "SpreadElement" && this.#locals.substitutable(arg) === undefined))
                    this.log.debug("selector call kept: an argument may have effects", site.call);
                else if (read.has(site.call)) this.log.debug("selector call kept: a calculation that stays reads its value", site.call);
                else if (this.#order.overwrittenAfter(site, resolved)) {
                    this.log.debug("selector call removed: the next selector call overwrites its value before anything can read it", site.call);
                    removable.add(site.call);
                } else if (keep !== undefined) this.log.debug("selector call kept: a calculation may read its value", site.call);
                else if (!this.effects.runsAfterPrelude(site.reference) && preludeReaders.has(calculator))
                    this.log.debug("selector call kept: it runs in the prelude, where a calculation that stays may read it", site.call);
                else removable.add(site.call);
            }
        }

        for (const resolution of resolutions) {
            const { selected, bound } = resolution;
            this.log.debug(
                `${resolution.site.calculator.name}: calculation resolved (case ${selected === undefined ? "none: undefined" : String(selected.label)}${bound === undefined ? "" : `, arguments bound first: ${bound}`})`,
                resolution.site.call
            );
        }
        counts.resolved = resolutions.length;
        counts.bound = resolutions.filter((resolution) => resolution.bound !== undefined).length;
        counts.selectorsRemoved = this.#rewrite(resolved, removable);
        counts.selectorsKept = [...this.#sites.values()].filter((site) => site.role === "selector").length - counts.selectorsRemoved;

        const refusals = [...reasons].map(([reason, n]) => `${reason} ${n}`).join("; ");
        this.log.info(
            `${counts.calculators} calculator(s): resolved ${counts.resolved} calculation(s) (${counts.bound} with arguments bound first), kept ${counts.refused}${refusals === "" ? "" : ` (${refusals})`}; removed ${counts.selectorsRemoved} selector call(s), kept ${counts.selectorsKept}`
        );
        // A bound calculation's arrow names only its own parameters (see `PassResult.bindingsChanged`); copied
        // arguments are new references to existing bindings.
        return { changed: counts.resolved + counts.selectorsRemoved, bindingsChanged: this.#cloned > 0, stats: counts };
    }

    /** Built once, before the rewrite moves anything. */
    #parents(): ReadonlyMap<Node, Node> {
        this.#parentLinks ??= parentsWithin(this.program);
        return this.#parentLinks;
    }

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
            const info = this.effects.snapshot.typeAt([key]);
            if (typeof info === "string" || info.type !== "function") continue;
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

    /** A refusal carries the selector call the calculation surely reads, when that much is proven. */
    #resolve(site: Site): Resolution | (Refusal & { readonly selector?: Site }) {
        const { call } = site;
        if (call.arguments.some((arg) => arg.type === "SpreadElement")) return refusal("a spread argument", call);
        const args = call.arguments as Expression[];
        const search = this.#order.selectorBefore(site);
        if (search.kind === "stop") return refusal(search.reason, search.node);
        const outcome = this.#caseOf(site, search.selector, args);
        return "ok" in outcome ? { ...outcome, selector: search.selector } : outcome;
    }

    #caseOf(site: Site, selector: Site, args: readonly Expression[]): Resolution | Refusal {
        const { call, calculator } = site;
        const [chosen] = selector.call.arguments;
        if (chosen?.type === "SpreadElement") return refusal("the selector's argument is spread", selector.call);
        const value = chosen === undefined ? { ok: true as const, value: undefined } : evaluate(chosen, this.env);
        if (!value.ok) return refusal("the selector's argument isn't a constant", selector.call);
        // An argument evaluated after the selector call may also be a read that runs a getter: code between the selector
        // call and the calculation, which doesn't use the calculator (model 8). Its effects stay as they were when it is
        // read exactly once, in the order the arguments were passed (`readOrderProblem`).
        const selectorAt = args.findLastIndex((arg) => isOwnSelector(this.#sites, arg, calculator));
        const getters = new Set<number>();
        for (const [index, arg] of args.entries()) {
            const problem = isOwnSelector(this.#sites, arg, calculator) ? undefined : this.#locals.substitutable(arg);
            if (problem === undefined) continue;
            if (index > selectorAt && this.#order.readsOnly(arg)) getters.add(index);
            else return refusal(`an argument may have effects: ${problem}`, arg);
        }
        const selected = calculator.cases.find((c) => c.label === value.value);
        if (selected?.problem !== undefined) return refusal(`case ${String(selected.label)} can't be used: ${selected.problem}`, selected.formula);
        if (getters.size > 0) {
            const problem = this.#order.readOrderProblem(selected?.formula, args, getters, calculator);
            if (problem !== undefined) return refusal(`a getter argument ${problem}`, call);
        }
        const bound = selected === undefined ? undefined : this.#order.orderProblem(selected.formula, args, calculator);
        if (bound !== undefined && !this.bindArguments) return refusal(bound, call);
        return { site, selected, args, bound };
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

    /** Where the value of `member` (in prelude-only `fn`) may get to code that isn't prelude-only. */
    #leavesPrelude(member: Node, places: readonly Place[], fn: Node | undefined): { reason: string; node: Node } | undefined {
        const [place] = places;
        if (place === undefined) return { reason: "used at the top", node: member };
        const { parent, key } = place;
        if (calledOrTested(parent, member)) return undefined;
        const holder =
            parent.type === "AssignmentExpression" && key === "right" && parent.operator === "=" ? parent.left : parent.type === "VariableDeclarator" && key === "init" ? parent.id : undefined;
        if (holder?.type !== "Identifier" || fn === undefined) return { reason: `used in a ${parent.type}`, node: parent };
        const variable = this.scopes.variableOf(holder);
        if (variable === undefined || (variable.scope.block as unknown as Node) !== fn) return { reason: "held outside its function", node: holder };
        const references = this.scopes.references(variable);
        if (references === undefined) return { reason: "a with statement may intercept a use of its local", node: holder };
        const parents = this.#parents();
        for (const reference of references) {
            const identifier = reference.identifier as unknown as Node;
            if (reference.isWrite() && !reference.isRead()) continue;
            const above = parents.get(identifier);
            if (above !== undefined && calledOrTested(above, identifier)) continue;
            if (above?.type === "ReturnStatement" && enclosingScopeFunction(reference.from) === fn) {
                const caller = this.#returnLeaves(fn);
                if (caller !== undefined) return caller;
                continue;
            }
            return { reason: "its local is used otherwise", node: identifier };
        }
        return undefined;
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
        if (this.scopes.annexBEscapes(variable)) return { reason: "its function also goes to a function-wide binding (Annex B)", node: fn };
        const references = this.scopes.references(variable);
        if (references === undefined) return { reason: "a with statement may intercept a use of its function", node: fn };
        const parents = this.#parents();
        for (const reference of references) {
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

    /**
     * The replacement of a resolved calculation: the case's expression with the arguments in, after kept selector calls
     * among them. Bound arguments become `((p0, p1) => <expression>)(x, y)` instead, literals (primitive constants:
     * `substitutable`) staying in the expression. It names nothing but its parameters, so no name collides.
     */
    #replacement({ site, selected, args, bound }: Resolution, removable: ReadonlySet<CallExpression>): Expression {
        const { call, calculator } = site;
        const used = new Set<number>();
        const parameters = new Map<number, string>();
        if (bound !== undefined) {
            for (const [index, arg] of args.entries()) if (arg.type !== "Literal" && !isOwnSelector(this.#sites, arg, calculator)) parameters.set(index, `p${parameters.size}`);
        }
        const put = (node: Expression): Expression => {
            switch (node.type) {
                case "MemberExpression": {
                    const index = Number(propertyKey(node));
                    const arg = args[index];
                    if (arg === undefined || isOwnSelector(this.#sites, arg, calculator)) return valueToNode(undefined, call);
                    const parameter = parameters.get(index);
                    if (parameter !== undefined) return at<Expression>({ type: "Identifier", name: parameter }, call);
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
        const computed = selected === undefined ? valueToNode(undefined, call) : put(selected.formula);
        const value =
            bound === undefined
                ? computed
                : callOf(
                      at<Expression>(
                          {
                              type: "ArrowFunctionExpression",
                              id: null,
                              expression: true,
                              async: false,
                              generator: false,
                              params: [...parameters.values()].map((name) => at<Expression>({ type: "Identifier", name }, call)),
                              body: computed,
                          },
                          call
                      ),
                      [...parameters.keys()].map((index) => args[index] as Expression),
                      call
                  );
        const kept = args.filter((arg): arg is CallExpression => isOwnSelector(this.#sites, arg, calculator) && !removable.has(arg as CallExpression));
        return kept.length === 0 ? value : at<Expression>({ type: "SequenceExpression", expressions: [...kept, value] }, call);
    }

    /**
     * Replace the calculations and remove dead selector calls, at the places the walk recorded (no other walk: the
     * replacements don't move anything, and removals from lists happen last, per list). Returns how many selector
     * calls went.
     */
    #rewrite(resolved: ReadonlyMap<Node, Resolution>, removable: ReadonlySet<CallExpression>): number {
        for (const resolution of resolved.values()) {
            const [place] = resolution.site.places;
            if (place !== undefined) putAt(place, this.#replacement(resolution, removable));
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
            else if (parent.type === "ExpressionStatement" && outer !== undefined) putAt(outer, at<Statement>({ type: "EmptyStatement" }, parent));
            else if (parent.type === "SequenceExpression" && own.index !== null && own.index < parent.expressions.length - 1 && outer !== undefined) prune(parent.expressions, call, outer);
            else putAt(own, valueToNode(undefined, call));
        }
        for (const [list, { gone, sequenceAt }] of pruned) {
            let length = 0;
            for (const node of list) if (!gone.has(node)) list[length++] = node;
            list.length = length;
            const [only] = list;
            if (sequenceAt !== undefined && length === 1 && only !== undefined) putAt(sequenceAt, only);
        }
        return removed;
    }
}

const putAt = ({ parent, key, index }: Place, node: Node): void => {
    const holder = parent as unknown as Record<string, Node | Node[]>;
    const slot = holder[key];
    if (index !== null && Array.isArray(slot)) slot[index] = node;
    else holder[key] = node;
};

const calledOrTested = (parent: Node, value: Node): boolean => {
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
};

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
