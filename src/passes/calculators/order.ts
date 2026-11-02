import type { CallExpression, Expression, Function as FunctionNode, Node } from "../../core/ast.js";
import { isFunctionNode, memberPath, propertyKey } from "../../core/ast.js";
import type { EvaluateEnv } from "../../core/evaluate.js";
import { evaluate } from "../../core/evaluate.js";
import type { ScopeInfo } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { PassContext } from "../../pipeline/pass.js";
import { builderOf, definitionOf } from "../emulate/builders.js";
import type { StorageEffects } from "../emulate/effects.js";
import type { RuntimeModel } from "../emulate/model.js";
import type { LocalReads } from "./locals.js";
import type { Calculator, Resolution, Site, Sites } from "./sites.js";
import { isOwnSelector } from "./sites.js";

export type Search = { readonly kind: "found"; readonly selector: Site } | { readonly kind: "stop"; readonly reason: string; readonly node: Node };

export interface OrderContext {
    readonly runtime: RuntimeModel;
    readonly isStorage: (node: Node) => boolean;
    readonly effects: StorageEffects;
    readonly scopes: ScopeInfo;
    readonly env: EvaluateEnv;
    readonly log: PassContext["log"];
}

/**
 * Evaluation order around the calculator calls in `sites`: the selector call a calculation follows (`selectorBefore`),
 * whether a selector call's value is overwritten before anything reads it (`overwrittenAfter`), and whether the
 * arguments put into a case's expression are read as the calculation reads them (`readOrderProblem`, `orderProblem`).
 */
export class EvaluationOrder {
    readonly #isolated = new Map<Node, boolean>();
    #provisional: Node[] | undefined;

    constructor(
        readonly sites: Sites,
        readonly locals: LocalReads,
        readonly context: OrderContext
    ) {}

    /**
     * The selector call the calculation at `site` follows: walking back in evaluation order from the call (its own
     * arguments first, then what its ancestors evaluate before it), staying in the function and on every path (no loop
     * bodies, no other branch, no `case` bodies). Explicit code (a call, `new`, a store that may hit a setter) stops
     * the search; code that runs implicitly (getters, `valueOf`/`toString` of converted objects) is passed: it doesn't
     * use the calculator (model 8), so the selector's value is still the state when the calculation reads it.
     */
    selectorBefore(site: Site): Search {
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
            const site = this.sites.get(node);
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
                const test = evaluate(node.test, this.context.env);
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
                return this.locals.localStore(node.argument) ? undefined : { reason: "an update of a property or global (possible setter)", node };
            case "AssignmentExpression":
                // A compound operator's read and conversion of a local run code only implicitly (model 8).
                return this.locals.localStore(node.left) ? this.#explicitCode(node.right, calculator) : { reason: "a property or global write (possible setter)", node };
            case "CallExpression": {
                const site = this.sites.get(node);
                if (!node.arguments.every((arg) => arg.type !== "SpreadElement")) return { reason: "a call", node };
                const passed = site !== undefined && (site.role === "calculation" || site.calculator !== calculator);
                if (passed || this.#quietCall(node)) return all(node.arguments as Expression[]);
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
        const { runtime, isStorage, effects, scopes, log } = this.context;
        if (call.callee.type !== "MemberExpression") return false;
        const path = memberPath(call.callee);
        if (path === undefined || !isStorage(path.root)) return false;
        const [first] = path.keys;
        const wrapper = path.keys.length === 1 && first !== undefined ? runtime.wrappers.get(first) : undefined;
        const target = wrapper?.target ?? path.keys;
        if (target.length !== 2 || (wrapper !== undefined && effects.staleAt(path.root, path.keys) !== undefined) || effects.staleAt(path.root, target) !== undefined) return false;
        const info = runtime.guest.inspect(target);
        if (info?.data !== true || info.type !== "function" || effects.preludeWritesTo(target) !== 1) return false;
        const definition = definitionOf(runtime, isStorage, target.slice(0, 1));
        if (typeof definition === "string") return false;
        const builder = builderOf(definition.iife, scopes);
        const fn = typeof builder === "string" ? undefined : builder.methods.get(target[1] as string);
        const quiet = fn !== undefined && this.#cannotReachSelector(fn);
        if (quiet) log.debug(`call passed: ${runtime.storage}.${target.join(".")} can't reach a selector call`, call);
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

    #localFunction(identifier: Node): Node | undefined {
        const variable = this.context.scopes.variableOf(identifier);
        const [def] = variable?.defs ?? [];
        if (variable === undefined || variable.defs.length !== 1 || def === undefined) return undefined;
        if (def.type === "FunctionName") return def.node as unknown as Node;
        if (def.type !== "Variable" || this.context.scopes.references(variable)?.filter((reference) => reference.isWrite()).length !== 1) return undefined;
        const init = (def.node as unknown as Node & { type: "VariableDeclarator" }).init;
        return init !== null && isFunctionNode(init) ? init : undefined;
    }

    /**
     * Whether the value the selector call at `site` stores is overwritten before anything can read it: walking on in
     * evaluation order from the call, on every path (no branch, loop or function end), through quiet code only
     * (`#quiet`: it can't run code or throw, so control surely gets on), another selector call of the calculator comes.
     * Calculations `resolved` no longer read the state. Model 8 doesn't help here: a getter may throw, and then the
     * value stays in the state for whatever calculation runs next, which no selector call of ours precedes.
     */
    overwrittenAfter(site: Site, resolved: ReadonlyMap<Node, Resolution>): boolean {
        const { calculator } = site;
        const pass = (node: Node | null | undefined): boolean | undefined => {
            if (node === null || node === undefined) return undefined;
            if (isOwnSelector(this.sites, node, calculator)) return after((node as CallExpression).arguments, 0) ?? true;
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
                    result = parent.operator === "=" && key === "right" && this.locals.localStore(parent.left) ? undefined : false;
                    break;
                case "BlockStatement":
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
        if (!args.every((arg) => isOwnSelector(this.sites, arg, site.calculator) || evaluate(arg, this.context.env).ok)) return false;
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
        if (evaluate(node, this.context.env).ok) return true;
        switch (node.type) {
            case "Literal":
            case "ThisExpression":
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return true;
            case "Identifier":
                return this.locals.safeBinding(node);
            case "MemberExpression":
                return this.locals.slotRead(node);
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
                return node.operator === "=" && this.locals.localStore(node.left) && this.#quiet(node.right, resolved);
            case "CallExpression": {
                const resolution = resolved.get(node);
                if (resolution !== undefined) return this.#quietFormula(resolution);
                return this.sites.get(node)?.role === "selector" && node.arguments.every((arg) => arg.type !== "SpreadElement" && this.#quiet(arg, resolved));
            }
            default:
                return this.#quietPrimitive(node, resolved);
        }
    }

    #quietPrimitive(node: Node, resolved: ReadonlyMap<Node, Resolution>): boolean {
        if (evaluate(node, this.context.env).ok) return true;
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

    readsOnly(node: Node): boolean {
        switch (node.type) {
            case "Literal":
            case "Identifier":
            case "ThisExpression":
                return true;
            case "MemberExpression":
                return node.object.type !== "Super" && this.readsOnly(node.object) && (!node.computed || this.readsOnly(node.property));
            default:
                return false;
        }
    }

    /**
     * Why putting getter arguments (`getters`, by index) into the case's expression would change what runs: the
     * calculation reads every argument once, in order, before computing. In place, each non-constant argument must
     * then be read once, in that order, and surely (no `&&`/`||`/`?:` to skip it): getters run as they did, and none
     * can change a local or slot read before or after it out of turn. (The formula's own conversions come after the
     * reads: `orderProblem`.)
     */
    readOrderProblem(formula: Expression | undefined, args: readonly Expression[], getters: ReadonlySet<number>, calculator: Calculator): string | undefined {
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
                if (arg !== undefined && !isOwnSelector(this.sites, arg, calculator) && !evaluate(arg, this.context.env).ok) reads.push(index);
            },
        });
        if (branches) return "might not be read (the case's expression branches)";
        if ([...getters].some((index) => !reads.includes(index))) return "would not be read";
        return reads.every((index, i) => i === 0 || index > (reads[i - 1] as number)) ? undefined : "would be read out of turn (twice, or before an earlier argument)";
    }

    /**
     * Why the case's expression can't take the arguments in place of `a[i]`: in the calculation every argument is
     * read before the expression runs; in place, a non-constant one is read where the expression reaches it. That is
     * the same as long as no conversion that could run code (an operator applied to a possible object: not to one that
     * only ever holds primitives, `LocalReads.primitive`) comes first, or the argument reads the same after any code
     * (`LocalReads.stableAcrossCalls`).
     */
    orderProblem(formula: Expression, args: readonly Expression[], calculator: Calculator): string | undefined {
        let converted = false;
        let problem: string | undefined;
        /** Returns whether the value may be an object. */
        const visit = (node: Node): boolean => {
            switch (node.type) {
                case "MemberExpression": {
                    const arg = args[Number(propertyKey(node))];
                    if (arg === undefined || isOwnSelector(this.sites, arg, calculator) || evaluate(arg, this.context.env).ok) return false;
                    if (converted && !this.locals.stableAcrossCalls(arg)) problem ??= "an argument would be read after a conversion that may run code";
                    return !this.locals.primitive(arg);
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
}
