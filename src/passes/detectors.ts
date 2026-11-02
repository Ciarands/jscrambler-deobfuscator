import type { Expression, Function as FunctionNode, Node, Statement } from "../core/ast.js";
import { isFunctionNode, propertyKey } from "../core/ast.js";
import { constantEnv } from "../core/constants.js";
import type { EvaluateEnv } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import { valueToNode } from "../core/build.js";
import type { Primitive } from "../core/build.js";
import { pushAll } from "../core/list.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { OWN_GLOBAL_OBJECT_NAMES, scopeWithin } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Facts } from "../pipeline/facts.js";
import { factKey } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { CallSite } from "./storage-usage.js";
import { rewriteCalls, survey } from "./storage-usage.js";
import type { Builder, Closure, Slot } from "./emulate/builders.js";
import { bodyOf, builderOf, definitionOf, returnsOf, sameSlot, slotOf, slotsOnly } from "./emulate/builders.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import type { RuntimeModel } from "./emulate/model.js";
import type { StorageMatcher } from "./emulate/storage.js";
import { assignedPaths, storageMatcher } from "./emulate/storage.js";

/** Builders `G.k = (function () {...})()` holding only anti-debug detectors: cleanup may remove them (model 5). */
export const DETECTOR_BUILDERS = factKey<Set<Node>>("detector builders");

type Transform = "value" | "not" | "boolean";

/** The answer while the report stays unset; `literal`: every detection stores a truthy literal. */
interface Answer {
    readonly value: Primitive;
    readonly exact: boolean;
    readonly literal: boolean;
}

interface Detector {
    readonly report: Slot;
    readonly transform: Transform;
    readonly answer: Answer;
    /** Functions only the detector's calls run. */
    readonly slowPaths: readonly FunctionNode[];
    /** The method's own code: report writes there aren't detections. */
    readonly fastPaths: readonly FunctionNode[];
    /** A report write the shape allows in the fast path (a lazy probe's `catch (e) { R = false; }`). */
    readonly cleared: Node | undefined;
}

type Refusal = string;

const reportRead = (node: Node | null | undefined, scopes: ScopeInfo): { slot: Slot; transform: Transform } | undefined => {
    if (node === null || node === undefined) return undefined;
    const slot = slotOf(node, scopes);
    if (slot !== undefined) return { slot, transform: "value" };
    if (node.type !== "UnaryExpression" || node.operator !== "!") return undefined;
    const inner = slotOf(node.argument, scopes);
    if (inner !== undefined) return { slot: inner, transform: "not" };
    const twice = node.argument.type === "UnaryExpression" && node.argument.operator === "!" ? slotOf(node.argument.argument, scopes) : undefined;
    return twice === undefined ? undefined : { slot: twice, transform: "boolean" };
};

/** `!R`, `R === undefined` (or `void 0`, either side): the report isn't set yet. */
const testsUnset = (test: Node, report: Slot, scopes: ScopeInfo): boolean => {
    if (test.type === "UnaryExpression" && test.operator === "!") return sameSlot(report, slotOf(test.argument, scopes));
    if (test.type !== "BinaryExpression" || test.operator !== "===") return false;
    const isUndefined = (node: Node): boolean =>
        (node.type === "Identifier" && node.name === "undefined" && scopes.isGlobalReference(node)) ||
        (node.type === "UnaryExpression" && node.operator === "void" && node.argument.type === "Literal");
    return (sameSlot(report, slotOf(test.left, scopes)) && isUndefined(test.right)) || (sameSlot(report, slotOf(test.right, scopes)) && isUndefined(test.left));
};

const effective = (fn: Node): readonly Statement[] => {
    const statements = bodyOf(fn);
    const first = statements.findIndex((statement) => statement.type !== "VariableDeclaration" || !statement.declarations.every((d) => d.init === null || d.init.type === "ArrayExpression"));
    return first === -1 ? [] : statements.slice(first);
};

const lone = (node: Node): Node | undefined => (node.type === "BlockStatement" ? (node.body.length === 1 ? node.body[0] : undefined) : node);

const calleeOf = (call: Node): Node | undefined => {
    if (call.type !== "CallExpression") return undefined;
    const callee = call.callee;
    if (callee.type !== "SequenceExpression") return callee;
    return callee.expressions.slice(0, -1).every((e) => e.type === "Literal") ? callee.expressions.at(-1) : undefined;
};

const slotStore = (statement: Node | undefined, scopes: ScopeInfo): { slot: Slot; target: Node; value: Expression } | undefined => {
    if (statement?.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return undefined;
    const target = statement.expression.left;
    const slot = slotOf(target, scopes);
    return slot === undefined ? undefined : { slot, target, value: statement.expression.right };
};

interface SlotWrite {
    readonly slot: Slot;
    readonly node: Node;
}

const slotWrites = (root: Node, scopes: ScopeInfo): SlotWrite[] => {
    const writes: SlotWrite[] = [];
    traverse(root, {
        MemberExpression(path) {
            if (!path.isWriteTarget()) return;
            const slot = slotOf(path.node, scopes);
            if (slot !== undefined) writes.push({ slot, node: path.node });
        },
    });
    return writes;
};

const functionAround = (node: Node, parents: ReadonlyMap<Node, Node>): Node | undefined => {
    for (let current = parents.get(node); current !== undefined; current = parents.get(current)) if (isFunctionNode(current)) return current;
    return undefined;
};

/** A slot of an array `owner` declares and keeps to itself, starting unset (past the initializer's elements). */
const ownSlot = (slot: Slot, owner: Node, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>): boolean => {
    if ((slot.variable.scope.block as unknown as Node) !== owner || !slotsOnly(slot.variable, scopes, parents)) return false;
    const declarator = slot.variable.defs[0]?.node as unknown as Node | undefined;
    return declarator?.type === "VariableDeclarator" && declarator.init?.type === "ArrayExpression" && Number(slot.index) >= declarator.init.elements.length;
};

/** The lazy shape: `m: function () { if (!R) P(); return R; }`, `P` a builder-declared function called only here. */
const lazyDetector = (fn: FunctionNode, iife: FunctionNode, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>): Omit<Detector, "answer"> | Refusal => {
    const statements = effective(fn);
    const [check, ret] = statements;
    if (fn.async || fn.generator || statements.length !== 2 || check?.type !== "IfStatement" || check.alternate !== null || ret?.type !== "ReturnStatement")
        return "it isn't `if (report unset) probe(); return report;`";
    const read = reportRead(ret.argument, scopes);
    if (read === undefined || !testsUnset(check.test, read.slot, scopes)) return "it doesn't return the report its test checks";
    let call = lone(check.consequent);
    let cleared: Node | undefined;
    if (call?.type === "TryStatement") {
        const { block, handler, finalizer } = call;
        const handled = handler === null ? [] : handler.body.body;
        const store = slotStore(handled[0], scopes);
        const clears = handled.length === 1 && store !== undefined && sameSlot(read.slot, store.slot) && store.value.type === "Literal" && store.value.value === false;
        if (finalizer !== null || handler === null || (handled.length > 0 && !clears)) return "its probe's try statement does more than ignore a failure";
        cleared = clears ? store?.target : undefined;
        call = lone(block);
    }
    const probe = call?.type === "ExpressionStatement" && call.expression.type === "CallExpression" && call.expression.arguments.length === 0 ? call.expression.callee : undefined;
    const variable = probe?.type === "Identifier" ? scopes.variableOf(probe) : undefined;
    const declaration = variable?.defs[0]?.node as unknown as Node | undefined;
    if (
        variable === undefined ||
        variable.defs.length !== 1 ||
        declaration?.type !== "FunctionDeclaration" ||
        !(bodyOf(iife) as readonly Node[]).includes(declaration) ||
        scopes.references(variable)?.length !== 1
    ) {
        return "its probe isn't a function the builder declares and only it calls";
    }
    if (!ownSlot(read.slot, iife, scopes, parents)) return "its report isn't a slot of an array the builder keeps to itself";
    return { report: read.slot, transform: read.transform, slowPaths: [declaration], fastPaths: [fn], cleared };
};

/**
 * The timed shape, a method an IIFE of the builder makes:
 *
 *     m: function () { X[c] = function (k) {...; return R; }; X[b] = Date.now.bind(Date); X[n] = ...;
 *         return function () {
 *             if (X[n]) X[d] = X[c](X[n]);
 *             else { t = X[b](); if (!X[e] || t - X[e] > 1500) { X[e] = t; X[d] = X[c](); } }
 *             return X[d];
 *         };
 *     }()
 *
 * `X[d]` and `X[e]` are written only there, so the first call writes `X[d]` either way (`X[e]` starts unset) and
 * every call returns some call's check result.
 */
const timedDetector = ({ iife: maker, fn }: Closure, iife: FunctionNode, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>, memo: BuilderMemo): Omit<Detector, "answer"> | Refusal => {
    const shape = "it isn't the timed check: `if (N) D = C(N); else { t = B(); if (!E || t - E > K) { E = t; D = C(); } } return D;`";
    const statements = effective(fn);
    const [branch, ret] = statements;
    if (fn.async || fn.generator || statements.length !== 2 || branch?.type !== "IfStatement" || branch.alternate === null || ret?.type !== "ReturnStatement" || ret.argument === null) return shape;
    const own = (node: Node | undefined): Slot | undefined => {
        const slot = node === undefined ? undefined : slotOf(node, scopes);
        return slot !== undefined && ownSlot(slot, maker, scopes, parents) ? slot : undefined;
    };
    const result = own(ret.argument);
    const flag = own(branch.test);
    const first = slotStore(lone(branch.consequent), scopes);
    const [timing, rerun, extra] = branch.alternate.type === "BlockStatement" ? branch.alternate.body : [];
    const now = slotStore(timing, scopes);
    if (
        result === undefined ||
        flag === undefined ||
        first === undefined ||
        !sameSlot(result, first.slot) ||
        now === undefined ||
        rerun?.type !== "IfStatement" ||
        rerun.alternate !== null ||
        extra !== undefined
    )
        return shape;
    const check = own(calleeOf(first.value));
    const clock = own(calleeOf(now.value));
    const flagged = first.value.type === "CallExpression" && first.value.arguments.length === 1 && sameSlot(flag, slotOf(first.value.arguments[0] as Node, scopes));
    const test = rerun.test;
    const stamp =
        test.type === "LogicalExpression" && test.operator === "||" && test.left.type === "UnaryExpression" && test.left.operator === "!" && test.right.type === "BinaryExpression"
            ? own(test.left.argument)
            : undefined;
    const [restamp, again] = rerun.consequent.type === "BlockStatement" && rerun.consequent.body.length === 2 ? rerun.consequent.body : [];
    const stamped = slotStore(restamp, scopes);
    const rechecked = slotStore(again, scopes);
    if (check === undefined || clock === undefined || !flagged || stamp === undefined || stamped === undefined || !sameSlot(stamp, stamped.slot) || !sameSlot(now.slot, slotOf(stamped.value, scopes)))
        return shape;
    const recheck = rechecked?.value;
    if (
        rechecked === undefined ||
        !sameSlot(result, rechecked.slot) ||
        recheck?.type !== "CallExpression" ||
        recheck.arguments.length !== 0 ||
        !sameSlot(check, slotOf(calleeOf(recheck) as Node, scopes))
    )
        return shape;

    // The result and the stamp are written only by the method; the check, flag and clock once, by the IIFE.
    const writes = memo.slotWrites(iife);
    const count = (slot: Slot): number => writes.filter((write) => sameSlot(slot, write.slot)).length;
    if (count(result) !== 2 || count(stamp) !== 1) return "its cached result or time stamp is written elsewhere";
    const definitions = bodyOf(maker).map((statement) => slotStore(statement, scopes));
    const checkFn = definitions.find((store) => store !== undefined && sameSlot(check, store.slot))?.value;
    if (checkFn?.type !== "FunctionExpression" || checkFn.async || checkFn.generator || count(check) !== 1 || count(flag) !== 1 || count(clock) !== 1)
        return "its check, flag or clock isn't set once by the function that makes it";
    let calls = 0;
    traverse(iife, {
        MemberExpression(path) {
            if (sameSlot(check, slotOf(path.node, scopes))) calls++;
        },
    });
    if (calls !== 3) return "its check is used other than by the method";

    const reads = returnsOf(checkFn).map((r) => (r.type === "ReturnStatement" ? reportRead(r.argument, scopes) : undefined));
    const [read] = reads;
    if (read === undefined || reads.some((other) => other === undefined || !sameSlot(read.slot, other.slot) || other.transform !== read.transform)) return "its check doesn't always return the report";
    if (!ownSlot(read.slot, iife, scopes, parents)) return "its report isn't a slot of an array the builder keeps to itself";
    return { report: read.slot, transform: read.transform, slowPaths: [checkFn], fastPaths: [maker, fn], cleared: undefined };
};

const isFalsyLiteral = (node: Node): node is Node & { type: "Literal"; value: Primitive } =>
    node.type === "Literal" && !node.value && (node.value === null || typeof node.value === "number" || typeof node.value === "string" || typeof node.value === "boolean");

/**
 * A detection runs only when a check fires (conditional branch), in a hook the slow path hands out, or stores a
 * check's outcome. An unconditional store of anything else is an initialization.
 */
const isDetection = (write: Node, value: Node | undefined, slowPaths: readonly Node[], parents: ReadonlyMap<Node, Node>): boolean => {
    if (
        value !== undefined &&
        (value.type === "LogicalExpression" ||
            (value.type === "UnaryExpression" && value.operator === "!") ||
            (value.type === "BinaryExpression" && /^[!=]==?$|^[<>]=?$|^in$|^instanceof$/.test(value.operator)))
    )
        return true;
    for (let child = write, parent = parents.get(write); parent !== undefined; child = parent, parent = parents.get(parent)) {
        if (parent.type === "FunctionDeclaration" || slowPaths.includes(parent)) return false;
        if (parent.type === "FunctionExpression" || parent.type === "ArrowFunctionExpression") return true;
        if ((parent.type === "IfStatement" || parent.type === "ConditionalExpression") && child !== parent.test) return true;
        if (parent.type === "LogicalExpression" && child === parent.right) return true;
    }
    return false;
};

/**
 * `!R` answers `true`, `!!R` `false`; `R` answers exactly its falsy start when every detection stores a truthy
 * literal, some falsy value otherwise.
 */
const answerOf = (shape: Omit<Detector, "answer">, builder: Builder, iife: FunctionNode, writes: readonly SlotWrite[]): Answer | Refusal => {
    // A report slot the builder never writes reads `undefined`.
    let start: Primitive = undefined;
    let reports = 0;
    let literal = true;
    for (const { slot, node } of writes) {
        if (!sameSlot(shape.report, slot) || node === shape.cleared) continue;
        const assignment = builder.parents.get(node);
        const value = assignment?.type === "AssignmentExpression" && assignment.operator === "=" && assignment.left === node ? assignment.right : undefined;
        const statement = assignment === undefined ? undefined : builder.parents.get(assignment);
        if (statement !== undefined && builder.statements.includes(statement as Statement)) {
            if (value === undefined || !isFalsyLiteral(value)) return "its builder starts the report with something other than a falsy literal";
            start = value.value;
            continue;
        }
        const around = functionAround(node, builder.parents);
        if (around !== undefined && shape.fastPaths.includes(around as FunctionNode)) return "the method itself writes the report";
        if (!isDetection(node, value, [...shape.slowPaths, iife], builder.parents)) return "its slow path sets the report unconditionally: an initialization, not a detection";
        reports++;
        if (value?.type !== "Literal" || !value.value) literal = false;
    }
    if (reports === 0) return "nothing ever sets its report";
    if (shape.transform === "not") return { value: true, exact: true, literal };
    if (shape.transform === "boolean") return { value: false, exact: true, literal };
    return { value: start, exact: literal && shape.cleared === undefined, literal };
};

/** Globals whose functions only compute (model 7): calling them while building can't reach beyond the builder. */
const COMPUTING_GLOBALS: ReadonlySet<string> = new Set([
    "Array",
    "String",
    "Number",
    "Boolean",
    "Math",
    "JSON",
    "Date",
    "RegExp",
    "Error",
    "parseInt",
    "parseFloat",
    "isNaN",
    "isFinite",
    "performance",
]);
/** Builtin methods that only read their receiver (`f.toString()`, `f.bind(x)`): harmless on any global value (model 7). */
const READING_METHODS: ReadonlySet<string> = new Set(["toString", "bind"]);

const isObjectBuiltin = (node: Node, scopes: ScopeInfo): boolean =>
    (node.type === "Identifier" && node.name === "Object" && scopes.namesGlobal(node)) ||
    (node.type === "MemberExpression" && propertyKey(node) === "Object" && node.object.type === "Identifier" && OWN_GLOBAL_OBJECT_NAMES[node.object.name] === true && scopes.namesGlobal(node.object));

const rootOf = (node: Node): Node => {
    let root: Node = node;
    while (root.type === "MemberExpression") root = root.object;
    return root;
};

const fromComputingBuiltin = (node: Node, scopes: ScopeInfo): boolean => {
    let first: Node | undefined;
    let root: Node = node;
    while (root.type === "MemberExpression") {
        first = root;
        root = root.object;
    }
    if (root.type !== "Identifier" || !scopes.namesGlobal(root)) return false;
    if (COMPUTING_GLOBALS.has(root.name)) return true;
    return OWN_GLOBAL_OBJECT_NAMES[root.name] === true && first?.type === "MemberExpression" && COMPUTING_GLOBALS.has(propertyKey(first) ?? "");
};

/** `x["toString"]` too: normalize may not have run. */
const isToString = (node: Node): node is Node & { type: "MemberExpression"; object: Node } => node.type === "MemberExpression" && propertyKey(node) === "toString";

/**
 * Outside the slow paths, the builder assigns only to its own locals and calls only its own functions, computing
 * builtins, reading methods on global values, and methods of literals. A call through its own objects may hold
 * anything, so it doesn't count.
 */
const selfContained = (iife: FunctionNode, slowPaths: readonly FunctionNode[], parents: ReadonlyMap<Node, Node>, matcher: StorageMatcher, scopes: ScopeInfo): boolean => {
    const ownRoot = (node: Node): boolean => {
        const root = rootOf(node);
        const variable = root.type === "Identifier" ? scopes.variableOf(root) : undefined;
        return scopeWithin(variable?.scope ?? null, iife);
    };
    const ownValue = (node: Node): Node | undefined => {
        const variable = node.type === "Identifier" && ownRoot(node) ? scopes.variableOf(node) : undefined;
        const [def] = variable?.defs ?? [];
        if (variable === undefined || def === undefined || variable.defs.length !== 1) return undefined;
        if (def.type === "FunctionName") return def.node as unknown as Node;
        const init = def.type === "Variable" ? (def.node as unknown as { init: Node | null }).init : null;
        const references = scopes.references(variable);
        return init === null || references === undefined || references.some((reference) => reference.isWrite() && !reference.init) ? undefined : init;
    };
    const globalValue = (node: Node, visiting: ReadonlySet<Node> = new Set()): boolean => {
        const root = rootOf(node);
        if (root.type !== "Identifier") return false;
        if (scopes.namesGlobal(root)) return true;
        const value = ownValue(root);
        return value !== undefined && !visiting.has(value) && globalValue(value, new Set([...visiting, value]));
    };
    /** undefined: the slot is also written other than by `=`. */
    const slotValues = new Map<Variable, Map<string, Node[] | undefined>>();
    traverse(iife, {
        MemberExpression(path) {
            if (!path.isWriteTarget()) return;
            const slot = slotOf(path.node, scopes);
            if (slot === undefined) return;
            const slots = slotValues.get(slot.variable) ?? new Map<string, Node[] | undefined>();
            slotValues.set(slot.variable, slots);
            const assignment = path.parent?.type === "AssignmentExpression" && path.key === "left" && path.parent.operator === "=" ? path.parent : undefined;
            const values = slots.has(slot.index) ? slots.get(slot.index) : [];
            slots.set(slot.index, assignment === undefined || values === undefined ? undefined : [...values, assignment.right]);
        },
    });
    /** `visiting` stops cycles (as not harmless). */
    const harmlessFunction = (node: Node, visiting: ReadonlySet<Node>): boolean => {
        if (isFunctionNode(node) || fromComputingBuiltin(node, scopes)) return true;
        const follow = (value: Node): boolean => !visiting.has(value) && harmlessFunction(value, new Set([...visiting, value]));
        if (node.type === "Identifier") {
            const value = ownValue(node);
            return value !== undefined && follow(value);
        }
        if (node.type === "CallExpression" && node.callee.type === "MemberExpression" && propertyKey(node.callee) === "bind") return harmlessFunction(node.callee.object, visiting);
        const slot = ownRoot(node) ? slotOf(node, scopes) : undefined;
        const values = slot === undefined || !slotsOnly(slot.variable, scopes, parents) ? undefined : slotValues.get(slot.variable)?.get(slot.index);
        return values !== undefined && values.length > 0 && values.every(follow);
    };
    const harmlessCall = (callee: Node, args: readonly Node[]): boolean => {
        const target = callee.type === "SequenceExpression" && callee.expressions.slice(0, -1).every((e) => e.type === "Literal") ? (callee.expressions.at(-1) as Node) : callee;
        if (harmlessFunction(target, new Set())) return true;
        if (target.type !== "MemberExpression") return false;
        const root = rootOf(target);
        if (root.type === "Literal" || ((root.type === "CallExpression" || root.type === "NewExpression") && harmlessCall(root.callee, root.arguments))) return true;
        const key = propertyKey(target);
        if (key !== undefined && READING_METHODS.has(key) && globalValue(target.object)) return true;
        // `Object.defineProperty(own, ...)`: only the builder's own object changes.
        const [first] = args;
        const ownObject =
            first !== undefined &&
            (((first.type === "CallExpression" || first.type === "NewExpression") && harmlessCall(first.callee, first.arguments)) || (first.type !== "SpreadElement" && ownRoot(first)));
        return (key === "defineProperty" || key === "defineProperties") && isObjectBuiltin(target.object, scopes) && ownObject;
    };
    let contained = true;
    traverse(iife, {
        enter(path) {
            if (!contained || slowPaths.includes(path.node as FunctionNode)) {
                path.skip();
                return;
            }
            const node = path.node;
            if (node.type === "Identifier" && matcher.isStorage(node)) contained = false;
            if (node.type === "AssignmentExpression" && !ownRoot(node.left)) contained = false;
            if (node.type === "UpdateExpression" && !ownRoot(node.argument)) contained = false;
            if ((node.type === "CallExpression" || node.type === "NewExpression") && !harmlessCall(node.callee, node.arguments)) contained = false;
            if (node.type === "TaggedTemplateExpression" && !ownRoot(node.tag)) contained = false;
        },
    });
    return contained;
};

/** Also matched: jscrambler's detection codes (`"j-016-00033"`). */
const DEBUGGER_STRINGS: ReadonlySet<string> = new Set(["inspector", "Debugger.paused", "Debugger.enable", "--inspect", "--debug", "execArgv"]);

/**
 * Without such a sign, a lazily computed report is as likely a feature probe, which model 5 says nothing about.
 */
const probesDebugger = (iife: FunctionNode, scopes: ScopeInfo, env: EvaluateEnv): boolean => {
    let found = false;
    traverse(iife, {
        enter(path) {
            const node = path.node;
            if (found) return path.skip();
            if (node.type === "Literal" && typeof node.value === "string" && (/^j-\d{3}-\d{5}$/.test(node.value) || DEBUGGER_STRINGS.has(node.value))) found = true;
            if (node.type === "MemberExpression" && DEBUGGER_STRINGS.has(propertyKey(node) ?? "")) found = true;
            if (node.type === "AssignmentExpression" && isToString(node.left)) found = true;
            if (node.type === "AssignmentExpression" && node.left.type === "MemberExpression" && node.left.computed && isFunctionNode(node.right)) {
                const key = evaluate(node.left.property, env);
                if (key.ok && key.value === "toString") found = true;
            }
            if (node.type === "CallExpression" && isToString(node.callee) && node.callee.object.type === "MemberExpression" && fromComputingBuiltin(node.callee.object, scopes)) found = true;
        },
    });
    return found;
};

/** Per run: a builder's detector methods share its definition and parse, and each function's slot writes and debugger signs. */
class BuilderMemo {
    readonly #runtime: RuntimeModel;
    readonly #matcher: StorageMatcher;
    readonly #scopes: ScopeInfo;
    readonly #env: () => EvaluateEnv;
    readonly #holders = new Map<string, { statement: Statement; iife: FunctionNode; builder: Builder } | undefined>();
    readonly #writes = new Map<Node, readonly SlotWrite[]>();
    readonly #probes = new Map<Node, boolean>();
    readonly #detectors = new Map<string, DetectorAt>();

    constructor(runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, env: () => EvaluateEnv) {
        this.#runtime = runtime;
        this.#matcher = matcher;
        this.#scopes = scopes;
        this.#env = env;
    }

    /** The prelude statement building the holder `key`, and its builder, when it has a builder's shape. */
    holder(key: string): { statement: Statement; iife: FunctionNode; builder: Builder } | undefined {
        if (this.#holders.has(key)) return this.#holders.get(key);
        const definition = definitionOf(this.#runtime, this.#matcher.isStorage, [key], true);
        const builder = typeof definition === "string" ? definition : builderOf(definition.iife, this.#scopes);
        const held = typeof definition === "string" || typeof builder === "string" ? undefined : { ...definition, builder };
        this.#holders.set(key, held);
        return held;
    }

    slotWrites(root: Node): readonly SlotWrite[] {
        let writes = this.#writes.get(root);
        if (writes === undefined) {
            writes = slotWrites(root, this.#scopes);
            this.#writes.set(root, writes);
        }
        return writes;
    }

    probesDebugger(root: FunctionNode): boolean {
        let probes = this.#probes.get(root);
        if (probes === undefined) {
            probes = probesDebugger(root, this.#scopes, this.#env());
            this.#probes.set(root, probes);
        }
        return probes;
    }

    /** What `detectorAt` makes of the method at `path`: the `shaped` pre-check and the main loop ask for the same paths. */
    detector(path: PropertyPath): DetectorAt {
        const id = JSON.stringify(path);
        if (this.#detectors.has(id)) return this.#detectors.get(id);
        const found = detectorAt(path, this, this.#scopes);
        this.#detectors.set(id, found);
        return found;
    }
}

const builderFact = (facts: Facts): Set<Node> => {
    const known = facts.get(DETECTOR_BUILDERS);
    if (known !== undefined) return known;
    const builders = new Set<Node>();
    facts.set(DETECTOR_BUILDERS, builders);
    facts.onReplace((originals, replacements) => {
        const [original] = originals;
        const [replacement] = replacements;
        if (originals.length === 1 && replacements.length === 1 && original !== undefined && replacement !== undefined && builders.delete(original)) builders.add(replacement);
    });
    return builders;
};

type DetectorAt = { statement: Statement; iife: FunctionNode; builder: Builder; detector: Detector } | Refusal | undefined;

const detectorAt = (path: PropertyPath, memo: BuilderMemo, scopes: ScopeInfo): DetectorAt => {
    const held = memo.holder(path[0] as string);
    if (held === undefined) return undefined;
    const { statement, iife, builder } = held;
    const name = path[1] as string;
    const method = builder.methods.get(name);
    const closure = builder.closures.get(name);
    if (method === undefined && closure === undefined) return undefined;
    const shape = method !== undefined ? lazyDetector(method, iife, scopes, builder.parents) : timedDetector(closure as Closure, iife, scopes, builder.parents, memo);
    if (typeof shape === "string") return shape;
    // A builder holding more than this method may hold a feature probe next to it: then only the detector's own code
    // may show the sign, not the builder's shared setup or a sibling's slow path.
    const searched = builder.methods.size + builder.closures.size === 1 ? [iife] : [...shape.slowPaths, ...shape.fastPaths];
    if (!searched.some((root) => memo.probesDebugger(root))) return "its code shows no debugger check (no detection code, no debugger interface): it may probe a feature";
    const answer = answerOf(shape, builder, iife, memo.slotWrites(iife));
    if (typeof answer === "string") return answer;
    return { statement, iife, builder, detector: { ...shape, answer } };
};

/**
 * Anti-debug detectors (semantic model 5: the script isn't debugged, so detectors report nothing). jscrambler's j-016
 * family keeps a report in a slot of the builder's own array:
 *
 *     lazy:  m: function () { if (!R) P(); return R; }                          // R, !R or !!R; R === undefined
 *     timed: m: function () { ...; return function () { if (N) D = C(N); else { t = B(); if (!E || t - E > K)
 *                { E = t; D = C(); } } return D; }; }()                          // C returns R, !R or !!R
 *
 * Code locks, decoders and helpers take arguments or answer otherwise, so they never fit. Under the model the report
 * stays falsy, so every call answers `f(falsy)`. Where the guest ran the builder, it must answer the same,
 * repeatably. Calls where the method is current (`staleAt`) become the answer; call statements go. Not exact under a
 * debugger or where a detector would open an inspector session: accepted (model 5).
 */
export const detectors: Pass = {
    name: "detectors",
    description: "Answer jscrambler's anti-debug detector calls with their no-detection answer (semantic model 5)",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.guest.broken !== undefined) {
            log.info("no usable runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const matcher = storageMatcher(program, runtime, scopes);
        let constants: EvaluateEnv | undefined;
        const env = (): EvaluateEnv => (constants ??= constantEnv(scopes, log));
        const memo = new BuilderMemo(runtime, matcher, scopes, env);
        const counts = { detectors: 0, answered: 0, removed: 0, kept: 0, builders: 0 };
        // Every call below that qualifies targets a method `detectorAt` accepts of a holder a root statement builds:
        // with no such method, none does, and neither the storage analysis nor the survey is needed.
        const shaped = assignedPaths(runtime, matcher.isStorage).some((path) => {
            const key = path[0] as string;
            const held = path.length === 1 ? memo.holder(key) : undefined;
            return held !== undefined && [...held.builder.methods.keys(), ...held.builder.closures.keys()].some((name) => typeof memo.detector([key, name]) === "object");
        });
        if (!shaped) {
            log.info("no builder method has a detector's shape");
            return { changed: 0, stats: counts };
        }
        const { effects } = storageAnalysis(program, runtime, scopes, log);
        const { calls } = survey(program, runtime, matcher, scopes);

        const byTarget = new Map<string, { path: PropertyPath; sites: { site: CallSite; wrapper: string | undefined }[] }>();
        for (const { path, sites } of calls.values()) {
            const wrapper = path.length === 1 ? runtime.wrappers.get(path[0] as string) : undefined;
            const target = wrapper?.target ?? path;
            if (target.length !== 2) continue;
            const id = JSON.stringify(target);
            const entry = byTarget.get(id) ?? { path: target, sites: [] };
            for (const site of sites) entry.sites.push({ site, wrapper: wrapper?.key });
            byTarget.set(id, entry);
        }

        const replacements = new Map<Node, Node>();
        const removals = new Set<Node>();
        const proven = new Map<Statement, { builder: Builder; iife: FunctionNode; names: Set<string>; slowPaths: FunctionNode[] }>();
        for (const { path, sites } of byTarget.values()) {
            const name = `${runtime.storage}.${path.join(".")}`;
            const found = memo.detector(path);
            if (found === undefined) continue; // no builder method at all: say nothing
            if (typeof found === "string") {
                log.debug(`${name} is no detector: ${found}`);
                continue;
            }
            const { statement, detector } = found;
            const { answer } = detector;
            const shown = answer.exact ? String(answer.value) : answer.value ? "a truthy value" : "a falsy value";
            // Without the guest's word, every detection must store a detection code.
            const [probe] = runtime.executed.has(statement) ? runtime.guest.resolve([{ path, args: [] }]) : [];
            const confirmed =
                probe?.ok === true && !("nonPrimitive" in probe) && probe.repeatable && (answer.exact ? Object.is(probe.value, answer.value) : Boolean(probe.value) === Boolean(answer.value));
            if (probe?.ok === true && !confirmed) {
                log.debug(`${name} looks like a detector answering ${shown}, but the guest, which isn't debugged, doesn't answer that repeatably`, detector.slowPaths[0]);
                continue;
            }
            // An answer that depends on the environment (time, host globals) confirms nothing, but one contradicting
            // the detector's answer still shows its check may fire undebugged.
            if (probe?.ok === false && probe.env === true && probe.seen !== undefined && (answer.exact ? !Object.is(probe.seen, answer.value) : Boolean(probe.seen) !== Boolean(answer.value))) {
                log.debug(`${name} looks like a detector answering ${shown}, but in the guest (${probe.error}) it answered otherwise`, detector.slowPaths[0]);
                continue;
            }
            if (!confirmed && !answer.literal) {
                log.debug(`${name} looks like a detector answering ${shown}, but the guest can't confirm it and it stores reports other than detection codes`, detector.slowPaths[0]);
                continue;
            }
            counts.detectors++;
            log.debug(`${name} is an anti-debug detector: undebugged, it answers ${shown}`, detector.slowPaths[0]);

            const tally = { answered: 0, removed: 0, kept: 0 };
            for (const { site, wrapper } of sites) {
                const stale = (wrapper === undefined ? undefined : effects.staleAt(site.site, [wrapper])) ?? effects.staleAt(site.site, path, false, statement);
                if (stale !== undefined) {
                    tally.kept++;
                    log.debug(`kept: ${stale.reason}`, stale.node);
                } else if (site.statement !== undefined) {
                    removals.add(site.statement);
                    tally.removed++;
                } else if (answer.exact || site.discarded || site.tested) {
                    const value = site.tested || !answer.exact ? Boolean(answer.value) : answer.value;
                    replacements.set(site.call, valueToNode(value, site.call));
                    tally.answered++;
                } else {
                    tally.kept++;
                    log.debug("kept: its value is used, and only the answer's falsiness is known", site.call);
                }
            }
            log.info(`${name}: answered ${tally.answered} call(s), removed ${tally.removed}, kept ${tally.kept}`, statement);
            counts.answered += tally.answered;
            counts.removed += tally.removed;
            counts.kept += tally.kept;
            const entry = proven.get(statement) ?? { builder: found.builder, iife: found.iife, names: new Set<string>(), slowPaths: [] };
            entry.names.add(path[1] as string);
            pushAll(entry.slowPaths, detector.slowPaths);
            proven.set(statement, entry);
        }

        const builders = builderFact(facts);
        for (const [statement, { builder, iife, names, slowPaths }] of proven) {
            const all = [...builder.methods.keys(), ...builder.closures.keys()].every((name) => names.has(name));
            if (!all || !selfContained(iife, slowPaths, builder.parents, matcher, scopes)) {
                log.debug(`builder stays for cleanup's own rules: ${all ? "it does more than set up its own state when it runs" : "it holds more than detectors"}`, statement);
                continue;
            }
            builders.add(statement);
            counts.builders++;
        }

        rewriteCalls(program, replacements, removals);
        log.info(`${counts.detectors} detector(s): answered ${counts.answered} call(s), removed ${counts.removed}, kept ${counts.kept}; ${counts.builders} builder(s) may go`);
        return { changed: counts.answered + counts.removed, bindingsChanged: false, stats: counts };
    },
};
