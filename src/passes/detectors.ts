import type { Expression, Function as FunctionNode, Node, Statement } from "../core/ast.js";
import { isFunctionNode, propertyKey } from "../core/ast.js";
import { constantEnv } from "../core/constants.js";
import type { EvaluateEnv } from "../core/evaluate.js";
import { evaluate } from "../core/evaluate.js";
import { at, valueToNode } from "../core/build.js";
import type { Primitive } from "../core/build.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Facts } from "../pipeline/facts.js";
import { factKey } from "../pipeline/facts.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { CallSite } from "./code-locks.js";
import { rewriteCalls, survey } from "./code-locks.js";
import type { Builder, Closure, Slot } from "./emulate/builders.js";
import { bodyOf, builderOf, definitionOf, returnsOf, sameSlot, slotOf, slotsOnly } from "./emulate/builders.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import { RUNTIME } from "./emulate/model.js";
import type { RuntimeModel } from "./emulate/model.js";
import type { StorageMatcher } from "./emulate/storage.js";

/**
 * Prelude statements `G.k = (function () {...})()` whose builder holds only anti-debug detectors and does nothing
 * else when it runs but set up their own state: cleanup may remove them once nothing reads `G.k` (semantic model 5:
 * the detectors go), whether or not the guest finished them.
 */
export const DETECTOR_BUILDERS = factKey<Set<Node>>("detector builders");

/** How a detector's answer follows from its report `R`: `R`, `!R` or `!!R`. */
type Transform = "value" | "not" | "boolean";

/**
 * What a detector's call answers when its report stays unset: exactly `value`, or a value as truthy as it. `literal`:
 * every detection stores a truthy literal.
 */
interface Answer {
    readonly value: Primitive;
    readonly exact: boolean;
    readonly literal: boolean;
}

interface Detector {
    readonly report: Slot;
    readonly transform: Transform;
    readonly answer: Answer;
    /** The functions only the detector's calls run (its probe or check, and what they hold). */
    readonly slowPaths: readonly FunctionNode[];
    /** The method's own code: writes to the report there would be its fast path's, not a detection's. */
    readonly fastPaths: readonly FunctionNode[];
    /** The writes to the report the shape itself allows in the fast path (a lazy probe's `catch (e) { R = false; }`). */
    readonly cleared: Node | undefined;
}

type Refusal = string;

/** `R`, `!R` or `!!R` with `R` a slot. */
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

/** The statements after the leading `var X = [arguments]`-style declarations (no initializer, or an array literal). */
const effective = (fn: Node): readonly Statement[] => {
    const statements = bodyOf(fn);
    const first = statements.findIndex((statement) => statement.type !== "VariableDeclaration" || !statement.declarations.every((d) => d.init === null || d.init.type === "ArrayExpression"));
    return first === -1 ? [] : statements.slice(first);
};

/** The one statement of a block, or the statement itself. */
const lone = (node: Node): Node | undefined => (node.type === "BlockStatement" ? (node.body.length === 1 ? node.body[0] : undefined) : node);

/** The callee of a call, looking through `(1, f)`. */
const calleeOf = (call: Node): Node | undefined => {
    if (call.type !== "CallExpression") return undefined;
    const callee = call.callee;
    if (callee.type !== "SequenceExpression") return callee;
    return callee.expressions.slice(0, -1).every((e) => e.type === "Literal") ? callee.expressions.at(-1) : undefined;
};

/** `S[i] = value;` as a statement: the slot, its member expression and the value. */
const slotStore = (statement: Node | undefined, scopes: ScopeInfo): { slot: Slot; target: Node; value: Expression } | undefined => {
    if (statement?.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.operator !== "=") return undefined;
    const target = statement.expression.left;
    const slot = slotOf(target, scopes);
    return slot === undefined ? undefined : { slot, target, value: statement.expression.right };
};

/** Every write to a slot of a local array in `root` (assignments, updates, deletes, destructuring), by node. */
const slotWrites = (root: Node, scopes: ScopeInfo): { slot: Slot; node: Node }[] => {
    const writes: { slot: Slot; node: Node }[] = [];
    traverse(root, {
        MemberExpression(path) {
            if (!path.isWriteTarget()) return;
            const slot = slotOf(path.node, scopes);
            if (slot !== undefined) writes.push({ slot, node: path.node });
        },
    });
    return writes;
};

/** The innermost function around `node` within the builder (`parents` covers it). */
const functionAround = (node: Node, parents: ReadonlyMap<Node, Node>): Node | undefined => {
    for (let current = parents.get(node); current !== undefined; current = parents.get(current)) if (isFunctionNode(current)) return current;
    return undefined;
};

/** A slot of an array declared by `owner` itself and kept to itself, starting out unset (past the initializer's elements). */
const ownSlot = (slot: Slot, owner: Node, parents: ReadonlyMap<Node, Node>): boolean => {
    if ((slot.variable.scope.block as unknown as Node) !== owner || !slotsOnly(slot.variable, parents)) return false;
    const declarator = slot.variable.defs[0]?.node as unknown as Node | undefined;
    return declarator?.type === "VariableDeclarator" && declarator.init?.type === "ArrayExpression" && Number(slot.index) >= declarator.init.elements.length;
};

/**
 * The lazy shape: `m: function () { if (!R) P(); return R; }`, with the probe `P` a function the builder declares
 * (its only reference is this call), the test `!R` or `R === undefined`, the call possibly in `try {...} catch (e) {}`
 * (or `catch (e) { R = false; }`), and the answer `R`, `!R` or `!!R`. Every call returns what the report holds after
 * the probe ran (or didn't).
 */
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
        variable.references.length !== 1
    ) {
        return "its probe isn't a function the builder declares and only it calls";
    }
    if (!ownSlot(read.slot, iife, parents)) return "its report isn't a slot of an array the builder keeps to itself";
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
 * The check `X[c]`'s every return is the report (`R`, `!R`, `!!R`). `X[d]` and `X[e]` are written only there, so the
 * first call writes `X[d]` either way (`X[e]` starts unset) and every call returns some call's check result.
 */
const timedDetector = ({ iife: maker, fn }: Closure, iife: FunctionNode, scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>): Omit<Detector, "answer"> | Refusal => {
    const shape = "it isn't the timed check: `if (N) D = C(N); else { t = B(); if (!E || t - E > K) { E = t; D = C(); } } return D;`";
    const statements = effective(fn);
    const [branch, ret] = statements;
    if (fn.async || fn.generator || statements.length !== 2 || branch?.type !== "IfStatement" || branch.alternate === null || ret?.type !== "ReturnStatement" || ret.argument === null) return shape;
    const own = (node: Node | undefined): Slot | undefined => {
        const slot = node === undefined ? undefined : slotOf(node, scopes);
        return slot !== undefined && ownSlot(slot, maker, parents) ? slot : undefined;
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
    const writes = slotWrites(iife, scopes);
    const count = (slot: Slot): number => writes.filter((write) => sameSlot(slot, write.slot)).length;
    if (count(result) !== 2 || count(stamp) !== 1) return "its cached result or time stamp is written elsewhere";
    const definitions = bodyOf(maker).map((statement) => slotStore(statement, scopes));
    const checkFn = definitions.find((store) => store !== undefined && sameSlot(check, store.slot))?.value;
    if (checkFn?.type !== "FunctionExpression" || checkFn.async || checkFn.generator || count(check) !== 1 || count(flag) !== 1 || count(clock) !== 1)
        return "its check, flag or clock isn't set once by the function that makes it";
    // The check is only called by the method.
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
    if (!ownSlot(read.slot, iife, parents)) return "its report isn't a slot of an array the builder keeps to itself";
    return { report: read.slot, transform: read.transform, slowPaths: [checkFn], fastPaths: [maker, fn], cleared: undefined };
};

/** A falsy literal a call can answer: `0`, `""`, `false`, `null`. */
const isFalsyLiteral = (node: Node): node is Node & { type: "Literal"; value: Primitive } =>
    node.type === "Literal" && !node.value && (node.value === null || typeof node.value === "number" || typeof node.value === "string" || typeof node.value === "boolean");

/**
 * Whether a report write is a detection's: it runs only when a check fires (in a branch of an `if`, `?:`, `&&`/`||`),
 * in a hook the slow path hands out (a function expression: a `toString`, a getter, an event listener only a
 * debugger triggers), or it stores a check's outcome (a comparison, `!`, `&&`/`||`). An unconditional store of
 * anything else in plain code is an initialization (a lazy `if (!R) init(); return R;`), not a detection.
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
 * What the detector answers while its report stays unset, from the writes to the report. The builder's own
 * statements may start it with falsy literals; every other write must be a detection's (`isDetection`), outside the
 * method's own code, and there must be one (it can report). `!R` then answers `true` and `!!R` `false`; `R` answers
 * exactly what the builder started it with when every detection stores a truthy literal (a detection code), and
 * some falsy value otherwise.
 */
const answerOf = (shape: Omit<Detector, "answer">, builder: Builder, iife: FunctionNode, scopes: ScopeInfo): Answer | Refusal => {
    let start: Primitive;
    let reports = 0;
    let literal = true;
    for (const { slot, node } of slotWrites(iife, scopes)) {
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
const GLOBAL_OBJECT_NAMES: ReadonlySet<string> = new Set(["globalThis", "window", "self"]);

/** `Object` or `globalThis.Object`, the global. */
const isObjectBuiltin = (node: Node, scopes: ScopeInfo): boolean =>
    (node.type === "Identifier" && node.name === "Object" && isGlobalName(node, scopes)) ||
    (node.type === "MemberExpression" && propertyKey(node) === "Object" && node.object.type === "Identifier" && GLOBAL_OBJECT_NAMES.has(node.object.name) && isGlobalName(node.object, scopes));

/** The root of a member chain. */
const rootOf = (node: Node): Node => {
    let root: Node = node;
    while (root.type === "MemberExpression") root = root.object;
    return root;
};
/**
 * Whether `node`, an identifier, is the global `name` stands for: a global reference, or (an identifier a pass put in
 * since the analysis, unknown to it) a name no scope of the program declares.
 */
const isGlobalName = (node: Node, scopes: ScopeInfo): boolean =>
    node.type === "Identifier" &&
    (scopes.isGlobalReference(node) || (scopes.referenceOf(node) === undefined && !scopes.manager.scopes.some((scope) => scope.type !== "global" && scope.set.has(node.name))));

/** Whether a member chain starts at a computing builtin (`Date.now`, `globalThis.Date.now`). */
const fromComputingBuiltin = (node: Node, scopes: ScopeInfo): boolean => {
    let first: Node | undefined;
    let root: Node = node;
    while (root.type === "MemberExpression") {
        first = root;
        root = root.object;
    }
    if (root.type !== "Identifier" || !isGlobalName(root, scopes)) return false;
    if (COMPUTING_GLOBALS.has(root.name)) return true;
    return GLOBAL_OBJECT_NAMES.has(root.name) && first?.type === "MemberExpression" && COMPUTING_GLOBALS.has(propertyKey(first) ?? "");
};

/** `x.toString` (or `x["toString"]`, before normalize writes it with a dot) */
const isToString = (node: Node): node is Node & { type: "MemberExpression"; object: Node } => node.type === "MemberExpression" && propertyKey(node) === "toString";

/**
 * Whether the builder does nothing when it runs but set up its own state, with every call into the runtime in the
 * detectors' slow paths (which only their calls run): outside them it assigns only to its own locals and their
 * objects, and calls only functions it defines (their bodies are checked with it), computing builtins, builtins'
 * reading methods on global values, and methods of literals (a call of anything else, `side()` or
 * `console.log(x)`, may have effects beyond the builder; so may a call through one of its own objects, which may
 * hold anything).
 */
const selfContained = (iife: FunctionNode, slowPaths: readonly FunctionNode[], parents: ReadonlyMap<Node, Node>, matcher: StorageMatcher, scopes: ScopeInfo): boolean => {
    /** Whether the member chain or name `node` starts at a binding of the builder's own. */
    const ownRoot = (node: Node): boolean => {
        const root = rootOf(node);
        const variable = root.type === "Identifier" ? scopes.variableOf(root) : undefined;
        let scope = variable?.scope ?? null;
        while (scope !== null && (scope.block as unknown as Node) !== iife) scope = scope.upper;
        return scope !== null;
    };
    /** The one value an own local holds: a function it declares, or its initializer when nothing else writes it. */
    const ownValue = (node: Node): Node | undefined => {
        const variable = node.type === "Identifier" && ownRoot(node) ? scopes.variableOf(node) : undefined;
        const [def] = variable?.defs ?? [];
        if (variable === undefined || def === undefined || variable.defs.length !== 1) return undefined;
        if (def.type === "FunctionName") return def.node as unknown as Node;
        const init = def.type === "Variable" ? (def.node as unknown as { init: Node | null }).init : null;
        return init === null || variable.references.some((reference) => reference.isWrite() && !reference.init) ? undefined : init;
    };
    /** Whether `node` is a global value: a member chain from a global name, also through own locals holding one. */
    const globalValue = (node: Node, visiting: ReadonlySet<Node> = new Set()): boolean => {
        const root = rootOf(node);
        if (root.type !== "Identifier") return false;
        if (isGlobalName(root, scopes)) return true;
        const value = ownValue(root);
        return value !== undefined && !visiting.has(value) && globalValue(value, new Set([...visiting, value]));
    };
    /** Values written to each slot of the builder's arrays (`W[4] = function () {...}`); undefined: also written otherwise. */
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
    /**
     * Whether calling the value `node` runs only code the builder defines or computing builtins (`Date.now.bind(Date)`).
     * `visiting`: the values being followed through locals and slots, so a cycle stops (as not harmless).
     */
    const harmlessFunction = (node: Node, visiting: ReadonlySet<Node>): boolean => {
        if (isFunctionNode(node) || fromComputingBuiltin(node, scopes)) return true;
        const follow = (value: Node): boolean => !visiting.has(value) && harmlessFunction(value, new Set([...visiting, value]));
        if (node.type === "Identifier") {
            const value = ownValue(node);
            return value !== undefined && follow(value);
        }
        // A bound function calls what it binds.
        if (node.type === "CallExpression" && node.callee.type === "MemberExpression" && propertyKey(node.callee) === "bind") return harmlessFunction(node.callee.object, visiting);
        const slot = ownRoot(node) ? slotOf(node, scopes) : undefined;
        const values = slot === undefined || !slotsOnly(slot.variable, parents) ? undefined : slotValues.get(slot.variable)?.get(slot.index);
        return values !== undefined && values.length > 0 && values.every(follow);
    };
    const harmlessCall = (callee: Node, args: readonly Node[]): boolean => {
        // `(1, f)(x)`: the call of `f` without a `this`.
        const target = callee.type === "SequenceExpression" && callee.expressions.slice(0, -1).every((e) => e.type === "Literal") ? (callee.expressions.at(-1) as Node) : callee;
        if (harmlessFunction(target, new Set())) return true;
        if (target.type !== "MemberExpression") return false;
        const root = rootOf(target);
        // A method of a literal or of what a harmless call returned (`Date.now.toString().indexOf("=>")`).
        if (root.type === "Literal" || ((root.type === "CallExpression" || root.type === "NewExpression") && harmlessCall(root.callee, root.arguments))) return true;
        const key = propertyKey(target);
        if (key !== undefined && READING_METHODS.has(key) && globalValue(target.object)) return true;
        // `Object.defineProperty(own, ...)`, `Object.defineProperties(fresh(), ...)`: only the builder's own object changes.
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

/** jscrambler's detection codes (`"j-016-00033"`) and the debugger interfaces its detectors probe. */
const DEBUGGER_STRINGS: ReadonlySet<string> = new Set(["inspector", "Debugger.paused", "Debugger.enable", "--inspect", "--debug", "execArgv"]);

/**
 * Whether the builder shows it detects a debugger: a detection code, a string or property naming a debugger interface,
 * a `toString` hook (a debugger's console calls it), or a native-code check of a builtin (`Date.now.toString()`).
 * Without one, a lazily computed report is just as likely a feature probe (`if (globalThis.FEATURE) r = 1`), which
 * model 5 says nothing about.
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
            // A hook through a computed key the builder sets to "toString" (a regex hook `o[k] = () => ...`).
            if (node.type === "AssignmentExpression" && node.left.type === "MemberExpression" && node.left.computed && isFunctionNode(node.right)) {
                const key = evaluate(node.left.property, env);
                if (key.ok && key.value === "toString") found = true;
            }
            if (node.type === "CallExpression" && isToString(node.callee) && node.callee.object.type === "MemberExpression" && fromComputingBuiltin(node.callee.object, scopes)) found = true;
        },
    });
    return found;
};

/** Follow builder statements through one-for-one replacements (see `Facts.replaced`). */
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

/** The detector at `path` (`[k, m]`): its builder statement and proof, or why it is none. */
const detectorAt = (
    path: PropertyPath,
    runtime: RuntimeModel,
    matcher: StorageMatcher,
    scopes: ScopeInfo,
    env: () => EvaluateEnv
): { statement: Statement; iife: FunctionNode; builder: Builder; detector: Detector } | Refusal | undefined => {
    const definition = definitionOf(runtime, matcher.isStorage, path.slice(0, 1), true);
    if (typeof definition === "string") return undefined;
    const builder = builderOf(definition.iife, scopes);
    if (typeof builder === "string") return undefined;
    const name = path[1] as string;
    const method = builder.methods.get(name);
    const closure = builder.closures.get(name);
    if (method === undefined && closure === undefined) return undefined;
    const shape = method !== undefined ? lazyDetector(method, definition.iife, scopes, builder.parents) : timedDetector(closure as Closure, definition.iife, scopes, builder.parents);
    if (typeof shape === "string") return shape;
    // The checks sit in the builder, in the method, or (timed detectors) in the function in the holder's literal making it.
    const searched = [definition.iife, ...(method === undefined ? [] : [method]), ...(closure === undefined ? [] : [closure.iife, closure.fn])];
    if (!searched.some((root) => probesDebugger(root, scopes, env()))) return "its builder shows no debugger check (no detection code, no debugger interface): it may probe a feature";
    const answer = answerOf(shape, builder, definition.iife, scopes);
    if (typeof answer === "string") return answer;
    return { statement: definition.statement, iife: definition.iife, builder, detector: { ...shape, answer } };
};

/**
 * Anti-debug detectors (semantic model 5, extended: the script isn't being debugged, so detectors report nothing).
 * jscrambler's j-016 family: methods of prelude builders `G.k = (function () {...})()` that keep a report in a slot of
 * the builder's own array and answer from it, through a slow path that probes the host (`require("inspector")`,
 * `process.execArgv`, console timing, `Date.now` source text, getters and `toString` hooks only a debugger's console
 * would call):
 *
 *     lazy:  m: function () { if (!R) P(); return R; }                          // R, !R or !!R; R === undefined
 *     timed: m: function () { ...; return function () { if (N) D = C(N); else { t = B(); if (!E || t - E > K)
 *                { E = t; D = C(); } } return D; }; }()                          // C returns R, !R or !!R
 *
 * Recognition (`lazyDetector`, `timedDetector`, `answerOf`): one of the two shapes exactly, a report the builder keeps
 * to itself and at most starts with falsy literals, set only past the fast path. Code locks (`if (S[j]) return L;`
 * with literal answers), string decoders, calculators and hash helpers take arguments or answer something else, so
 * they never fit. The report's truthy values are its detections, so under the model it stays falsy: every call,
 * the first included, answers `f(falsy)`: `!R` is `true`, `!!R` `false`, `R` the value the builder started it with
 * when every report write is a literal detection code (else only its falsiness is known: such a call is replaced only
 * where just its truthiness is used). Where the guest ran the builder, a guest call (no debugger, no `require`, no
 * `process`, no console) must answer the same, repeatably, or the detector is left alone.
 *
 * Each call (direct, or through a wrapper of it with no arguments; detectors ignore arguments and `this`) whose path
 * holds the builder's method when it runs (`staleAt` with the builder as `built`: later writes, or the builder not
 * having run yet) becomes the answer; a call statement goes. The probes' effects go with them (the model: console
 * output, timers re-running the checks, inspector sessions). The builder itself goes once nothing reads `G.k`
 * (`DETECTOR_BUILDERS`, for cleanup) when it holds only detectors and touches nothing but its own state when it runs.
 * Not exact under a debugger, or in Node where a detector would open an inspector session: accepted (model 5).
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
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
        const { calls } = survey(program, matcher, scopes);
        let constants: EvaluateEnv | undefined;
        const env = (): EvaluateEnv => (constants ??= constantEnv(scopes, log));

        // Call sites by detector path: direct calls and calls of its wrappers.
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
        const counts = { detectors: 0, answered: 0, removed: 0, kept: 0, builders: 0 };
        for (const { path, sites } of byTarget.values()) {
            const name = `${runtime.storage}.${path.join(".")}`;
            const found = detectorAt(path, runtime, matcher, scopes, env);
            if (found === undefined) continue; // no builder method at all: say nothing
            if (typeof found === "string") {
                log.debug(`${name} is no detector: ${found}`);
                continue;
            }
            const { statement, detector } = found;
            const { answer } = detector;
            const shown = answer.exact ? String(answer.value) : answer.value ? "a truthy value" : "a falsy value";
            // The guest isn't debugged: where it ran the builder, a call there must answer the same, repeatably.
            // Without its word, every detection must store a detection code (a truthy literal).
            const [probe] = runtime.executed.has(statement) ? runtime.guest.resolve([{ path, args: [] }]) : [];
            const confirmed =
                probe?.ok === true && !("nonPrimitive" in probe) && probe.repeatable && (answer.exact ? Object.is(probe.value, answer.value) : Boolean(probe.value) === Boolean(answer.value));
            if (probe?.ok === true && !confirmed) {
                log.debug(`${name} looks like a detector answering ${shown}, but the guest, which isn't debugged, doesn't answer that repeatably`, detector.slowPaths[0]);
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
                    // Where only truthiness counts, a boolean; else the value (`void 0`: `undefined` may be shadowed there).
                    const value = site.tested || !answer.exact ? Boolean(answer.value) : answer.value;
                    replacements.set(
                        site.call,
                        value === undefined
                            ? at<Expression>({ type: "UnaryExpression", operator: "void", prefix: true, argument: valueToNode(0, site.call) }, site.call)
                            : valueToNode(value, site.call)
                    );
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
            entry.slowPaths.push(...detector.slowPaths);
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
