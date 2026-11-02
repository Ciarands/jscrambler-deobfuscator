import type { CallExpression, MemberExpression, Node, Statement } from "../../core/ast.js";
import { isFunctionNode, propertyKey } from "../../core/ast.js";
import type { Value } from "../../core/evaluate.js";
import { binary, evaluate, unary } from "../../core/evaluate.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { forEachChild } from "../../core/traverse.js";
import { pathName } from "./model.js";
import type { RuntimeModel } from "./model.js";
import { realm } from "./realm.js";
import type { StorageMatcher } from "./storage.js";

/**
 * What a root statement does, in evaluation order: a call of the decoder (made exactly once, unconditionally, with
 * constant arguments; the walk is sent back what it gives), or the first point where code may run, or be skipped,
 * that this walk doesn't follow (`stop`).
 */
export type OrderEvent = { readonly kind: "call"; readonly call: CallExpression; readonly args: readonly Value[] } | { readonly kind: "stop"; readonly reason: string; readonly node: Node };

/** A walk: its events, and the decoder calls' values sent back. */
type Walk<T> = Generator<OrderEvent, T, Value>;

export interface OrderContext {
    readonly scopes: ScopeInfo;
    readonly matcher: StorageMatcher;
    readonly runtime: RuntimeModel;
    /** Whether a call is one of the decoder's: through one of its wrappers, or of its target `G.k.m`. */
    readonly decoderCall: (call: CallExpression) => boolean;
    /** Whether `G[key]` holds the decoder's holder (a plain object its builder made). */
    readonly holder: (key: string) => boolean;
    /** Why writing the storage key `key` at `write` may change what the decoder's calls do (its holder, its wrappers). */
    readonly guarded: (key: string, write: Node) => string | undefined;
    /** Members of `G` and of the holder the walk read, for the caller. */
    readonly seen: Set<Node>;
}

/** How a statement list went: it stopped, returned on every path, returned on some, or goes on. */
type Flow = "stop" | "return" | "partial" | "next";

/** An expression the walk can't tell the value of (objects, reads, calls run in place). */
const UNKNOWN: unique symbol = Symbol("unknown");
/** The walk stopped in an expression. */
const STOPPED: unique symbol = Symbol("stopped");
type Walked = Value | typeof UNKNOWN | typeof STOPPED;

const unparenthesized = (node: Node): Node => (node.type === "ParenthesizedExpression" ? unparenthesized(node.expression) : node);

/** Whether `node` holds a `return` of its own function (not of a nested one). */
const returns = (node: Node): boolean => {
    if (node.type === "ReturnStatement") return true;
    let found = false;
    forEachChild(node, (child) => {
        if (!found && !isFunctionNode(child)) found = returns(child);
    });
    return found;
};

/** Why an object literal isn't plain: accessors, spreads, computed or `__proto__` keys. */
const notPlain = (node: Node & { type: "ObjectExpression" }): string | undefined => {
    for (const property of node.properties) {
        if (property.type !== "Property") return "it spreads into an object";
        if (property.kind !== "init") return "it defines an accessor";
        if (property.computed && property.key.type !== "Literal") return "it computes a key";
        const name = property.key.type === "Identifier" ? property.key.name : property.key.type === "Literal" ? String(property.key.value) : undefined;
        if (!property.computed && !property.shorthand && name === "__proto__") return "it sets a prototype";
    }
    return undefined;
};

const isPlainLiteral = (node: Node | null | undefined): boolean => node?.type === "ArrayExpression" || (node?.type === "ObjectExpression" && notPlain(node) === undefined);

const known = (value: Walked): value is Value => value !== UNKNOWN && value !== STOPPED;

function* halt(reason: string, node: Node): Walk<typeof STOPPED> {
    yield { kind: "stop", reason, node };
    return STOPPED;
}

/** Values no operator converts by calling program code: primitives (and results of operators, which are). */
const primitive = (node: Node): boolean => {
    const inner = unparenthesized(node);
    switch (inner.type) {
        case "Literal":
            return !("regex" in inner);
        case "TemplateLiteral":
        case "UnaryExpression":
        case "BinaryExpression":
            return true;
        case "LogicalExpression":
            return primitive(inner.left) && primitive(inner.right);
        case "ConditionalExpression":
            return primitive(inner.consequent) && primitive(inner.alternate);
        default:
            return false;
    }
};

/**
 * Walks the code a root statement runs in place (its top level and the bodies of functions it calls right there) in
 * evaluation order, yielding the decoder's calls, until it meets something whose effects it doesn't follow: then it
 * yields `stop` and ends. Followed: literals, names, functions made but not called, plain array and object literals,
 * operators that convert only primitives (or nothing: `===`, `!`, `typeof`, `void`, `&&`), plain assignments, reads
 * and writes of `G`'s static keys other than the setup's (its keys, aliases on `Function.prototype` and
 * `Object.prototype`), reads of the decoder's holder, writes to the global object's static keys other than setup
 * globals and what the page model (`realm.ts`) has as an accessor or a read-only property (see `access` for model 10),
 * reads and writes of plain arrays and objects the code made, `if` and `return`. Where a test's value follows from
 * literals and the decoder's results (operators on primitives, `evaluate.ts`), only the branch it takes runs; otherwise
 * either may. Builtins are intact (model 7): none of their properties is an accessor running program code, none has
 * index properties. Anything else that may call (but the decoder, and functions called right there), construct,
 * convert an object, delete, loop or leave the root function stops.
 */
export function* statementOrder(cx: OrderContext, statement: Statement): Walk<void> {
    const ended = yield* statements([statement], false);
    if (ended === "return" || ended === "partial") yield { kind: "stop", reason: "it may end the runtime's function", node: statement };

    function* statements(list: readonly Node[], conditional: boolean): Walk<Flow> {
        let maybe = conditional;
        let partial = false;
        for (const node of list) {
            const flow = yield* statementOf(node, maybe);
            if (flow === "stop" || flow === "return") return flow;
            if (flow === "partial") {
                maybe = true;
                partial = true;
            }
        }
        return partial ? "partial" : "next";
    }

    function* statementOf(node: Node, conditional: boolean): Walk<Flow> {
        switch (node.type) {
            case "ExpressionStatement":
                return (yield* expression(node.expression, conditional)) === STOPPED ? "stop" : "next";
            case "VariableDeclaration":
                for (const declarator of node.declarations) {
                    if (declarator.id.type !== "Identifier") {
                        yield* halt("it destructures", declarator);
                        return "stop";
                    }
                    if (declarator.init !== null && (yield* expression(declarator.init, conditional)) === STOPPED) return "stop";
                }
                return "next";
            case "FunctionDeclaration":
            case "EmptyStatement":
                return "next";
            case "BlockStatement":
                return yield* statements(node.body, conditional);
            case "ReturnStatement":
                return node.argument === null || (yield* expression(node.argument, conditional)) !== STOPPED ? "return" : "stop";
            case "IfStatement": {
                const test = yield* expression(node.test, conditional);
                if (test === STOPPED) return "stop";
                if (known(test)) {
                    const taken = test ? node.consequent : node.alternate;
                    return taken === null ? "next" : yield* statements([taken], conditional);
                }
                const consequent = yield* statements([node.consequent], true);
                if (consequent === "stop") return "stop";
                const alternate = node.alternate === null ? "next" : yield* statements([node.alternate], true);
                if (alternate === "stop") return "stop";
                if (consequent === "return" && alternate === "return") return "return";
                return returns(node) ? "partial" : "next";
            }
            default:
                yield* halt(`it runs a ${node.type}`, node);
                return "stop";
        }
    }

    function* all(nodes: readonly Node[], conditional: boolean): Walk<Walked> {
        let last: Walked = undefined;
        for (const node of nodes) {
            last = yield* expression(node, conditional);
            if (last === STOPPED) return STOPPED;
        }
        return last;
    }

    function* expression(node: Node, conditional: boolean): Walk<Walked> {
        switch (node.type) {
            case "Literal":
                return "regex" in node || typeof node.value === "bigint" ? UNKNOWN : (node.value as Value);
            case "Identifier":
            case "ThisExpression":
            case "FunctionExpression":
            case "ArrowFunctionExpression":
                return UNKNOWN;
            case "TemplateLiteral": {
                const [quasi] = node.quasis;
                if (node.expressions.length > 0) return yield* halt("its template converts values", node);
                return quasi?.value.cooked ?? UNKNOWN;
            }
            case "ParenthesizedExpression":
                return yield* expression(node.expression, conditional);
            case "SequenceExpression":
                return yield* all(node.expressions, conditional);
            case "ArrayExpression": {
                const elements: Node[] = [];
                for (const element of node.elements) {
                    if (element?.type === "SpreadElement") return yield* halt("it spreads", node);
                    if (element !== null) elements.push(element);
                }
                return (yield* all(elements, conditional)) === STOPPED ? STOPPED : UNKNOWN;
            }
            case "ObjectExpression": {
                const why = notPlain(node);
                if (why !== undefined) return yield* halt(why, node);
                const values = node.properties.map((property) => (property as Node & { type: "Property" }).value);
                return (yield* all(values, conditional)) === STOPPED ? STOPPED : UNKNOWN;
            }
            case "LogicalExpression": {
                const left = yield* expression(node.left, conditional);
                if (left === STOPPED) return STOPPED;
                if (!known(left)) return (yield* expression(node.right, true)) === STOPPED ? STOPPED : UNKNOWN;
                const done = node.operator === "&&" ? !left : node.operator === "||" ? Boolean(left) : left !== null && left !== undefined;
                return done ? left : yield* expression(node.right, conditional);
            }
            case "ConditionalExpression": {
                const test = yield* expression(node.test, conditional);
                if (test === STOPPED) return STOPPED;
                if (known(test)) return yield* expression(test ? node.consequent : node.alternate, conditional);
                if ((yield* expression(node.consequent, true)) === STOPPED || (yield* expression(node.alternate, true)) === STOPPED) return STOPPED;
                return UNKNOWN;
            }
            case "UnaryExpression": {
                if (node.operator === "delete") return yield* halt("it deletes", node);
                // `typeof name` reads no binding that may be missing.
                const operand = node.operator === "typeof" && node.argument.type === "Identifier" ? UNKNOWN : yield* expression(node.argument, conditional);
                if (operand === STOPPED) return STOPPED;
                if (known(operand)) {
                    const result = unary(node.operator, operand);
                    return result.ok ? result.value : UNKNOWN;
                }
                const converts = node.operator !== "typeof" && node.operator !== "void" && node.operator !== "!";
                return !converts || primitive(node.argument) ? UNKNOWN : yield* halt(`${node.operator} may convert an object`, node);
            }
            case "BinaryExpression": {
                if (node.operator === "in" || node.operator === "instanceof") return yield* halt(`it uses ${node.operator}`, node);
                const left = yield* expression(node.left, conditional);
                if (left === STOPPED) return STOPPED;
                const right = yield* expression(node.right, conditional);
                if (right === STOPPED) return STOPPED;
                // `**` is approximated differently by engines.
                if (known(left) && known(right) && node.operator !== "**") {
                    const result = binary(node.operator, left, right);
                    return result.ok ? result.value : UNKNOWN;
                }
                const converts = node.operator !== "===" && node.operator !== "!==";
                const plain = (side: Walked, operand: Node): boolean => known(side) || primitive(operand);
                return !converts || (plain(left, node.left) && plain(right, node.right)) ? UNKNOWN : yield* halt(`${node.operator} may convert an object`, node);
            }
            case "AssignmentExpression": {
                if (node.operator !== "=") return yield* halt(`it assigns with ${node.operator}`, node);
                const target = node.left;
                if (target.type === "Identifier") {
                    if (cx.scopes.variableOf(target) === undefined) return yield* halt(`it assigns the global ${target.name}`, node);
                    return yield* expression(node.right, conditional);
                }
                if (target.type !== "MemberExpression") return yield* halt("it destructures", node);
                if ((yield* memberParts(target, conditional)) === STOPPED) return STOPPED;
                const value = yield* expression(node.right, conditional);
                if (value === STOPPED) return STOPPED;
                const why = access(target, true);
                return why === undefined ? value : yield* halt(why, target);
            }
            case "MemberExpression": {
                if ((yield* memberParts(node, conditional)) === STOPPED) return STOPPED;
                const why = access(node, false);
                return why === undefined ? UNKNOWN : yield* halt(why, node);
            }
            case "CallExpression":
                return yield* call(node, conditional);
            default:
                return yield* halt(`it uses ${node.type}`, node);
        }
    }

    function* memberParts(node: MemberExpression, conditional: boolean): Walk<Walked> {
        if ((yield* expression(node.object, conditional)) === STOPPED) return STOPPED;
        return node.computed ? yield* expression(node.property, conditional) : UNKNOWN;
    }

    function* call(node: CallExpression, conditional: boolean): Walk<Walked> {
        if (node.optional) return yield* halt("it calls optionally", node);
        if (cx.decoderCall(node)) {
            const args: Value[] = [];
            for (const arg of node.arguments) {
                const value = arg.type === "SpreadElement" ? undefined : evaluate(arg);
                if (value?.ok !== true) return yield* halt("a decoder call's argument isn't constant", node);
                args.push(value.value);
            }
            if (conditional) return yield* halt("a decoder call may or may not run", node);
            return yield { kind: "call", call: node, args };
        }
        const callee = unparenthesized(node.callee);
        if (callee.type !== "FunctionExpression" && callee.type !== "ArrowFunctionExpression") return yield* halt("it calls something that may call the decoder", node);
        if (callee.async || callee.generator || !callee.params.every((param) => param.type === "Identifier")) return yield* halt("it calls a function whose call runs more than its body", node);
        // Called right here, once: its arguments, then its body.
        if ((yield* all(node.arguments, conditional)) === STOPPED) return STOPPED;
        if (callee.body === null) return yield* halt("it calls a function without a body", node);
        if (callee.body.type !== "BlockStatement") return (yield* expression(callee.body, conditional)) === STOPPED ? STOPPED : UNKNOWN;
        return (yield* statements(callee.body.body, conditional)) === "stop" ? STOPPED : UNKNOWN;
    }

    /** A function's local whose every write puts down a plain array or object literal. */
    function freshLocal(node: Node): Variable | undefined {
        const variable = node.type === "Identifier" ? cx.scopes.variableOf(node) : undefined;
        if (variable === undefined || variable.scope.type === "global" || variable.scope.type === "module") return undefined;
        const literals = cx.scopes.staticReferences(variable).every((reference) => !reference.isWrite() || isPlainLiteral(reference.writeExpr as unknown as Node | null | undefined));
        return literals ? variable : undefined;
    }

    /** `local` or `local[k]` where every write of that slot (and none by a computed key) puts down a plain literal. */
    function fresh(node: Node): boolean {
        if (freshLocal(node) !== undefined) return true;
        if (node.type !== "MemberExpression") return false;
        const slot = propertyKey(node);
        const variable = freshLocal(node.object);
        if (slot === undefined || variable === undefined) return false;
        return cx.scopes.staticReferences(variable).every((reference) => {
            if (reference.isWrite()) return true;
            const id = reference.identifier as unknown as Node;
            const member = cx.scopes.parentOf(id);
            if (member?.type !== "MemberExpression" || member.object !== id) return false;
            const above = cx.scopes.parentOf(member);
            const written = (above?.type === "AssignmentExpression" && above.left === member) || above?.type === "UpdateExpression";
            if (!written) return true;
            const key = propertyKey(member);
            if (key !== slot) return key !== undefined;
            return above?.type === "AssignmentExpression" && above.operator === "=" && isPlainLiteral(above.right);
        });
    }

    /** Why reading or writing `member` may run code: an accessor this walk can't rule out. */
    function access(member: MemberExpression, write: boolean): string | undefined {
        const { runtime, matcher } = cx;
        const key = propertyKey(member);
        const object = unparenthesized(member.object);
        const aliased = (owners: readonly string[], name: string): boolean =>
            runtime.unprovenAliases.has(name) || runtime.aliases.some((alias) => owners.includes(pathName(alias.owner)) && alias.alias === name);
        if (matcher.isStorage(object)) {
            cx.seen.add(member);
            if (key === undefined) return `it uses a computed key of ${runtime.storage}`;
            if (runtime.setupKeys.has(key)) return `${runtime.storage}.${key} is a property the setup defined`;
            if (aliased(["Function.prototype", "Object.prototype"], key)) return `${runtime.storage}.${key} may be an alias's accessor`;
            return write ? cx.guarded(key, member) : undefined;
        }
        const slot = object.type === "MemberExpression" && matcher.isStorage(unparenthesized(object.object)) ? propertyKey(object) : undefined;
        if (slot !== undefined && cx.holder(slot)) {
            cx.seen.add(member);
            return write ? `it writes the decoder's holder ${runtime.storage}.${slot}` : undefined;
        }
        if (slot !== undefined && runtime.globalKeys.has(slot)) {
            if (!write || key === undefined || runtime.setupGlobals.has(key) || runtime.hostAliases.has(key) || aliased(["Object.prototype"], key))
                return `it ${write ? "writes" : "reads"} ${key ?? "a computed key"} of the global object`;
            // An accessor of the page model (`__proto__`) runs code; a read-only property ignores the write. Model 10 as
            // this reads it: the page's globals the script depends on are the builtins and those its host aliases forward;
            // any other name is a plain property the write adds (a page's own accessor, `location`, isn't modelled).
            const found = realm().lookup([], key);
            return found.kind === "accessor" || (found.kind === "data" && !found.writable) ? `it writes ${key} of the global object, an accessor or a read-only property` : undefined;
        }
        if (!fresh(object)) return `it ${write ? "writes" : "reads"} a property of something that may have accessors`;
        if (key === undefined) return "it uses a computed key";
        if (key === "__proto__" || aliased(["Object.prototype", "Array.prototype"], key)) return `${key} may be an accessor`;
        return undefined;
    }
}
