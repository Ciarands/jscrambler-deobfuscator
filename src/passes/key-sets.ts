import type { Expression, Node } from "../core/ast.js";
import { propertyKey } from "../core/ast.js";
import type { Value } from "../core/evaluate.js";
import { binary } from "../core/evaluate.js";
import type { ScopeInfo, Variable } from "../core/scope.js";

/** Keys a computed read may select: one of `strings`, or any string made only of `chars`. */
export interface KeySet {
    readonly strings: ReadonlySet<string>;
    readonly chars: ReadonlySet<string> | undefined;
}

export const mayName = (keys: KeySet, key: string): boolean => keys.strings.has(key) || (keys.chars !== undefined && key.split("").every((char) => keys.chars?.has(char)));

/** The elements an array may hold: those written to it (holes, and reads past its end, are `undefined` besides). */
interface ArraySource {
    readonly elements: readonly Expression[];
}

/**
 * What an expression may evaluate to: one of `prims`, any number (`numbers`), a string made only of `chars`, one of
 * `arrays`, or `String.fromCharCode`. `undefined` (top) when it may be anything else.
 */
interface Abstract {
    readonly prims: ReadonlySet<Value>;
    readonly numbers: boolean;
    readonly chars: ReadonlySet<string> | undefined;
    readonly arrays: ReadonlySet<ArraySource>;
    readonly fromCharCode: boolean;
}

/** More values than this and an abstract value gives up: a key set that large selects nearly anything anyway. */
const MAX_PRIMS = 1024;

const NUMBER_CHARS: ReadonlySet<string> = new Set("0123456789.-+eInfinityNaN".split(""));

const EMPTY: Abstract = { prims: new Set(), numbers: false, chars: undefined, arrays: new Set(), fromCharCode: false };
const prims = (...values: Value[]): Abstract => ({ ...EMPTY, prims: new Set(values) });
const ANY_NUMBER: Abstract = { ...EMPTY, numbers: true };

const union = (a: Abstract | undefined, b: Abstract | undefined): Abstract | undefined => {
    if (a === undefined || b === undefined) return undefined;
    const values = new Set([...a.prims, ...b.prims]);
    if (values.size > MAX_PRIMS) return undefined;
    const chars = a.chars === undefined ? b.chars : b.chars === undefined ? a.chars : new Set([...a.chars, ...b.chars]);
    return { prims: values, numbers: a.numbers || b.numbers, chars, arrays: new Set([...a.arrays, ...b.arrays]), fromCharCode: a.fromCharCode || b.fromCharCode };
};

/** Only primitives (no "any number", strings of characters, arrays or functions). */
const onlyPrims = (a: Abstract): boolean => !a.numbers && a.chars === undefined && a.arrays.size === 0 && !a.fromCharCode;

/** Only arrays (or `undefined`/`null`, whose members can't be read: reading one throws, giving no value). */
const arraysOnly = (a: Abstract): boolean => a.arrays.size > 0 && !a.numbers && a.chars === undefined && !a.fromCharCode && [...a.prims].every((v) => v === undefined || v === null);

const numeric = (a: Abstract): boolean => a.chars === undefined && a.arrays.size === 0 && !a.fromCharCode && [...a.prims].every((v) => typeof v === "number");

const UNARY: Readonly<Record<string, ((v: Value) => Value) | undefined>> = {
    "-": (v) => -Number(v),
    "+": (v) => Number(v),
    "~": (v) => ~Number(v),
    "!": (v) => !v,
};

const COMPARISONS: Record<string, true> = { "==": true, "!=": true, "===": true, "!==": true, "<": true, "<=": true, ">": true, ">=": true };

/** Characters `String(v)` (or, in a join, the element `v`: `undefined` and `null` add nothing) may have. */
const charsOf = (a: Abstract, inJoin: boolean): Set<string> | undefined => {
    if (a.arrays.size > 0 || a.fromCharCode) return undefined;
    const chars = new Set<string>(a.chars ?? []);
    if (a.numbers) for (const char of NUMBER_CHARS) chars.add(char);
    for (const v of a.prims) if (!inJoin || (v !== undefined && v !== null)) for (const char of String(v).split("")) chars.add(char);
    return chars;
};

/**
 * The keys computed reads may select, from a flow-insensitive abstract evaluation over the function they sit in.
 * Built for jscrambler's decoder probe:
 *
 *     do { key = c.sort(function () { return 0.5 - random(); }).join(""); found = G[key]; } while (!found);
 *
 * A variable holds any of its writes or `undefined`; a parameter what any call passes, when its function is only
 * called directly by name and doesn't use `arguments`; a local array whatever its element writes put there, when it
 * is only read, written by element, sorted or joined. Relies on model 7 (builtins intact, no index properties on
 * their prototypes). Anything else is top.
 */
export const keySets = (scopes: ScopeInfo, parents: ReadonlyMap<Node, Node>): ((key: Expression) => KeySet | undefined) => {
    const withScope = scopes.manager.scopes.some((scope) => scope.type === "with");
    const values = new Map<Variable, Abstract | undefined>();
    const sources = new Map<Node | Variable, ArraySource | undefined>();
    const pending = new Set<Variable>();

    /** Whether `node` is the global `name`: an identifier a pass made since the analysis names it when no scope declares the name. */
    const isGlobal = (node: Node, name: string): boolean =>
        node.type === "Identifier" && node.name === name && !withScope && (scopes.isGlobalReference(node) || (scopes.referenceOf(node) === undefined && !scopes.declaresName(name)));

    const parentOf = (id: Node): Node | undefined => parents.get(id);

    /** A local array declared with a literal and used only in ways that leave its elements to the writes `V[k] = v`. */
    const arraySource = (variable: Variable): ArraySource | undefined => {
        if (sources.has(variable)) return sources.get(variable);
        let source: ArraySource | undefined;
        const [def] = variable.defs;
        const declarator = def?.node as unknown as Node | undefined;
        if (variable.defs.length === 1 && def?.type === "Variable" && declarator?.type === "VariableDeclarator" && declarator.init?.type === "ArrayExpression") {
            const elements: Expression[] = [];
            let ok = true;
            for (const element of declarator.init.elements) {
                if (element?.type === "SpreadElement") ok = false;
                else if (element !== null) elements.push(element);
            }
            for (const reference of scopes.staticReferences(variable)) {
                if (!ok) break;
                if (reference.init) continue;
                const id = reference.identifier as unknown as Node;
                const member = parentOf(id);
                const above = member === undefined ? undefined : parentOf(member);
                if (member?.type !== "MemberExpression" || member.object !== id) ok = false;
                else if (above?.type === "AssignmentExpression" && above.left === member) {
                    if (above.operator === "=") elements.push(above.right);
                    else ok = false;
                } else if (above?.type === "CallExpression" && above.callee === member) ok = propertyKey(member) === "sort" || propertyKey(member) === "join";
                else if (above?.type === "UpdateExpression" || (above?.type === "UnaryExpression" && above.operator === "delete")) ok = false;
                else if (above?.type === "TaggedTemplateExpression" && above.tag === member) ok = false;
                else if (above?.type === "ArrayPattern" || above?.type === "RestElement" || above?.type === "ForInStatement" || above?.type === "ForOfStatement") ok = false;
            }
            if (ok) source = { elements };
        }
        sources.set(variable, source);
        return source;
    };

    const literalSource = (node: Node): ArraySource | undefined => {
        if (sources.has(node)) return sources.get(node);
        const elements: Expression[] = [];
        let ok = node.type === "ArrayExpression";
        if (node.type === "ArrayExpression") {
            for (const element of node.elements) {
                if (element?.type === "SpreadElement") ok = false;
                else if (element !== null) elements.push(element);
            }
        }
        const source = ok ? { elements } : undefined;
        sources.set(node, source);
        return source;
    };

    /** Whether every use of the parameter `variable` reads it (as a member object, not written or called through). */
    const readOnly = (variable: Variable): boolean =>
        scopes.staticReferences(variable).every((reference) => {
            const id = reference.identifier as unknown as Node;
            const member = parentOf(id);
            const above = member === undefined ? undefined : parentOf(member);
            if (member?.type !== "MemberExpression" || member.object !== id) return false;
            if (above?.type === "CallExpression" && above.callee === member) return false;
            if (above?.type === "AssignmentExpression" && above.left === member) return false;
            return above?.type !== "UpdateExpression" && !(above?.type === "UnaryExpression" && above.operator === "delete");
        });

    /** What a parameter may hold: what every (direct) call passes, or `undefined` when it passes nothing there. */
    const parameterValues = (variable: Variable): Abstract | undefined => {
        const [def] = variable.defs;
        const fn = def?.node as unknown as Node | undefined;
        if (variable.defs.length !== 1 || fn === undefined || (fn.type !== "FunctionExpression" && fn.type !== "FunctionDeclaration" && fn.type !== "ArrowFunctionExpression")) return undefined;
        const index = fn.params.findIndex((param) => param === (def?.name as unknown as Node));
        if (index < 0 || fn.params.slice(0, index).some((param) => param.type !== "Identifier")) return undefined;
        if (fn.type !== "ArrowFunctionExpression" && (scopes.scopeOf(fn)?.set.get("arguments")?.references.length ?? 0) > 0) return undefined;
        // Every read of the function's bindings (its holder, and its own name inside a named function expression)
        // must be a direct call, except reads after a later declarator of the same declaration replaced the holder
        // (`var r = function (e) {...}, s = r(k), r = s;`): with no other read, `s` can't be the function.
        const parent = parentOf(fn);
        const holder = fn.type === "FunctionDeclaration" ? fn.id : parent?.type === "VariableDeclarator" && parent.init === fn ? parent.id : undefined;
        const binding = holder?.type === "Identifier" ? scopes.staticVariableOf(holder) : undefined;
        if (binding === undefined || !binding.defs.every((d) => d.type === "Variable" || d.type === "FunctionName")) return undefined;
        const ownName = fn.type === "FunctionExpression" && fn.id !== null ? scopes.variableOf(fn.id) : undefined;
        const replacedFrom = Math.min(
            Number.POSITIVE_INFINITY,
            ...binding.defs.filter((d) => parent !== undefined && d.parent === parentOf(parent) && (d.node as unknown as Node).start > parent.start).map((d) => (d.node as unknown as Node).end)
        );
        let result: Abstract | undefined = EMPTY;
        let hasArrays = false;
        const reads = [
            ...scopes.staticReferences(binding).map((reference) => ({ reference, ofHolder: true })),
            ...(ownName === undefined ? [] : scopes.staticReferences(ownName).map((reference) => ({ reference, ofHolder: false }))),
        ];
        for (const { reference, ofHolder } of reads) {
            if (reference.isWrite() && !reference.isRead()) continue;
            const id = reference.identifier as unknown as Node;
            const call = parentOf(id);
            if (ofHolder && id.start >= replacedFrom && reference.from.variableScope === binding.scope.variableScope) continue;
            if (call?.type !== "CallExpression" || call.callee !== id) return undefined;
            const args = call.arguments;
            if (args.slice(0, index + 1).some((arg) => arg.type === "SpreadElement")) return undefined;
            const arg = args[index] as Expression | undefined;
            const literal = arg?.type === "ArrayExpression" ? literalSource(arg) : undefined;
            if (arg?.type === "ArrayExpression" && literal === undefined) return undefined;
            const value = arg === undefined ? prims(undefined) : literal !== undefined ? { ...EMPTY, arrays: new Set([literal]) } : abstract(arg);
            if (value !== undefined && value.arrays.size > 0) hasArrays = true;
            result = union(result, value);
        }
        // A literal handed over is reached only through the parameter: it holds its elements if nothing writes through it.
        if (hasArrays && !readOnly(variable)) return undefined;
        return union(result, writesOf(variable));
    };

    const writesOf = (variable: Variable): Abstract | undefined => {
        let result: Abstract | undefined = EMPTY;
        for (const reference of scopes.staticReferences(variable)) {
            if (!reference.isWrite() || reference.init) continue;
            const id = reference.identifier as unknown as Node;
            const above = parentOf(id);
            if (above?.type === "AssignmentExpression" && above.operator === "=" && above.left === id) result = union(result, abstract(above.right));
            else if (above?.type === "UpdateExpression") result = union(result, ANY_NUMBER);
            else return undefined;
        }
        return result;
    };

    const valuesOf = (variable: Variable): Abstract | undefined => {
        if (values.has(variable)) return values.get(variable);
        if (pending.has(variable)) return undefined;
        pending.add(variable);
        let result: Abstract | undefined;
        const [def] = variable.defs;
        if (def?.type === "Parameter") result = parameterValues(variable);
        else if (def?.type === "Variable" && variable.defs.every((d) => d.type === "Variable")) {
            const source = arraySource(variable);
            // A `var` is `undefined` until its initializer runs.
            result = source !== undefined ? { ...EMPTY, arrays: new Set([source]) } : union(prims(undefined), writesOf(variable));
            for (const d of source === undefined ? variable.defs : []) {
                const declarator = d.node as unknown as Node;
                if (declarator.type === "VariableDeclarator" && declarator.init !== null) result = union(result, abstract(declarator.init));
            }
        }
        pending.delete(variable);
        values.set(variable, result);
        return result;
    };

    const elementRead = (object: Abstract, key: Abstract | undefined): Abstract | undefined => {
        if (key === undefined || !arraysOnly(object) || key.chars !== undefined || key.arrays.size > 0 || key.fromCharCode) return undefined;
        // Keys other than strings name no property of an array but its elements (`"undefined"`, `"1.5"`, `"true"`).
        if ([...key.prims].some((v) => typeof v === "string" && !/^(0|[1-9]\d*)$/.test(v))) return undefined;
        let result: Abstract | undefined = prims(undefined);
        for (const source of object.arrays) for (const element of source.elements) result = union(result, abstract(element));
        return result;
    };

    const call = (node: Node): Abstract | undefined => {
        if (node.type !== "CallExpression") return undefined;
        const callee = node.callee;
        const method = callee.type === "MemberExpression" && !callee.computed ? propertyKey(callee) : undefined;
        if (callee.type === "MemberExpression" && (method === "sort" || method === "join")) {
            const object = abstract(callee.object);
            if (object === undefined || !arraysOnly(object)) return undefined;
            if (method === "sort") return node.arguments.length <= 1 && node.arguments.every((arg) => arg.type === "FunctionExpression" || arg.type === "ArrowFunctionExpression") ? object : undefined;
            if (node.arguments.length > 1) return undefined;
            const separator = node.arguments[0];
            const sepValue = separator === undefined ? prims(",") : separator.type === "SpreadElement" ? undefined : abstract(separator);
            const sepChars = sepValue === undefined ? undefined : charsOf({ ...sepValue, prims: new Set([...sepValue.prims].map((v) => (v === undefined ? "," : v))) }, false);
            let chars = sepChars;
            for (const source of object.arrays) {
                for (const element of source.elements) {
                    const value = abstract(element);
                    const elementChars = value === undefined ? undefined : charsOf(value, true);
                    chars = chars === undefined || elementChars === undefined ? undefined : new Set([...chars, ...elementChars]);
                }
            }
            return chars === undefined ? undefined : { ...EMPTY, chars };
        }
        const fn = abstract(callee);
        // `undefined`/`null` callees throw: no value.
        if (fn === undefined || !fn.fromCharCode || fn.numbers || fn.chars !== undefined || fn.arrays.size > 0 || [...fn.prims].some((v) => v !== undefined && v !== null)) return undefined;
        if (node.arguments.length !== 1 || node.arguments[0]?.type === "SpreadElement") return undefined;
        const arg = abstract(node.arguments[0] as Expression);
        if (arg === undefined || !onlyPrims(arg)) return undefined;
        return prims(...[...arg.prims].map((v) => String.fromCharCode(Number(v))));
    };

    const abstract = (node: Node): Abstract | undefined => {
        switch (node.type) {
            case "Literal": {
                const v: unknown = node.value;
                return v === null || typeof v === "string" || typeof v === "number" || typeof v === "boolean" ? prims(v) : undefined;
            }
            case "Identifier": {
                if (isGlobal(node, "undefined")) return prims(undefined);
                const variable = scopes.staticVariableOf(node);
                return variable === undefined ? undefined : valuesOf(variable);
            }
            case "MemberExpression": {
                if (isGlobal(node.object, "String") && propertyKey(node) === "fromCharCode") return { ...EMPTY, fromCharCode: true };
                const object = abstract(node.object);
                if (object === undefined) return undefined;
                return elementRead(object, node.computed ? abstract(node.property) : undefined);
            }
            case "CallExpression":
                return call(node);
            case "UnaryExpression": {
                // Operators on primitives run no code: `-49`, `!x`.
                const operate = UNARY[node.operator];
                const argument = operate === undefined ? undefined : abstract(node.argument);
                if (operate === undefined || argument === undefined) return undefined;
                if (onlyPrims(argument)) return prims(...[...argument.prims].map(operate));
                return numeric(argument) ? (node.operator === "!" ? prims(true, false) : ANY_NUMBER) : undefined;
            }
            case "BinaryExpression": {
                if (node.left.type === "PrivateIdentifier" || node.operator === "in" || node.operator === "instanceof") return undefined;
                const left = abstract(node.left);
                const right = abstract(node.right);
                if (left === undefined || right === undefined) return undefined;
                if (!onlyPrims(left) || !onlyPrims(right)) return numeric(left) && numeric(right) ? (COMPARISONS[node.operator] === true ? prims(true, false) : ANY_NUMBER) : undefined;
                if (left.prims.size * right.prims.size > MAX_PRIMS) return undefined;
                const results: Value[] = [];
                for (const l of left.prims) {
                    for (const r of right.prims) {
                        const result = binary(node.operator, l, r);
                        if (!result.ok) return undefined;
                        results.push(result.value);
                    }
                }
                return prims(...results);
            }
            case "ConditionalExpression":
                return union(abstract(node.consequent), abstract(node.alternate));
            case "LogicalExpression":
                return union(abstract(node.left), abstract(node.right));
            case "SequenceExpression":
                return abstract(node.expressions.at(-1) as Expression);
            case "AssignmentExpression":
                return node.operator === "=" ? abstract(node.right) : undefined;
            default:
                return undefined;
        }
    };

    return (key) => {
        if (withScope) return undefined;
        const value = abstract(key);
        if (value === undefined || value.arrays.size > 0 || value.fromCharCode) return undefined;
        const chars = value.chars !== undefined || value.numbers ? charsOf({ ...value, prims: new Set() }, false) : undefined;
        return { strings: new Set([...value.prims].map((v) => String(v))), chars };
    };
};
