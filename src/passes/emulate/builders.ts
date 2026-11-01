import type { Function as FunctionNode, Node, Statement } from "../../core/ast.js";
import { isFunctionNode, isIndexKey, memberPath, propertyKey } from "../../core/ast.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { PropertyPath } from "./guest.js";
import type { RuntimeModel } from "./model.js";
import { rootStatements } from "./storage.js";

export interface Slot {
    readonly variable: Variable;
    readonly index: string;
}

/** A method an immediately invoked function makes: `m: function () {...; return function () {...}; }()`. */
export interface Closure {
    readonly iife: FunctionNode;
    readonly fn: FunctionNode;
}

export interface Builder {
    readonly methods: ReadonlyMap<string, FunctionNode>;
    /** Methods made by a function invoked in the literal (not in `methods`). */
    readonly closures: ReadonlyMap<string, Closure>;
    readonly parents: ReadonlyMap<Node, Node>;
    readonly statements: readonly Statement[];
}

/** Of a non-computed object-literal key (`a`, `"a"`, `1`). */
const keyName = (key: Node): string | undefined => {
    if (key.type === "Identifier") return key.name;
    if (key.type === "Literal" && (typeof key.value === "string" || typeof key.value === "number")) return String(key.value);
    return undefined;
};

export const slotOf = (node: Node, scopes: ScopeInfo): Slot | undefined => {
    if (node.type !== "MemberExpression" || node.object.type !== "Identifier") return undefined;
    const index = propertyKey(node);
    const variable = scopes.variableOf(node.object);
    return index === undefined || !isIndexKey(index) || variable === undefined ? undefined : { variable, index };
};

export const sameSlot = (a: Slot, b: Slot | undefined): boolean => b !== undefined && a.variable === b.variable && a.index === b.index;

export const bodyOf = (fn: Node): readonly Statement[] => ((fn.type === "FunctionExpression" || fn.type === "FunctionDeclaration") && fn.body !== null ? fn.body.body : []);

/** Not counting returns of nested functions. */
export const returnsOf = (fn: Node): Node[] => {
    const found: Node[] = [];
    traverse(fn, {
        enter(path) {
            if (path.node !== fn && isFunctionNode(path.node)) path.skip();
        },
        ReturnStatement(path) {
            found.push(path.node);
        },
    });
    return found;
};

export const parentsWithin = (root: Node): Map<Node, Node> => {
    const parents = new Map<Node, Node>();
    traverse(root, {
        enter(path) {
            if (path.parent !== null) parents.set(path.node, path.parent);
        },
    });
    return parents;
};

/** A local array declared once, used only as `S[index]`: its slots hold only what is written to them. */
export const slotsOnly = (variable: Variable, parents: ReadonlyMap<Node, Node>): boolean =>
    variable.defs.length === 1 &&
    variable.references.every((reference) => {
        if (reference.init) return true;
        const identifier = reference.identifier as unknown as Node;
        const member = parents.get(identifier);
        return member?.type === "MemberExpression" && member.object === identifier && isIndexKey(propertyKey(member) ?? "");
    });

/**
 * A builder function declaration, or a top-level `var f = function () {...}` before the returning statement, bound by
 * nothing else.
 */
const localFunction = (value: Node, statements: readonly Statement[], returning: Node, scopes: ScopeInfo): FunctionNode | undefined => {
    const variable = value.type === "Identifier" ? scopes.variableOf(value) : undefined;
    const [def] = variable?.defs ?? [];
    if (variable === undefined || def === undefined || variable.defs.length !== 1) return undefined;
    const writes = scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length;
    const node = def.node as unknown as Node;
    if (node.type === "FunctionDeclaration") return writes === 0 && statements.includes(node) ? node : undefined;
    if (node.type !== "VariableDeclarator" || node.init?.type !== "FunctionExpression" || writes !== 1) return undefined;
    const index = statements.indexOf(def.parent as unknown as Statement);
    return index !== -1 && index < statements.indexOf(returning as Statement) ? node.init : undefined;
};

/**
 * The object an immediately invoked builder returns, as far as its methods go. Two shapes:
 *
 *     function () { ...; return { m: function () {...}, n() {...}, f }; }         // an object literal
 *     function () { var S = [arguments]; S[i] = {}; S[i].m = function () {...}; return S[i]; }
 *
 * Exactly one return. In the second shape the holder `S[i]` is a slot of a local array kept to itself, and each method
 * is assigned exactly once. Methods of any other shape are left out (the careful default).
 */
export const builderOf = (fn: FunctionNode, scopes: ScopeInfo): Builder | string => {
    if (fn.async || fn.generator) return "the builder is async or a generator";
    const statements = bodyOf(fn);
    const returns = returnsOf(fn);
    const [returned] = returns;
    if (returns.length !== 1 || returned?.type !== "ReturnStatement" || returned.argument === null) return "the builder doesn't end in one return of what it built";
    const parents = parentsWithin(fn);
    const methods = new Map<string, FunctionNode>();
    const closures = new Map<string, Closure>();
    const result = returned.argument;

    if (result.type === "ObjectExpression") {
        // The top-level statement that returns: locals a method is named by must hold their function before it runs.
        let returning: Node = returned;
        for (let parent = parents.get(returning); parent !== undefined && !statements.includes(returning as Statement); parent = parents.get(parent)) returning = parent;
        literalMethods(result, statements, returning, scopes, methods, closures);
        return { methods, closures, parents, statements };
    }

    const holder = slotOf(result, scopes);
    if (holder === undefined || !slotsOnly(holder.variable, parents)) return "the builder doesn't return an object literal or a slot of a local array it keeps to itself";
    const assigned = new Map<string, { fn: FunctionNode | undefined; count: number }>();
    const literals: Node[] = [];
    let holderWrites = 0;
    traverse(fn, {
        AssignmentExpression(path) {
            const target = path.node.left;
            const statement = path.parent;
            const topLevel = path.node.operator === "=" && statement?.type === "ExpressionStatement" && statements.includes(statement);
            if (sameSlot(holder, slotOf(target, scopes))) {
                holderWrites++;
                if (topLevel && path.node.right.type === "ObjectExpression") literals.push(statement);
                return;
            }
            if (target.type !== "MemberExpression" || !sameSlot(holder, slotOf(target.object, scopes))) return;
            const name = propertyKey(target);
            if (name === undefined) return;
            const entry = assigned.get(name) ?? { fn: undefined, count: 0 };
            entry.count++;
            if (topLevel && path.node.right.type === "FunctionExpression") entry.fn = path.node.right;
            assigned.set(name, entry);
        },
    });
    const [literal] = literals;
    if (holderWrites === 1 && literal?.type === "ExpressionStatement" && literal.expression.type === "AssignmentExpression" && literal.expression.right.type === "ObjectExpression") {
        literalMethods(literal.expression.right, statements, literal, scopes, methods, closures);
    }
    for (const [name, { fn: method, count }] of assigned) {
        // Also in the literal: written twice.
        const twice = methods.delete(name) || closures.delete(name);
        if (method !== undefined && count === 1 && !twice) methods.set(name, method);
    }
    return { methods, closures, parents, statements };
};

const closureOf = (value: Node): Closure | undefined => {
    if (value.type !== "CallExpression" || value.arguments.length > 0 || value.callee.type !== "FunctionExpression" || value.callee.async || value.callee.generator) return undefined;
    const iife = value.callee;
    const last = bodyOf(iife).at(-1);
    if (last?.type !== "ReturnStatement" || last.argument?.type !== "FunctionExpression" || returnsOf(iife).length !== 1) return undefined;
    return { iife, fn: last.argument };
};

/** Functions written in the literal, builder locals holding one, and functions a function invoked in it returns. */
const literalMethods = (
    literal: Node & { type: "ObjectExpression" },
    statements: readonly Statement[],
    creating: Node,
    scopes: ScopeInfo,
    methods: Map<string, FunctionNode>,
    closures: Map<string, Closure>
): void => {
    for (const property of literal.properties) {
        if (property.type !== "Property" || property.kind !== "init" || property.computed) continue;
        const name = keyName(property.key);
        if (name === undefined) continue;
        const method = property.value.type === "FunctionExpression" ? property.value : localFunction(property.value, statements, creating, scopes);
        const closure = method === undefined ? closureOf(property.value) : undefined;
        if (method !== undefined) methods.set(name, method);
        else if (closure !== undefined) closures.set(name, closure);
    }
};

/** The one prelude statement `G.k = (function () {...})()` building `prefix`; unless `unfinished`, run to completion. */
export const definitionOf = (runtime: RuntimeModel, isStorage: (node: Node) => boolean, prefix: PropertyPath, unfinished = false): { iife: FunctionNode; statement: Statement } | string => {
    const found: { iife: FunctionNode; statement: Statement }[] = [];
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const target = memberPath(statement.expression.left);
        if (target === undefined || !isStorage(target.root) || target.keys.length !== prefix.length || !target.keys.every((k, i) => k === prefix[i])) continue;
        const value = statement.expression.right;
        if (value.type !== "CallExpression" || value.callee.type !== "FunctionExpression" || value.arguments.length > 0) return "it isn't built by an immediately invoked function";
        found.push({ iife: value.callee, statement });
    }
    const [only] = found;
    if (only === undefined || found.length !== 1) return found.length === 0 ? "no prelude statement builds it" : "the prelude builds it more than once";
    if (!unfinished && !runtime.executed.has(only.statement)) return "the guest didn't run the statement that builds it";
    return only;
};
