import type { ArrowFunctionExpression, Function as FunctionNode, MemberExpression, Node, Statement } from "../core/ast.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import { returnsOf } from "./emulate/builders.js";

type FunctionLike = FunctionNode | ArrowFunctionExpression;

/** `Math`'s members a pure function may use: everything but `random`. */
const PURE_MATH: ReadonlySet<string> = new Set(Object.getOwnPropertyNames(Math).filter((name) => name !== "random"));

/** Global names a pure function may read. */
const GLOBAL_VALUES: ReadonlySet<string> = new Set(["undefined", "NaN", "Infinity"]);

/**
 * The node types a pure function may contain: statements and operators over primitives. Nothing that makes objects
 * or functions (so every value it handles is a primitive when its arguments are), and nothing that runs code it
 * doesn't show (`new`, getters through computed keys, iteration protocols, `with`, `yield`/`await`).
 */
const ALLOWED: ReadonlySet<string> = new Set([
    "BlockStatement",
    "ExpressionStatement",
    "VariableDeclaration",
    "VariableDeclarator",
    "ReturnStatement",
    "IfStatement",
    "ForStatement",
    "WhileStatement",
    "DoWhileStatement",
    "BreakStatement",
    "ContinueStatement",
    "SwitchStatement",
    "SwitchCase",
    "LabeledStatement",
    "EmptyStatement",
    "Identifier",
    "Literal",
    "UnaryExpression",
    "BinaryExpression",
    "LogicalExpression",
    "ConditionalExpression",
    "AssignmentExpression",
    "UpdateExpression",
    "SequenceExpression",
    "MemberExpression",
    "CallExpression",
    "TemplateLiteral",
    "TemplateElement",
    "ParenthesizedExpression",
]);

const isWithin = (scope: Scope | null, fn: Node): boolean => {
    for (let current = scope; current !== null; current = current.upper) if ((current.block as unknown as Node) === fn) return true;
    return false;
};

/** Whether `inner` is in `outer`'s subtree. */
const contains = (outer: Node, inner: Node): boolean => {
    let found = false;
    traverse(outer, {
        enter(path) {
            if (found) return path.skip();
            if (path.node === inner) found = true;
        },
    });
    return found;
};

/** Members (never written: assignments and updates take only names): `x.length`, `x.charCodeAt(...)`, `Math.name` (checked with the name `Math`). */
const memberImpurity = (node: MemberExpression, parent: Node | null, key: string | null): string | undefined => {
    if (node.computed || node.property.type !== "Identifier") return "it reads a computed member";
    if (node.object.type === "Identifier" && node.object.name === "Math") return undefined;
    const name = node.property.name;
    const called = parent?.type === "CallExpression" && key === "callee";
    if (called ? name === "charCodeAt" : name === "length") return undefined;
    return `it ${called ? "calls" : "uses"} .${name}`;
};

/** A global the function reads: `undefined`, `NaN`, `Infinity`, or a member of `Math` but `random`. */
const globalImpurity = (name: string, parent: Node | null, key: string | null): string | undefined => {
    if (GLOBAL_VALUES.has(name)) return undefined;
    if (name !== "Math" || parent?.type !== "MemberExpression" || key !== "object" || parent.computed || parent.property.type !== "Identifier") return `it reads the global ${name}`;
    return PURE_MATH.has(parent.property.name) ? undefined : `it uses Math.${parent.property.name}`;
};

/**
 * Proves functions of a runtime builder pure: their result depends only on their arguments, they change nothing
 * outside their own locals, and they make the same choices on every run. Termination is the caller's to see (a
 * guest run with the arguments in question).
 *
 * A pure function's code uses only the node types in `ALLOWED`; with primitive arguments every value it handles is
 * then a primitive, or a function giving a string's char codes (`String.prototype.charCodeAt.bind(x)`). Its names are
 * its own locals and parameters (written freely), the builder's locals that hold one value for good (bound once, before
 * the builder returns, to a literal or to a function that is pure itself), and the globals `undefined`, `NaN`,
 * `Infinity` and `Math` (all members but `random`). Members it reads are `length` and `Math`'s; the only methods it
 * calls are `Math`'s, `charCodeAt`, and that `bind`. Relies on model 7: builtins intact (those it calls are the
 * standard ones, as in the guest).
 */
export class PurityProver {
    readonly #scopes: ScopeInfo;
    readonly #proven = new Map<Node, string | undefined>();
    /** Per builder, the index of the top-level statement holding its one return (-1: none such). */
    readonly #returning = new Map<FunctionNode, number>();

    constructor(scopes: ScopeInfo) {
        this.#scopes = scopes;
    }

    /** Why `fn`, a function of the immediately invoked `builder`, isn't pure; `undefined` when it is. */
    impurity(fn: FunctionLike, builder: FunctionNode): string | undefined {
        if (this.#proven.has(fn)) return this.#proven.get(fn);
        this.#proven.set(fn, undefined); // a helper calling back into a function being proven: the outer proof decides
        const reason = this.#check(fn, builder);
        this.#proven.set(fn, reason);
        return reason;
    }

    #check(fn: FunctionLike, builder: FunctionNode): string | undefined {
        if (fn.async || fn.generator) return "it is async or a generator";
        if (!fn.params.every((param) => param.type === "Identifier")) return "its parameters aren't plain names";
        if (fn.body === null) return "it has no body";
        let reason: string | undefined;
        /** Nodes of `String.prototype.charCodeAt.bind(x)` callees, checked as a whole. */
        const accepted = new Set<Node>();
        traverse(fn.body, {
            enter: (path) => {
                if (reason !== undefined) return path.skip();
                const node = path.node;
                if (accepted.has(node)) return;
                if (node.type === "CallExpression") for (const part of this.#boundCharCodeAt(node.callee)) accepted.add(part);
                if (!ALLOWED.has(node.type)) reason = `it uses ${node.type}`;
                else if (node.type === "Literal" && typeof node.value === "object" && node.value !== null) reason = "it makes an object (a regular expression)";
                else if (node.type === "Literal" && typeof node.value === "bigint") reason = "it uses a bigint";
                else if (node.type === "UnaryExpression" && node.operator === "delete") reason = "it deletes";
                else if (node.type === "BinaryExpression" && (node.operator === "in" || node.operator === "instanceof")) reason = `it uses ${node.operator}`;
                else if (node.type === "AssignmentExpression" && node.left.type !== "Identifier") reason = "it assigns to something other than a name";
                else if (node.type === "UpdateExpression" && node.argument.type !== "Identifier") reason = "it updates something other than a name";
                else if (node.type === "VariableDeclarator" && node.id.type !== "Identifier") reason = "it destructures";
                else if (node.type === "MemberExpression") reason = memberImpurity(node, path.parent, path.key);
                else if (node.type === "Identifier") reason = this.#name(node, node.name, path.parent, path.key, fn, builder);
            },
        });
        return reason;
    }

    /**
     * The nodes of `String.prototype.charCodeAt.bind` (with `String` the global), a callee giving a function that
     * returns its receiver's char codes: pure like `charCodeAt` itself (model 7). Empty for any other callee.
     */
    #boundCharCodeAt(callee: Node): Node[] {
        if (callee.type !== "MemberExpression" || callee.computed || callee.property.type !== "Identifier" || callee.property.name !== "bind") return [];
        const method = callee.object;
        if (method.type !== "MemberExpression" || method.computed || method.property.type !== "Identifier" || method.property.name !== "charCodeAt") return [];
        const prototype = method.object;
        if (prototype.type !== "MemberExpression" || prototype.computed || prototype.property.type !== "Identifier" || prototype.property.name !== "prototype") return [];
        const owner = prototype.object;
        const global = owner.type === "Identifier" && owner.name === "String" && this.#scopes.referenceOf(owner) !== undefined && this.#scopes.staticVariableOf(owner) === undefined;
        return global ? [callee, method, prototype, owner] : [];
    }

    /**
     * Names: own locals, builder locals bound for good, and a few globals. Property names and labels aren't references.
     * A write to an outer name is refused with it: such a name is bound more than once (a global by name: the writable
     * ones aren't among those allowed, the allowed values are read-only).
     */
    #name(node: Node, name: string, parent: Node | null, key: string | null, fn: FunctionLike, builder: FunctionNode): string | undefined {
        if (parent?.type === "MemberExpression" && key === "property") return undefined;
        if (parent?.type === "LabeledStatement" || parent?.type === "BreakStatement" || parent?.type === "ContinueStatement") return undefined;
        if (name === "arguments") return "it uses arguments";
        const reference = this.#scopes.referenceOf(node);
        if (reference === undefined) return this.#scopes.variableOf(node) === undefined ? `it names ${name}, which the analysis doesn't know` : undefined;
        const variable = this.#scopes.staticVariableOf(node);
        if (variable !== undefined && isWithin(variable.scope, fn)) return undefined;
        return variable === undefined ? globalImpurity(name, parent, key) : this.#bound(variable, builder);
    }

    /** A builder local that holds one value for good: a literal, or a pure function. */
    #bound(variable: Variable, builder: FunctionNode): string | undefined {
        const outside = `it reads ${variable.name}, which may change`;
        const [def] = variable.defs;
        if ((variable.scope.block as unknown as Node) !== builder || def === undefined || variable.defs.length !== 1) return outside;
        const statements: readonly Statement[] = builder.body?.body ?? [];
        const writes = this.#scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length;
        const node = def.node as unknown as Node;
        if (node.type === "FunctionDeclaration") return writes === 0 && statements.includes(node) ? this.impurity(node, builder) : outside;
        if (node.type !== "VariableDeclarator" || writes !== 1 || node.init === null) return outside;
        // Bound before the builder returns (the builder ran to its return in the prelude).
        const index = statements.indexOf(def.parent as unknown as Statement);
        const returning = this.#returningIndex(builder, statements);
        if (index === -1 || returning === -1 || index > returning) return outside;
        const init = node.init;
        if (init.type === "Literal") return typeof init.value === "object" && init.value !== null ? outside : undefined;
        if (init.type === "FunctionExpression" || init.type === "ArrowFunctionExpression") return this.impurity(init, builder);
        return outside;
    }

    #returningIndex(builder: FunctionNode, statements: readonly Statement[]): number {
        const known = this.#returning.get(builder);
        if (known !== undefined) return known;
        const returns = returnsOf(builder);
        const [returned] = returns;
        const index = returned === undefined || returns.length !== 1 ? -1 : statements.findIndex((statement) => contains(statement, returned));
        this.#returning.set(builder, index);
        return index;
    }
}
