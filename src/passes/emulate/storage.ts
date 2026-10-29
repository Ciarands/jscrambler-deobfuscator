import type { Node, Statement } from "../../core/ast.js";
import { isFunctionNode } from "../../core/ast.js";
import type { Reference, ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { RuntimeModel } from "./model.js";

/** Recognises the runtime's storage object (`G`) in expressions. */
export interface StorageMatcher {
    /** `node` is `G` itself, or another name that only ever holds `G`. */
    readonly isStorage: (node: Node) => boolean;
    /** `node` declares another name for `G`: `g` in `var g = G;`, a parameter an IIFE receives `G` in. */
    readonly isAliasBinding: (node: Node) => boolean;
    /** Locals and parameters that only ever hold `G`. */
    readonly aliases: ReadonlySet<Variable>;
}

/** The statements of the runtime's root: the program's, or the top-level IIFE's. */
export const rootStatements = (root: Node): Statement[] => {
    if (root.type === "Program") return root.body as Statement[];
    if ((root.type === "FunctionExpression" || root.type === "FunctionDeclaration") && root.body !== null) return root.body.body as Statement[];
    if (root.type === "ArrowFunctionExpression" && root.body.type === "BlockStatement") return root.body.body as Statement[];
    return [];
};

/**
 * Whether the value at `path` (a use of `G`) only gets tested: a condition, possibly through `&&`/`||`/`??`, an
 * operand of `!`, `typeof`, `void` or an equality. No code can reach `G`'s properties from there (operators only
 * read: semantic model 4).
 */
export const onlyTested = (path: Path): boolean => {
    let operand = path;
    while (operand.parent?.type === "LogicalExpression" && operand.parentPath !== null) operand = operand.parentPath;
    const parent = operand.parent;
    switch (parent?.type) {
        case "IfStatement":
        case "ConditionalExpression":
        case "WhileStatement":
        case "DoWhileStatement":
        case "ForStatement":
            return operand.key === "test";
        case "UnaryExpression":
            return parent.operator === "!" || parent.operator === "typeof" || parent.operator === "void";
        case "BinaryExpression":
            return parent.operator === "===" || parent.operator === "!==" || parent.operator === "==" || parent.operator === "!=";
        default:
            return false;
    }
};

/** Whether a function's own body (not nested non-arrow functions) mentions `arguments`. */
const usesArguments = (fn: Node): boolean => {
    let found = false;
    traverse(fn, {
        enter(path) {
            if (found || (path.node !== fn && isFunctionNode(path.node) && path.node.type !== "ArrowFunctionExpression")) path.skip();
        },
        Identifier(path) {
            if (path.node.name === "arguments" && path.key !== "property") found = true;
        },
    });
    return found;
};

/** One matcher per scope analysis: its aliases are bindings, which only change with a new scope analysis. */
const matchers = new WeakMap<ScopeInfo, StorageMatcher>();

/**
 * The storage binding is told apart from same-named locals by scope: it is declared in the root scope or, for
 * top-level script declarations, global. Other names for it count as `G` too: locals whose only write is `var x = G`,
 * and parameters an immediately invoked function receives `G` in (never reassigned, and not reachable through
 * `arguments`). Names resolve statically, also inside functions a direct `eval` makes dynamic: the code an eval runs
 * is taken not to use this script's names. Computed once per scope analysis (`matchers`).
 */
export const storageMatcher = (program: Node, runtime: RuntimeModel, scopes: ScopeInfo): StorageMatcher => {
    const known = matchers.get(scopes);
    if (known !== undefined) return known;
    const { storage, root } = runtime;
    const aliases = new Set<Variable>();
    const isStorageName = (node: Node): boolean => {
        if (node.type !== "Identifier") return false;
        const variable = scopes.staticVariableOf(node);
        if (node.name === storage) {
            if (variable === undefined) return scopes.isGlobalReference(node);
            if (variable.scope.type === "global" || (variable.scope.block as unknown as Node) === root) return true;
        }
        return variable !== undefined && aliases.has(variable);
    };
    /** The variable `id` declares, when that is its only definition, with every reference to it. */
    const singleDefinition = (id: Node): { variable: Variable; references: readonly Reference[] } | undefined => {
        const variable = scopes.staticVariableOf(id);
        return variable !== undefined && variable.defs.length === 1 ? { variable, references: scopes.staticReferences(variable) } : undefined;
    };

    traverse(program, {
        VariableDeclarator(path) {
            const { id, init } = path.node;
            if (id.type !== "Identifier" || init === null || !isStorageName(init)) return;
            const bound = singleDefinition(id);
            if (bound !== undefined && bound.references.filter((reference) => reference.isWrite()).length === 1) aliases.add(bound.variable);
        },
        CallExpression(path) {
            const fn = path.node.callee;
            if ((fn.type !== "FunctionExpression" && fn.type !== "ArrowFunctionExpression") || !path.node.arguments.some(isStorageName) || usesArguments(fn)) return;
            for (const [i, argument] of path.node.arguments.entries()) {
                // After a spread, arguments no longer line up with parameters.
                if (argument.type === "SpreadElement") break;
                const param = fn.params[i];
                if (param?.type !== "Identifier" || !isStorageName(argument)) continue;
                const bound = singleDefinition(param);
                if (bound !== undefined && bound.references.every((reference) => !reference.isWrite())) aliases.add(bound.variable);
            }
        },
    });

    const matcher: StorageMatcher = {
        aliases,
        isStorage: isStorageName,
        isAliasBinding(node) {
            const variable = scopes.staticVariableOf(node);
            return variable !== undefined && aliases.has(variable) && variable.identifiers.includes(node as never);
        },
    };
    matchers.set(scopes, matcher);
    return matcher;
};
