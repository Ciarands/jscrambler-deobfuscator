import type { Node, Statement } from "../../core/ast.js";
import { isFunctionNode, memberPath } from "../../core/ast.js";
import type { Reference, ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { Path } from "../../core/traverse.js";
import type { RuntimeModel, PropertyPath } from "./model.js";

export interface StorageMatcher {
    /** `node` is `G` itself, or another name that only ever holds `G`. */
    readonly isStorage: (node: Node) => boolean;
    /** `g` in `var g = G;`, or a parameter an IIFE receives `G` in. */
    readonly isAliasBinding: (node: Node) => boolean;
    readonly aliases: ReadonlySet<Variable>;
}

export const rootStatements = (root: Node): Statement[] => {
    if (root.type === "Program") return root.body as Statement[];
    if ((root.type === "FunctionExpression" || root.type === "FunctionDeclaration") && root.body !== null) return root.body.body as Statement[];
    if (root.type === "ArrowFunctionExpression" && root.body.type === "BlockStatement") return root.body.body as Statement[];
    return [];
};

/** The storage paths root statements assign (`G.k.l = ...`): every path `definitionOf` can find a definition of. */
export const assignedPaths = (runtime: RuntimeModel, isStorage: (node: Node) => boolean): PropertyPath[] => {
    const paths = new Map<string, PropertyPath>();
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const target = memberPath(statement.expression.left);
        if (target !== undefined && isStorage(target.root)) paths.set(JSON.stringify(target.keys), target.keys);
    }
    return [...paths.values()];
};

/** Not counting nested non-arrow functions. */
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

/** Aliases are bindings, which only change with a new scope analysis. */
const matchers = new WeakMap<ScopeInfo, StorageMatcher>();

/**
 * `G` is the storage name declared in the root scope or globally, plus locals whose only write is `var x = G` and
 * IIFE parameters receiving `G` (never reassigned, not reachable via `arguments`). Names resolve statically even
 * under direct `eval`: eval'd code is taken not to use this script's names.
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

/**
 * Where the value at `path` goes: up through the operators passing it on (`||`/`&&`/`??`, `?:` branches, a sequence's
 * last) and the object and array literals holding it (a property's value, an element), to the outermost; `literal`
 * when it went into one.
 */
export const passedOn = (path: Path): { outer: Path; literal: boolean } => {
    let outer = path;
    let literal = false;
    for (let through = outer.parentPath; through !== null; through = outer.parentPath) {
        const node = through.node;
        if (node.type === "Property" && outer.key === "value" && through.parent?.type === "ObjectExpression" && through.parentPath !== null) {
            outer = through.parentPath;
            literal = true;
        } else if (node.type === "ArrayExpression" && outer.key === "elements") {
            outer = through;
            literal = true;
        } else if (
            node.type === "LogicalExpression" ||
            (node.type === "ConditionalExpression" && outer.key !== "test") ||
            (node.type === "SequenceExpression" && node.expressions.at(-1) === outer.node)
        ) {
            outer = through;
        } else break;
    }
    return { outer, literal };
};
