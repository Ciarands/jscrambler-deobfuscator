import type { ArrayExpression, Expression, FunctionLike, Node, ObjectExpression } from "../../core/ast.js";
import { isIdentifierName } from "../../core/ast.js";
import { at, valueToNode } from "../../core/build.js";
import { constantEnv } from "../../core/constants.js";
import type { Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";

const isNamed = (node: Node | null | undefined, name: string): boolean => node?.type === "Identifier" && node.name === name;

/** The statements of `(acc, [k, v]) => { acc[k] = v; return acc; }` in any of the spellings a minifier leaves. */
const reducerSteps = (body: Node): Node[] => {
    if (body.type !== "BlockStatement") return body.type === "SequenceExpression" ? body.expressions : [body];
    return body.body.flatMap((statement, index, all): Node[] => {
        if (statement.type === "ExpressionStatement") return statement.expression.type === "SequenceExpression" ? statement.expression.expressions : [statement.expression];
        if (statement.type !== "ReturnStatement" || statement.argument === null || index !== all.length - 1) return [statement];
        return statement.argument.type === "SequenceExpression" ? statement.argument.expressions : [statement.argument];
    });
};

/** `list => list.reduce((acc, [k, v]) => { acc[k] = v; return acc; }, {})`: builds an object from `[key, value]` pairs. */
const isEntryBuilder = (fn: FunctionLike): boolean => {
    const [list] = fn.params;
    if (fn.type !== "ArrowFunctionExpression" || fn.async || fn.params.length !== 1 || list?.type !== "Identifier" || fn.body === null) return false;
    const [call, ...rest] = reducerSteps(fn.body);
    if (rest.length > 0 || call?.type !== "CallExpression" || call.optional || call.arguments.length !== 2) return false;
    const { callee } = call;
    if (callee.type !== "MemberExpression" || callee.computed || callee.optional || !isNamed(callee.object, list.name) || !isNamed(callee.property, "reduce")) return false;
    const [reducer, seed] = call.arguments;
    if (seed?.type !== "ObjectExpression" || seed.properties.length > 0) return false;
    if (reducer?.type !== "ArrowFunctionExpression" || reducer.async || reducer.params.length !== 2 || reducer.body === null) return false;
    const [acc, pair] = reducer.params;
    if (acc?.type !== "Identifier" || pair?.type !== "ArrayPattern" || pair.elements.length !== 2) return false;
    const [key, value] = pair.elements;
    if (key?.type !== "Identifier" || value?.type !== "Identifier" || new Set([acc.name, key.name, value.name]).size !== 3) return false;
    const [store, result, ...more] = reducerSteps(reducer.body);
    if (more.length > 0 || store?.type !== "AssignmentExpression" || store.operator !== "=" || !isNamed(result, acc.name)) return false;
    const target = store.left;
    return target.type === "MemberExpression" && target.computed && isNamed(target.object, acc.name) && isNamed(target.property, key.name) && isNamed(store.right, value.name);
};

/** `[["a", x], ["b", y]]` as the properties `a: x, b: y`: literal keys only, each pair exactly a key and a value. */
const entryProperties = (list: ArrayExpression): ObjectExpression["properties"] | undefined => {
    const properties: Node[] = [];
    for (const entry of list.elements) {
        if (entry?.type !== "ArrayExpression" || entry.elements.length !== 2) return undefined;
        const [key, value] = entry.elements;
        if (key?.type !== "Literal" || (typeof key.value !== "string" && typeof key.value !== "number")) return undefined;
        if (value === null || value === undefined || value.type === "SpreadElement" || key.value === "__proto__") return undefined;
        const name = key.value;
        const keyNode = typeof name === "string" && isIdentifierName(name) ? at<Expression>({ type: "Identifier", name }, key) : valueToNode(name, key);
        properties.push(at<Node>({ type: "Property", kind: "init", key: keyNode, value, computed: false, method: false, shorthand: false }, entry));
    }
    return properties as ObjectExpression["properties"];
};

/**
 * `build([["a", x], ["b", y]])` -> `{ a: x, b: y }`, where `build` holds an entry builder for good at the call
 * (`functionAt`). The values run in the same order; the keys are literals, so converting them earlier changes
 * nothing; a store to a fresh plain object creates the property as the literal does, in the same order, a repeated
 * key keeping its first place and last value in both (no setter on Object.prototype but `__proto__`'s, which is
 * refused; `reduce` and array destructuring are the builtins: model 7). A builder left without uses goes after the
 * walk (`unusedDeclarators`).
 *
 * Runs before the walk: `functionAt` reads the tree as the scope analysis saw it.
 */
export const objectsFromEntryLists = (program: Node, context: UnminifyContext): void => {
    const { scopes } = context;
    const builders = new Map<FunctionLike, boolean>();
    const replaced = new Map<Variable, number>();
    let env: ReturnType<typeof constantEnv> | undefined;
    traverse(program, {
        CallExpression(path) {
            const call = path.node;
            const [list] = call.arguments;
            if (call.optional || call.callee.type !== "Identifier" || call.arguments.length !== 1 || list?.type !== "ArrayExpression") return;
            const properties = entryProperties(list);
            if (properties === undefined) return;
            const fn = (env ??= constantEnv(scopes, context.log)).functionAt(call.callee);
            const variable = scopes.variableOf(call.callee);
            if (fn === undefined || variable === undefined) return;
            let builder = builders.get(fn);
            if (builder === undefined) builders.set(fn, (builder = isEntryBuilder(fn)));
            if (!builder) return;
            context.did("entryLists", call);
            context.removedReferences.add(call.callee);
            replaced.set(variable, (replaced.get(variable) ?? 0) + 1);
            path.replace(at<ObjectExpression>({ type: "ObjectExpression", properties }, call));
        },
    });
    for (const [variable, count] of replaced) {
        const [def] = variable.defs;
        const references = scopes.references(variable);
        // Its declaration and the calls replaced. The declarator holds the function itself: for `var b; b = fn;` the
        // write would stay without its declaration.
        if (variable.defs.length !== 1 || def?.type !== "Variable" || variable.scope.type === "global" || context.isExported(variable) || references?.length !== count + 1) continue;
        const init = (def.node as unknown as { init?: Node | null }).init;
        if (init === null || init === undefined || builders.get(init as FunctionLike) !== true) continue;
        context.unusedDeclarators.add(def.node as unknown as Node);
    }
};
