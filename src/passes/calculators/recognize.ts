import type { Function as FunctionNode, Node } from "../../core/ast.js";
import { isIndexKey, memberPath, propertyKey } from "../../core/ast.js";
import type { EvaluateEnv } from "../../core/evaluate.js";
import { evaluate } from "../../core/evaluate.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import type { PassContext } from "../../pipeline/pass.js";
import { bodyOf, builderOf, definitionOf } from "../runtime/builders.js";
import type { StorageEffects } from "../runtime/effects.js";
import type { RuntimeModel } from "../runtime/model.js";
import { rootStatements } from "../runtime/storage.js";
import type { Calculator, Case, Refusal } from "./sites.js";
import { refusal } from "./sites.js";

const stateWrittenBy = (fn: FunctionNode, scopes: ScopeInfo): { variable: Variable; write: Node } | undefined => {
    const [param] = fn.params;
    const [only] = bodyOf(fn);
    if (fn.async || fn.generator || fn.params.length !== 1 || param?.type !== "Identifier" || bodyOf(fn).length !== 1 || only?.type !== "ExpressionStatement") return undefined;
    const set = only.expression;
    if (set.type !== "AssignmentExpression" || set.operator !== "=" || set.left.type !== "Identifier" || set.right.type !== "Identifier") return undefined;
    const variable = scopes.variableOf(set.left);
    const given = scopes.variableOf(param);
    return variable === undefined || given === undefined || variable === given || scopes.variableOf(set.right) !== given ? undefined : { variable, write: set.left };
};

/** Why a case's expression isn't a formula over `a[i]`, literals and operators. */
const formulaProblem = (node: Node, args: Variable, scopes: ScopeInfo): string | undefined => {
    switch (node.type) {
        case "Literal":
            return undefined;
        case "MemberExpression":
            return node.computed && node.object.type === "Identifier" && scopes.variableOf(node.object) === args && node.property.type === "Literal" && isIndexKey(propertyKey(node) ?? "")
                ? undefined
                : "it reads something other than an argument";
        case "UnaryExpression":
            return node.operator === "delete" ? "it deletes" : formulaProblem(node.argument, args, scopes);
        case "BinaryExpression":
            return node.left.type === "PrivateIdentifier" ? "it tests a private name" : (formulaProblem(node.left, args, scopes) ?? formulaProblem(node.right, args, scopes));
        case "LogicalExpression":
            return formulaProblem(node.left, args, scopes) ?? formulaProblem(node.right, args, scopes);
        case "ConditionalExpression":
            return formulaProblem(node.test, args, scopes) ?? formulaProblem(node.consequent, args, scopes) ?? formulaProblem(node.alternate, args, scopes);
        default:
            return `it contains a ${node.type}`;
    }
};

/**
 * The cases of a calculation `function () { var r, a = arguments; switch (I) { case L: r = <formula>; break; ... } return r; }`
 * (one declaration or two, either order; the last case may end without `break`). Every label is a distinct constant
 * and every case sets `r` and leaves the switch, so a call returns the formula of the case whose label is `=== I`, or
 * `r`'s initial undefined when none is.
 */
const calculationOf = (fn: FunctionNode, state: Variable, scopes: ScopeInfo, env: EvaluateEnv): { cases: Case[]; args: Variable } | Refusal => {
    if (fn.async || fn.generator || fn.params.length > 0) return refusal("the calculation takes parameters, or is async or a generator", fn);
    const statements = bodyOf(fn);
    let result: Variable | undefined;
    let args: Variable | undefined;
    let i = 0;
    for (let statement = statements[0]; statement?.type === "VariableDeclaration"; statement = statements[++i]) {
        if (statement.kind !== "var") return refusal("the calculation declares a lexical local", statement);
        for (const declarator of statement.declarations) {
            const variable = declarator.id.type === "Identifier" ? scopes.variableOf(declarator.id) : undefined;
            const init = declarator.init;
            const ownArguments = init?.type === "Identifier" && init.name === "arguments" ? scopes.variableOf(init) : undefined;
            if (variable !== undefined && init === null && result === undefined) result = variable;
            else if (variable !== undefined && ownArguments !== undefined && ownArguments.defs.length === 0 && (ownArguments.scope.block as unknown as Node) === fn && args === undefined)
                args = variable;
            else return refusal("the calculation declares other locals than its result and its arguments", declarator);
        }
    }
    const [choice, exit] = statements.slice(i);
    if (result === undefined || args === undefined || result === args || statements.length !== i + 2 || choice?.type !== "SwitchStatement" || exit?.type !== "ReturnStatement") {
        return refusal("the calculation isn't `var r, a = arguments; switch (state) {...} return r;`", fn);
    }
    const discriminant = choice.discriminant;
    if (discriminant.type !== "Identifier" || scopes.variableOf(discriminant) !== state) return refusal("the calculation doesn't switch on the selector's state", discriminant);
    if (exit.argument?.type !== "Identifier" || scopes.variableOf(exit.argument) !== result) return refusal("the calculation doesn't return its result", exit);

    const cases: Case[] = [];
    for (const [index, clause] of choice.cases.entries()) {
        if (clause.test === null) return refusal("the calculation has a default case", clause);
        const label = evaluate(clause.test, env);
        if (!label.ok) return refusal("a case label isn't a constant", clause.test);
        if (cases.some((known) => known.label === label.value)) return refusal(`the case label ${String(label.value)} repeats`, clause.test);
        const [set, jump, ...rest] = clause.consequent;
        const ends = jump === undefined ? index === choice.cases.length - 1 : jump.type === "BreakStatement" && jump.label === null;
        const assignment = set?.type === "ExpressionStatement" ? set.expression : undefined;
        if (
            assignment?.type !== "AssignmentExpression" ||
            assignment.operator !== "=" ||
            assignment.left.type !== "Identifier" ||
            scopes.variableOf(assignment.left) !== result ||
            !ends ||
            rest.length > 0
        ) {
            return refusal(`case ${String(label.value)} doesn't just set the result and leave the switch`, clause);
        }
        cases.push({ label: label.value, formula: assignment.right, problem: formulaProblem(assignment.right, args, scopes) });
    }
    return { cases, args };
};

const looksLikeCalculator = (iife: FunctionNode): boolean => {
    const returned = bodyOf(iife).at(-1);
    return (
        returned?.type === "ReturnStatement" &&
        returned.argument?.type === "ObjectExpression" &&
        returned.argument.properties.some((p) => p.type === "Property" && p.value.type === "FunctionExpression" && bodyOf(p.value).some((s) => s.type === "SwitchStatement"))
    );
};

/**
 * The calculator `iife` builds: `function (I) { return { sel: function (p) { I = p; }, calc: function () {...} }; }`,
 * with `I` the builder's parameter or a local it declares. Nothing else is in the builder, the selector is that one
 * assignment, and the calculation's only identifiers besides its own locals are the switch's `I` (labels are constants,
 * formulas read only its arguments): so `I` is written only by the selector and read only by the switch, and a
 * calculation computes the case the latest selector call chose.
 */
const calculatorOf = (iife: FunctionNode, scopes: ScopeInfo, env: EvaluateEnv): Omit<Calculator, "path" | "name" | "definition"> | Refusal => {
    const builder = builderOf(iife, scopes);
    if (typeof builder === "string") return refusal(builder, iife);
    const body = bodyOf(iife);
    const returned = body.at(-1);
    if (returned?.type !== "ReturnStatement" || returned.argument?.type !== "ObjectExpression") return refusal("its builder doesn't end by returning an object literal", iife);
    if (!body.slice(0, -1).every((s) => s.type === "VariableDeclaration" && s.kind === "var" && s.declarations.every((d) => d.id.type === "Identifier" && d.init === null))) {
        return refusal("its builder does more than declare locals and return the object", iife);
    }
    if (returned.argument.properties.length !== 2 || builder.methods.size !== 2) return refusal("its object has other properties than a selector and a calculation", returned.argument);
    const methods = [...builder.methods];
    const selected = methods.map(([name, fn]) => ({ name, fn, state: stateWrittenBy(fn, scopes) }));
    const selector = selected.find((m) => m.state !== undefined);
    const calculation = selected.find((m) => m.state === undefined);
    if (selector?.state === undefined || calculation === undefined) return refusal("it has no selector `function (p) { I = p; }` next to a calculation", returned.argument);
    const { variable: state, write } = selector.state;
    if ((state.scope.block as unknown as Node) !== iife || state.defs.length !== 1) return refusal("the selector's state isn't a parameter or local of the builder", write);
    const shape = calculationOf(calculation.fn, state, scopes, env);
    if ("ok" in shape) return shape;
    return { selector: selector.name, calculation: calculation.name, cases: shape.cases, args: shape.args };
};

/** The prelude's calculator definitions `G.k = (function (I) {...})()` whose snapshot methods are the ones their builder made. */
export const recognize = (runtime: RuntimeModel, isStorage: (node: Node) => boolean, effects: StorageEffects, scopes: ScopeInfo, env: EvaluateEnv, log: PassContext["log"]): Calculator[] => {
    const found: Calculator[] = [];
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const { left, right } = statement.expression;
        if (left.type !== "MemberExpression" || right.type !== "CallExpression" || right.callee.type !== "FunctionExpression" || !looksLikeCalculator(right.callee)) continue;
        const target = memberPath(left);
        if (target === undefined || !isStorage(target.root)) continue;
        const keys = target.keys;
        const name = `${runtime.storage}.${keys.join(".")}`;
        const definition = definitionOf(runtime, isStorage, keys);
        if (typeof definition === "string" || definition.statement !== statement) {
            log.debug(`${name} is no calculator: ${typeof definition === "string" ? definition : "it isn't the prelude's only definition"}`, statement);
            continue;
        }
        const shape = calculatorOf(definition.iife, scopes, env);
        if ("ok" in shape) {
            log.debug(`${name} is no calculator: ${shape.reason}`, shape.node);
            continue;
        }
        const unsure = [shape.selector, shape.calculation].find((method) => {
            const info = effects.snapshot.typeAt([...keys, method]);
            return typeof info === "string" || info.type !== "function";
        });
        if (unsure !== undefined) {
            log.debug(`${name} looks like a calculator, but ${name}.${unsure} may not hold the method its builder made (more prelude writes, or other values)`, statement);
            continue;
        }
        log.debug(`${name} is a calculator: ${name}.${shape.selector}(n) selects one of ${shape.cases.length} case(s) ${name}.${shape.calculation}(...) computes`, statement);
        found.push({ ...shape, path: keys, name, definition: statement });
    }
    return found;
};
