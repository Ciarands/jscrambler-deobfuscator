import type { Function as FunctionDeclaration, Node, Statement, VariableDeclaration } from "./ast.js";
import { isFunctionNode } from "./ast.js";
import { at } from "./build.js";
import { forEachChild } from "./traverse.js";

/** The names a binding pattern declares: `a`, `{ a, b: [c] }`, `[d = 1, ...e]`. */
export const bindingNames = (pattern: Node, names: Set<string> = new Set()): Set<string> => {
    switch (pattern.type) {
        case "Identifier":
            names.add(pattern.name);
            break;
        case "ObjectPattern":
            for (const property of pattern.properties) bindingNames(property.type === "RestElement" ? property.argument : property.value, names);
            break;
        case "ArrayPattern":
            for (const element of pattern.elements) if (element !== null) bindingNames(element, names);
            break;
        case "AssignmentPattern":
            bindingNames(pattern.left, names);
            break;
        case "RestElement":
            bindingNames(pattern.argument, names);
            break;
        default:
            break;
    }
    return names;
};

/**
 * Visit what a subtree declares for its whole function, wherever in it they sit, in source order: `var` names, and
 * block functions (sloppy-mode Annex B gives them a function-scoped binding too). Nested functions are their own scope
 * and not searched; a function declaration is reported, not entered.
 */
const visitHoisted = (node: Node, onVar: (name: string) => void, onFunction: (declaration: FunctionDeclaration) => void): void => {
    if (node.type === "VariableDeclaration" && node.kind === "var") {
        for (const declarator of node.declarations) for (const name of bindingNames(declarator.id)) onVar(name);
    }
    if (node.type === "FunctionDeclaration") {
        onFunction(node);
        return;
    }
    if (isFunctionNode(node)) return;
    forEachChild(node, (child) => visitHoisted(child, onVar, onFunction));
};

/** Names a subtree declares for its whole function: `var`s and block functions (see `visitHoisted`). */
export const hoistedNames = (node: Node, names: Set<string> = new Set()): Set<string> => {
    visitHoisted(
        node,
        (name) => names.add(name),
        (declaration) => {
            if (declaration.id !== null) names.add(declaration.id.name);
        }
    );
    return names;
};

/**
 * `hoistedNames`, split by kind. A block function only binds its name for the whole function when Annex B applies
 * (sloppy mode, no clashing lexical declaration on the way up), which takes scope analysis to decide; `var`s always do.
 */
export const hoistedDeclarations = (node: Node, into: { readonly vars: Set<string>; readonly functions: FunctionDeclaration[] }): void =>
    visitHoisted(
        node,
        (name) => into.vars.add(name),
        (declaration) => into.functions.push(declaration)
    );

/** `var a, b;` / `let a, b;` with no initializers, or nothing when there are no names. */
export const placeholderDeclaration = (kind: "var" | "let", names: ReadonlySet<string>, origin: Node): VariableDeclaration[] =>
    names.size === 0
        ? []
        : [
              at<VariableDeclaration>(
                  {
                      type: "VariableDeclaration",
                      kind,
                      declare: false,
                      declarations: [...names].map((name) => at({ type: "VariableDeclarator", id: at({ type: "Identifier", name }, origin), init: null, definite: false }, origin)),
                  },
                  origin
              ),
          ];

/** What a removed statement list leaves behind: `var x;`/`let x;` placeholders and function declarations (kept whole). */
export const isPlaceholder = (s: Statement): boolean =>
    s.type === "FunctionDeclaration" || (s.type === "VariableDeclaration" && (s.kind === "var" || s.kind === "let") && s.declarations.every((d) => d.init === null));

/**
 * The statements that must stay when `dead` (statements of one list that can never run) is removed, so that no binding
 * changes scope:
 * - `var` names and Annex B function names from anywhere inside: `var a, b;` (their binding is the function's);
 * - `let`/`const`/`class` names declared directly in the list: `let c;` (still in their temporal dead zone, as the
 *   originals would be forever: every access keeps throwing, nothing rebinds to an outer `c`);
 * - function declarations of the list itself, whole: they're hoisted with their body and may be called.
 */
export const deadRemainder = (dead: readonly Statement[], origin: Node): Statement[] => {
    const varNames = new Set<string>();
    const lexicalNames = new Set<string>();
    const functions: Statement[] = [];
    for (const statement of dead) {
        if (statement.type === "FunctionDeclaration") functions.push(statement);
        else if (statement.type === "VariableDeclaration" && statement.kind !== "var") for (const d of statement.declarations) bindingNames(d.id, lexicalNames);
        else if (statement.type === "ClassDeclaration" && statement.id !== null) lexicalNames.add(statement.id.name);
        else hoistedNames(statement, varNames);
    }
    return [...placeholderDeclaration("var", varNames, origin), ...placeholderDeclaration("let", lexicalNames, origin), ...functions];
};
