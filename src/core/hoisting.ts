import type { Function as FunctionDeclaration, Node, Statement, VariableDeclaration } from "./ast.js";
import { isFunctionNode } from "./ast.js";
import { at } from "./build.js";
import { forEachChild } from "./traverse.js";

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
 * `var` names and block functions (Annex B binds them function-wide too), in source order. Nested functions aren't
 * searched; a function declaration is reported, not entered.
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

/** Block functions are reported separately: whether Annex B applies needs scope analysis. */
export const hoistedDeclarations = (node: Node, into: { readonly vars: Set<string>; readonly functions: FunctionDeclaration[] }): void =>
    visitHoisted(
        node,
        (name) => into.vars.add(name),
        (declaration) => into.functions.push(declaration)
    );

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

export const isPlaceholder = (s: Statement): boolean =>
    s.type === "FunctionDeclaration" || (s.type === "VariableDeclaration" && (s.kind === "var" || s.kind === "let") && s.declarations.every((d) => d.init === null));

/**
 * What must stay when unreachable `dead` statements are removed, so no binding changes scope: `var`/Annex B names as
 * `var x;`; the list's own `let`/`const`/`class` names as `let c;` (forever in TDZ, as the originals were, so nothing
 * rebinds to an outer `c`); the list's function declarations whole (hoisted, may be called).
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
