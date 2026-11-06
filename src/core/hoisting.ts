import type { Function as FunctionDeclaration, Node, Statement, VariableDeclaration } from "./ast.js";
import { isFunctionNode } from "./ast.js";
import { at } from "./build.js";
import type { ScopeInfo } from "./scope.js";
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
 * `var` names and block functions (in sloppy code Annex B may bind them function-wide too), in source order. Nested
 * functions and class static blocks (whose `var`s are their own) aren't searched; a function declaration is reported,
 * not entered.
 */
const visitHoisted = (node: Node, onVar: (name: string) => void, onFunction: (declaration: FunctionDeclaration) => void): void => {
    if (node.type === "VariableDeclaration" && node.kind === "var") {
        for (const declarator of node.declarations) for (const name of bindingNames(declarator.id)) onVar(name);
    }
    if (node.type === "FunctionDeclaration") {
        onFunction(node);
        return;
    }
    if (isFunctionNode(node) || node.type === "StaticBlock") return;
    forEachChild(node, (child) => visitHoisted(child, onVar, onFunction));
};

/** Block functions are reported separately: whether Annex B applies needs scope analysis. */
export const hoistedDeclarations = (node: Node, into: { readonly vars: Set<string>; readonly functions: FunctionDeclaration[] }): void =>
    visitHoisted(
        node,
        (name) => into.vars.add(name),
        (declaration) => into.functions.push(declaration)
    );

/**
 * The function-wide names `node` binds, which must stay when it is dropped: its `var`s, and its block functions' where
 * Annex B binds them (`ScopeInfo.annexBName`: sloppy code only, a strict block function binds only in its block). Undefined
 * when `scopes` doesn't know a block function (made after the analysis), so whether it binds function-wide is unknown.
 */
export const droppedNames = (node: Node, scopes: ScopeInfo, names: Set<string> = new Set()): Set<string> | undefined => {
    const functions: FunctionDeclaration[] = [];
    hoistedDeclarations(node, { vars: names, functions });
    for (const declaration of functions) {
        if (declaration.id === null) continue;
        if (scopes.variableOf(declaration.id) === undefined) return undefined;
        const name = scopes.annexBName(declaration);
        if (name !== undefined) names.add(name);
    }
    return names;
};

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
 * rebinds to an outer `c`); the list's function declarations whole (hoisted, may be called), labelled ones without
 * their labels (a labelled function declares as a plain one does, and nothing can break to its labels). Undefined where
 * `droppedNames` doesn't know what a statement binds.
 */
export const deadRemainder = (dead: readonly Statement[], origin: Node, scopes: ScopeInfo): Statement[] | undefined => {
    const varNames = new Set<string>();
    const lexicalNames = new Set<string>();
    const functions: Statement[] = [];
    for (const statement of dead) {
        let item = statement;
        while (item.type === "LabeledStatement") item = item.body;
        if (item.type === "FunctionDeclaration") functions.push(item);
        else if (statement.type === "VariableDeclaration" && statement.kind !== "var") for (const d of statement.declarations) bindingNames(d.id, lexicalNames);
        else if (statement.type === "ClassDeclaration" && statement.id !== null) lexicalNames.add(statement.id.name);
        else if (droppedNames(statement, scopes, varNames) === undefined) return undefined;
    }
    return [...placeholderDeclaration("var", varNames, origin), ...placeholderDeclaration("let", lexicalNames, origin), ...functions];
};
