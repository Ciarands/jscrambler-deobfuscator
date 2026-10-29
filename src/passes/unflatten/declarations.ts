import type { ForStatement, Function as FunctionDeclaration, Node, Statement, SwitchCase } from "../../core/ast.js";
import { bindingNames, hoistedDeclarations } from "../../core/hoisting.js";
import type { PassLog } from "../../core/log.js";
import type { Scope, ScopeInfo, Variable } from "../../core/scope.js";
import { forEachChild } from "../../core/traverse.js";
import type { Block, Machine, Refusal } from "./match.js";
import { refuse } from "./match.js";
import type { NodeId } from "./structure.js";

/**
 * What unflattening does to declarations, and how to keep every binding exactly as it was.
 *
 * The case bodies of a machine share one block scope (the switch's), entered afresh on every dispatch. Unflattening
 * spreads them over plain blocks and drops the cases that can never run, so:
 *
 * - `var`s in dropped code still bind for the whole function: they're kept as one `var a, b;` placeholder;
 * - block functions in dropped code bind a function-wide name too, when Annex B applies (`annexBName`);
 * - `let`/`const`/`class` directly in a reachable case would leave the switch's scope: refused. In a dead case they're
 *   in their temporal dead zone forever, so dropping them is exact only when nothing reachable refers to them;
 * - function declarations directly in a case are hoisted to the top of the switch, visible from every case: they move
 *   to a block wrapped around the rebuilt code (`hoistable` says when that is exact).
 */

/** A declaration scoped to the statement list it sits in, other than a function (those are handled separately). */
const isLexicalDeclaration = (s: Statement): boolean => (s.type === "VariableDeclaration" && s.kind !== "var") || s.type === "ClassDeclaration";

/**
 * A `let` in the loop's init clause gets a fresh copy per iteration. Rebuilt as one `let` in a block, the copies
 * become one binding: only a closure can tell, and only if the binding changes after its initializer.
 */
export const perIterationCapture = (scopes: ScopeInfo, loop: ForStatement): Refusal | undefined => {
    const init = loop.init;
    if (init?.type !== "VariableDeclaration" || init.kind === "var") return undefined;
    const scope = scopes.scopeOf(loop);
    if (scope === null || scope.dynamic) return refuse("lexical-loop-init", "direct eval in the loop could tell its per-iteration bindings apart", init);
    for (const variable of scope.variables) {
        // Never reassigned: every iteration's copy holds the same value.
        if (!variable.references.some((reference) => reference.isWrite() && !reference.init)) continue;
        const captured = variable.references.find((reference) => reference.from.variableScope !== scope.variableScope);
        if (captured !== undefined) return refuse("lexical-loop-init", `a closure captures \`${variable.name}\`, which has one binding per iteration`, captured.identifier as unknown as Node);
    }
    return undefined;
};

/** Whether a definition clashes with a `var` of the same name in `scope` (so Annex B leaves the block function alone). */
const blocksAnnexB = (variable: Variable, functionLevel: boolean): boolean =>
    variable.defs.some(
        (def) =>
            def.type === "ClassName" || def.type === "ImportBinding" || def.type === "Parameter" || (def.type === "Variable" && def.kind !== "var") || (def.type === "FunctionName" && !functionLevel)
    );

/**
 * The function-wide name a block function declares besides its block binding (Annex B.3.3): only in sloppy mode, and
 * only when a `var` of that name would not clash with a lexical declaration (or parameter) on the way up.
 */
export const annexBName = (scopes: ScopeInfo, declaration: FunctionDeclaration): string | undefined => {
    if (declaration.id === null) return undefined;
    const name = declaration.id.name;
    const variable = scopes.variableOf(declaration.id);
    if (variable === undefined || variable.scope.isStrict) return undefined;
    const target = variable.scope.variableScope;
    for (let scope: Scope | null = variable.scope; scope !== target && scope !== null;) {
        scope = scope.upper;
        const other = scope?.set.get(name);
        if (other !== undefined && blocksAnnexB(other, scope === target)) return undefined;
    }
    return name;
};

/**
 * Why moving case-level function `declaration` (binding `variable` in the switch scope) to one block around the
 * rebuilt machine would change behaviour, or undefined when it wouldn't. The switch creates a new function object on
 * every dispatch; the hoisted one is created once. That is only invisible when the function is only ever called:
 * not used as a value, not a generator (its objects' prototype is per function), not reading `arguments` (`callee`).
 * In sloppy mode the declaration also assigns a function-wide variable (Annex B) when evaluated; moving it changes
 * when, so nothing else in the function may refer to that name.
 */
const hoistable = (
    scopes: ScopeInfo,
    switchScope: Scope,
    variable: Variable,
    declaration: FunctionDeclaration,
    isLive: (identifier: Node) => boolean,
    callees: ReadonlySet<Node>
): { reason: string; node: Node } | undefined => {
    const name = variable.name;
    if (declaration.generator) return { reason: `case-level generator \`${name}\` is re-created on every dispatch`, node: declaration };
    const asValue = variable.references.find((reference) => {
        const identifier = reference.identifier as unknown as Node;
        return isLive(identifier) && !callees.has(identifier);
    });
    if (asValue !== undefined) return { reason: `case-level function \`${name}\` is used as a value, and is re-created on every dispatch`, node: asValue.identifier as unknown as Node };
    const own = scopes.scopeOf(declaration);
    const argumentsVariable = own?.set.get("arguments");
    if (argumentsVariable !== undefined && argumentsVariable.references.length > 0)
        return { reason: `case-level function \`${name}\` reads \`arguments\`, whose callee is re-created on every dispatch`, node: argumentsVariable.references[0]?.identifier as unknown as Node };
    if (switchScope.isStrict) return undefined;
    const functionScope = switchScope.variableScope;
    if (functionScope.type === "global") return { reason: `sloppy top-level case function \`${name}\` also sets a global, which hoisting would set earlier`, node: declaration };
    const outer = functionScope.set.get(name);
    const outerUse = outer !== undefined && !outer.defs.every((def) => def.type === "Parameter") ? outer.references[0] : undefined;
    const through = functionScope.through.find((reference) => reference.identifier.name === name);
    const conflict = outerUse ?? through;
    if (conflict !== undefined)
        return { reason: `\`${name}\` is also a function-wide name here, which the hoisted declaration would set earlier (Annex B)`, node: conflict.identifier as unknown as Node };
    return undefined;
};

export interface CaseDeclarations {
    /** Case-level function declarations to put in a block around the rebuilt code, in source order. */
    readonly hoisted: FunctionDeclaration[];
    /** Names dropped code still binds for the whole function (`var`s, Annex B names). */
    readonly vars: Set<string>;
}

/**
 * The declarations of `machine`'s cases once unflattened (see the top of this file). `reachable` are the states the
 * entry reaches; `callees` the identifiers in the machine called directly (`g(...)`).
 */
export const caseDeclarations = (
    scopes: ScopeInfo,
    machine: Machine,
    reachable: ReadonlySet<NodeId>,
    callees: ReadonlySet<Node>,
    log: PassLog
): { readonly ok: true; readonly declarations: CaseDeclarations } | Refusal => {
    const blockOf = new Map<SwitchCase, Block>();
    for (const block of machine.blocks.values()) if (block.origin !== null && reachable.has(block.key)) blockOf.set(block.origin, block);

    const vars = new Set<string>();
    const blockFunctions: FunctionDeclaration[] = [];
    const functions: { declaration: FunctionDeclaration; live: boolean }[] = [];
    const deadLexical: Statement[] = [];
    // Code that never runs: whole unreachable cases, and what follows a `return` in a reachable one.
    const dead: Statement[] = [];
    const deadCases: SwitchCase[] = [];
    for (const switchCase of machine.dispatch.cases) {
        const block = blockOf.get(switchCase);
        if (block === undefined) deadCases.push(switchCase);
        for (const s of switchCase.consequent) if (s.type === "FunctionDeclaration") functions.push({ declaration: s, live: block !== undefined });
        const lexical = block?.statements.find(isLexicalDeclaration);
        if (lexical !== undefined) return refuse("block-scoped-declaration", "case body has a block-scoped declaration", lexical);
        for (const s of block === undefined ? switchCase.consequent : block.dead) {
            if (s.type === "FunctionDeclaration") continue;
            dead.push(s);
            if (isLexicalDeclaration(s)) deadLexical.push(s);
            else hoistedDeclarations(s, { vars, functions: blockFunctions });
        }
    }

    const hoisted: FunctionDeclaration[] = [];
    const dropped: Node[] = [];
    if (deadLexical.length > 0 || functions.length > 0) {
        const switchScope = scopes.scopeOf(machine.dispatch);
        const first = functions[0]?.declaration ?? deadLexical[0] ?? machine.dispatch;
        if (switchScope === null || switchScope.dynamic) return refuse("block-scoped-declaration", "direct eval in the machine could see the declarations of its cases", first);

        // Identifiers in code that never runs. Case-level functions aren't: reachable code may call them.
        const deadIdentifiers = new Set<Node>();
        const collect = (node: Node): void => {
            if (node.type === "Identifier") deadIdentifiers.add(node);
            forEachChild(node, collect);
        };
        for (const s of dead) collect(s);
        const isLive = (identifier: Node): boolean => !deadIdentifiers.has(identifier);
        const liveUse = (variable: Variable | undefined): Node | undefined =>
            variable?.references.find((reference) => isLive(reference.identifier as unknown as Node))?.identifier as unknown as Node | undefined;

        for (const s of deadLexical) {
            const names = new Set<string>();
            if (s.type === "VariableDeclaration") for (const declarator of s.declarations) bindingNames(declarator.id, names);
            else if (s.type === "ClassDeclaration" && s.id !== null) names.add(s.id.name);
            for (const name of names) {
                const use = liveUse(switchScope.set.get(name));
                if (use !== undefined) return refuse("block-scoped-declaration", `unreachable case code declares \`${name}\`, which reachable code refers to`, use);
            }
            dropped.push(s);
        }
        for (const { declaration, live: inLiveCase } of functions) {
            const variable = declaration.id === null ? undefined : switchScope.set.get(declaration.id.name);
            if (variable === undefined) return refuse("block-scoped-declaration", "case-level function without a binding in the switch scope", declaration);
            if (!inLiveCase && liveUse(variable) === undefined) {
                blockFunctions.push(declaration);
                dropped.push(declaration);
                continue;
            }
            const why = hoistable(scopes, switchScope, variable, declaration, isLive, callees);
            if (why !== undefined) return refuse("block-scoped-declaration", why.reason, why.node);
            hoisted.push(declaration);
        }
    }

    for (const declaration of blockFunctions) {
        const name = annexBName(scopes, declaration);
        if (name !== undefined) vars.add(name);
    }
    for (const switchCase of deadCases) log.debug("dropped unreachable case", switchCase);
    for (const node of dropped) log.debug("dropped unreachable declaration", node);
    for (const declaration of hoisted) log.debug("hoisted case-level function declaration out of the switch", declaration);
    return { ok: true, declarations: { hoisted, vars } };
};
