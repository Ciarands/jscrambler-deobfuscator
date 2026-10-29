import type { ArrowFunctionExpression, Function as FunctionNode, Node, Statement, VariableDeclaration, VariableDeclarator } from "../core/ast.js";
import { identifier } from "../core/build.js";
import type { PassLog } from "../core/log.js";
import type { Reference, ScopeInfo, Variable } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { RuntimeModel } from "./emulate/model.js";
import type { StorageMatcher } from "./emulate/storage.js";
import { rootStatements } from "./emulate/storage.js";

type FunctionLike = FunctionNode | ArrowFunctionExpression;

const asFunction = (node: Node): FunctionLike | undefined => (node.type === "FunctionExpression" || node.type === "FunctionDeclaration" || node.type === "ArrowFunctionExpression" ? node : undefined);

/** The statements of a function's block body (none for an expression-bodied arrow). */
const statementsOf = (fn: FunctionLike): Statement[] => (fn.body?.type === "BlockStatement" ? fn.body.body : []);

/**
 * Another name for `G` and what makes it hold `G` wherever it is read:
 * - `declared`: `var A = G;` as top-level statement `index` of `fn`'s body. Code in that body's later statements runs
 *   after it, and so do the functions those statements create (and the functions those create, whatever their kind).
 *   A function declaration directly in `fn` is `fn`'s local, created once `fn`'s parameters are bound (their
 *   initialisers can't reach it), so only the code of `fn`'s body can call it first: its reads come after the alias is
 *   set when that code runs nothing before (`quietStart`: only directives and function declarations before the
 *   statement, no initialiser before the alias's declarator).
 * - `parameter`: a parameter of the immediately invoked `fn`, bound before any of its code runs; `valid` once the call
 *   is seen to pass `G` itself.
 */
type Alias =
    | {
          readonly kind: "declared";
          readonly fn: FunctionLike;
          readonly index: number;
          readonly quietStart: boolean;
          readonly declaration: VariableDeclaration;
          readonly declarator: VariableDeclarator;
      }
    | { readonly kind: "parameter"; readonly fn: Node; valid: boolean };

/** A function whose code is running, and which top-level statement of its body the walk is in (-1: none yet). */
interface Frame {
    readonly fn: FunctionLike;
    top: number;
}

/**
 * The storage binding, when it holds `G` at every moment code runs: a function declaration among the root's
 * statements (initialised before any of the root's code runs) that nothing reassigns.
 */
const storageBinding = (runtime: RuntimeModel, scopes: ScopeInfo): Variable | string => {
    const declarations = rootStatements(runtime.root).filter((statement) => statement.type === "FunctionDeclaration" && statement.id?.name === runtime.storage);
    const [only] = declarations;
    if (only?.type !== "FunctionDeclaration" || only.id === null || declarations.length !== 1) return `${runtime.storage} isn't one function declaration of the runtime's root`;
    const variable = scopes.variableOf(only.id);
    if (variable === undefined || variable.defs.length !== 1) return `${runtime.storage} is declared more than once`;
    if (scopes.staticReferences(variable).some((reference) => reference.isWrite())) return `${runtime.storage} is reassigned`;
    return variable;
};

/** What makes `variable`, another name for `G`, hold `G` where it is read; a reason when that can't be shown. */
const aliasOf = (variable: Variable, storage: Variable, scopes: ScopeInfo): Alias | string => {
    const [def] = variable.defs;
    if (def === undefined) return "it has no declaration";
    const block = variable.scope.block as unknown as Node;
    if (def.type === "Parameter") return { kind: "parameter", fn: block, valid: false };
    const declarator = def.node as unknown as Node;
    const declaration = def.parent as unknown as Node | null;
    if (declarator.type !== "VariableDeclarator" || declaration?.type !== "VariableDeclaration") return "it isn't declared by a variable declaration";
    const fn = asFunction(block);
    if (fn === undefined || variable.scope.type !== "function") return "it isn't a function's local";
    if (declarator.init?.type !== "Identifier" || scopes.staticVariableOf(declarator.init) !== storage) return "it is initialised from another alias";
    const statements = statementsOf(fn);
    const index = statements.indexOf(declaration);
    if (index === -1) return "it isn't declared by a top-level statement of its function";
    const before = declaration.declarations.slice(0, declaration.declarations.indexOf(declarator));
    const quietStart =
        statements.slice(0, index).every((statement) => statement.type === "FunctionDeclaration" || (statement.type === "ExpressionStatement" && typeof statement.directive === "string")) &&
        before.every((other) => other.init === null);
    return { kind: "declared", fn, index, quietStart, declaration, declarator };
};

/** Whether `name`, written where `reference` is, names `binding`: the first scope out that declares it, no `with` on the way. */
const namesBindingAt = (reference: Reference, name: string, binding: Variable): boolean => {
    for (let scope = reference.from as Reference["from"] | null; scope !== null; scope = scope.upper) {
        if (scope.type === "with") return false;
        const variable = scope.set.get(name);
        if (variable !== undefined) return variable === binding;
    }
    return false;
};

/** Why the read in `frames`' innermost function may run before `alias` holds `G`, if it may (see `Alias`). */
const tooEarly = (alias: Alias, frames: readonly Frame[]): string | undefined => {
    if (alias.kind === "parameter") return alias.valid ? undefined : "the call doesn't pass the storage binding itself";
    const at = frames.findLastIndex((frame) => frame.fn === alias.fn);
    const frame = frames[at];
    if (frames[at + 1]?.fn.type === "FunctionDeclaration") return alias.quietStart ? undefined : "it is read in a function declaration, which code before the alias may call";
    return frame !== undefined && frame.top > alias.index ? undefined : "it is read before its declaration runs";
};

/**
 * Replace reads of locals and parameters that only hold the storage object `G` (`var A = G;`, `(function (A) {...})(G)`)
 * with `G`'s own name, so the output names the runtime one way; a declaration left without reads goes.
 *
 * Exact where `A` holds `G` whenever it is read and `G`'s name means `G`'s binding there:
 * - `G` is a function declaration of the runtime's root, never reassigned: it holds the storage object from before
 *   any code runs (see `storageBinding`);
 * - `A` is written only by its initialiser, `G` itself, in a top-level statement of its function's body, and each read
 *   runs after that statement (see `Alias`); a parameter is never written, and its function doesn't use `arguments`
 *   (the matcher's conditions), and the call passes `G` itself at its position;
 * - no declaration of `G`'s name and no `with` sit between the read and `G`'s binding. Names resolve statically: code
 *   a direct `eval` runs doesn't use this script's names (model 2), so the declaration also goes in such functions.
 * Aliases initialised from another alias are left for the next round, which sees them initialised from `G`.
 *
 * Runs once the storage analyses are done with the program: the new references are unknown to `scopes`, so the
 * caller reports changed bindings.
 */
export const inlineStorageAliases = (runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, log: PassLog): number => {
    if (matcher.aliases.size === 0) return 0;
    const storage = storageBinding(runtime, scopes);
    if (typeof storage === "string") {
        log.debug(`aliases of ${runtime.storage} kept: ${storage}`);
        return 0;
    }

    const aliases = new Map<Variable, Alias>();
    const parameters = new Map<Node, Map<Variable, Alias & { kind: "parameter" }>>();
    const reads = new Map<Node, { variable: Variable; reference: Reference }>();
    for (const variable of matcher.aliases) {
        const references = scopes.staticReferences(variable).filter((reference) => !reference.isWrite());
        if (references.length === 0) continue;
        const alias = aliasOf(variable, storage, scopes);
        if (typeof alias === "string") {
            log.debug(`alias ${variable.name} of ${runtime.storage} kept: ${alias}`, variable.identifiers[0] as unknown as Node);
            continue;
        }
        aliases.set(variable, alias);
        if (alias.kind === "parameter") parameters.set(alias.fn, (parameters.get(alias.fn) ?? new Map()).set(variable, alias));
        for (const reference of references) reads.set(reference.identifier as unknown as Node, { variable, reference });
    }
    if (reads.size === 0) return 0;

    const replaced = new Map<Variable, number>();
    const kept = new Map<string, number>();
    const frames: Frame[] = [];
    traverse(runtime.root, {
        enter(path) {
            const frame = frames.at(-1);
            if (frame !== undefined && path.parent !== null && path.parent === frame.fn.body && path.index !== null) frame.top = path.index;
            const fn = asFunction(path.node);
            if (fn !== undefined) frames.push({ fn, top: -1 });
        },
        exit(path) {
            if (asFunction(path.node) !== undefined) frames.pop();
        },
        CallExpression(path) {
            const { callee, arguments: args } = path.node;
            const own = parameters.get(callee);
            if (own === undefined || (callee.type !== "FunctionExpression" && callee.type !== "ArrowFunctionExpression")) return;
            // The matcher lists a parameter only where the arguments line up with the parameters (no spread before).
            for (const [i, param] of callee.params.entries()) {
                const variable = param.type === "Identifier" ? scopes.variableOf(param) : undefined;
                const alias = variable === undefined ? undefined : own.get(variable);
                const argument = args[i];
                if (alias !== undefined) alias.valid = argument?.type === "Identifier" && scopes.staticVariableOf(argument) === storage;
            }
        },
        Identifier(path) {
            const read = reads.get(path.node);
            const alias = read === undefined ? undefined : aliases.get(read.variable);
            if (read === undefined || alias === undefined) return;
            const parent = path.parent;
            const reason =
                tooEarly(alias, frames) ??
                (namesBindingAt(read.reference, runtime.storage, storage) ? undefined : `${runtime.storage} names another binding here`) ??
                (parent?.type === "Property" && parent.shorthand ? "it is a shorthand property" : undefined);
            if (reason !== undefined) {
                kept.set(reason, (kept.get(reason) ?? 0) + 1);
                log.debug(`kept ${read.variable.name}: ${reason}`, path.node);
                return;
            }
            path.replace(identifier(runtime.storage, path.node));
            replaced.set(read.variable, (replaced.get(read.variable) ?? 0) + 1);
        },
    });

    // A declaration whose every read is now `G` goes with its declarator (its initialiser only reads `G`'s binding).
    let removed = 0;
    for (const [variable, count] of replaced) {
        const alias = aliases.get(variable);
        log.debug(`replaced ${count} read(s) of ${variable.name} with ${runtime.storage}`, variable.identifiers[0] as unknown as Node);
        if (alias?.kind !== "declared" || count !== scopes.staticReferences(variable).filter((reference) => !reference.isWrite()).length) continue;
        const { declaration, declarator, fn } = alias;
        if (declaration.declarations.length > 1) declaration.declarations.splice(declaration.declarations.indexOf(declarator), 1);
        else {
            const body = statementsOf(fn);
            body.splice(body.indexOf(declaration), 1);
        }
        removed++;
    }
    const uses = [...replaced.values()].reduce((sum, count) => sum + count, 0);
    const refusals = [...kept].map(([reason, count]) => `${count} (${reason})`).join(", ");
    log.info(`replaced ${uses} read(s) of ${replaced.size} alias(es) of ${runtime.storage} with ${runtime.storage}, removed ${removed} declaration(s); kept ${refusals || "none"}`);
    return uses + removed;
};
