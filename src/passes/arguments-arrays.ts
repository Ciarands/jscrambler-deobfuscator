import type {
    ArrayExpression,
    ArrowFunctionExpression,
    Expression,
    ExpressionStatement,
    FunctionBody,
    Function as FunctionNode,
    MemberExpression,
    Node,
    ParamPattern,
    VariableDeclaration,
    VariableDeclarator,
} from "../core/ast.js";
import { isIndexKey, propertyKey } from "../core/ast.js";
import { at, identifier } from "../core/build.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import type { Path } from "../core/traverse.js";
import { traverse } from "../core/traverse.js";
import type { PassLog } from "../core/log.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

/** A use of slot k ≥ 1, `S[k]`, from scope `from`. */
interface SlotUse {
    readonly member: MemberExpression;
    readonly from: Scope;
}

/** The first write of a slot, in source order, when it is a statement `S[k] = value;` directly in the function body. */
interface FirstWrite {
    readonly statement: ExpressionStatement;
    readonly value: Expression;
}

interface SlotInfo {
    readonly uses: SlotUse[];
    /** `null` when the first write is anything else, `undefined` while no write was seen. */
    firstWrite: FirstWrite | null | undefined;
}

/** A use of `S[0]` from scope `from`; `element` when it is `S[0][index]`, read or written, not called on or deleted. */
interface ArgumentsUse {
    readonly member: MemberExpression;
    readonly from: Scope;
    readonly element: { readonly node: MemberExpression; readonly index: number; readonly write: boolean } | undefined;
}

/** `var S = [arguments, ...]` directly in the body of the function `fn`, and what the walk found about its uses. */
interface Candidate {
    readonly variable: Variable;
    readonly scope: Scope;
    readonly fn: FunctionNode | ArrowFunctionExpression;
    readonly body: FunctionBody;
    readonly declarator: VariableDeclarator;
    readonly literal: ArrayExpression;
    /** The function's own `arguments` object in element 0, never reassigned; `undefined` otherwise. */
    readonly argumentsObject: Variable | undefined;
    readonly slots: Map<number, SlotInfo>;
    readonly argumentsUses: ArgumentsUse[];
    /** `S[0]` itself is assigned, updated or deleted somewhere. */
    argumentsWritten: boolean;
    /** The walk has passed the declaration (tree order: execution order within the body). */
    declared: boolean;
    refusal: { readonly reason: string; readonly node: Node } | undefined;
}

/** Marks a statement to drop. */
const REMOVE: unique symbol = Symbol("remove");

/**
 * Code before the declaration must not use the array (`S[k]` would throw where the local reads undefined). That
 * code reaches it only by naming it, or by calling a function declared in the function body (created on entry):
 * so the walk refuses references to the array before the declaration, except inside such a function, and
 * references to such a function before the declaration (`recordUse`, `recordHoistedUse`).
 */
const insideHoistedFunction = (path: Path, candidate: Candidate): boolean => {
    for (let current = path.parentPath; current !== null && current.node !== candidate.fn; current = current.parentPath) {
        if (current.node.type === "FunctionDeclaration" && current.parent === candidate.body) return true;
    }
    return false;
};

/**
 * An array element whose evaluation runs no code, so nothing can observe the array before it is assigned (a hole,
 * not a spread: those would also move the later elements' indices).
 */
const evaluatesInertly = (element: Node | null, scopes: ScopeInfo): boolean =>
    element === null ||
    element.type === "Literal" ||
    element.type === "FunctionExpression" ||
    element.type === "ArrowFunctionExpression" ||
    (element.type === "Identifier" && scopes.variableOf(element) !== undefined);

/** `node` is called with its object as `this`: `S[k](...)`, `` S[k]`...` ``. */
const isCallee = (path: Path): boolean => (path.parent?.type === "CallExpression" && path.key === "callee") || (path.parent?.type === "TaggedTemplateExpression" && path.key === "tag");

/** `path` is the object of a member expression with a constant index key: that member (path and node) and its index. */
const indexedBy = (path: Path): { member: Path; node: MemberExpression; index: number } | undefined => {
    const member = path.parentPath;
    const node = member?.node;
    if (member === null || node?.type !== "MemberExpression" || path.key !== "object") return undefined;
    const key = propertyKey(node);
    return key === undefined || !isIndexKey(key) ? undefined : { member, node, index: Number(key) };
};

/** Whether a scope from `from` up to (not including) the function scope binds `name`, in the analysis or as a name this pass added. */
const shadowedBetween = (from: Scope, fnScope: Scope, name: string, added: ReadonlyMap<Scope, Set<string>>): boolean => {
    for (let scope: Scope | null = from; scope !== null && scope !== fnScope; scope = scope.upper) if (scope.set.has(name) || added.get(scope)?.has(name)) return true;
    return false;
};

/** A simple parameter list: identifiers only, no duplicates (so parameter i is the only alias of `arguments[i]`). */
const hasSimpleParameters = (params: readonly ParamPattern[]): boolean => {
    const names = new Set<string>();
    for (const param of params) {
        if (param.type !== "Identifier" || names.has(param.name)) return false;
        names.add(param.name);
    }
    return true;
};

/** Why the array's declaration doesn't allow the conversion (see `argumentsArrays`); `undefined` when it does. */
const declarationRefusal = (candidate: Candidate, declaration: VariableDeclaration, scopes: ScopeInfo): string | undefined => {
    const { variable, scope, literal } = candidate;
    if (variable.defs.length !== 1) return "the array's name is declared more than once";
    if (declaration.kind !== "var") return `the array is declared with ${declaration.kind}`;
    if (!candidate.body.body.includes(declaration)) return "the declaration isn't a statement directly in a function body";
    if (scope.dynamic) return "the function (or one nested in it) calls eval directly: its references are unresolved";
    return literal.elements.slice(1).every((e) => evaluatesInertly(e, scopes)) ? undefined : "an initializer element runs code (it could use the array before it exists)";
};

/**
 * Finds the arrays, descendants before ancestors (reverse of the scope manager's pre-order), so the names a nested
 * function's conversion adds are known when an enclosing function's slots are named. Refusals that need no walk are
 * decided here.
 */
const findCandidates = (scopes: ScopeInfo): Candidate[] => {
    const candidates: Candidate[] = [];
    for (const scope of scopes.manager.scopes.toReversed()) {
        if (scope.type !== "function") continue;
        // eslint-scope's function scopes are those of functions and arrows; one without a block body declares no var.
        const fn = scope.block as unknown as FunctionNode | ArrowFunctionExpression;
        const body = fn.body !== null && fn.body.type === "BlockStatement" ? fn.body : undefined;
        if (body === undefined) continue;
        for (const variable of scope.variables) {
            const def = variable.defs[0];
            if (def?.type !== "Variable") continue;
            const declarator = def.node as unknown as VariableDeclarator;
            const literal = declarator.init;
            const first = literal?.type === "ArrayExpression" ? literal.elements[0] : undefined;
            if (literal?.type !== "ArrayExpression" || first?.type !== "Identifier" || first.name !== "arguments") continue;
            const declaration = def.parent as unknown as VariableDeclaration;
            const argumentsVariable = scopes.variableOf(first);
            const owned = argumentsVariable?.scope === scope && argumentsVariable.defs.length === 0 && argumentsVariable.references.every((r) => !r.isWrite());
            const candidate: Candidate = {
                variable,
                scope,
                fn,
                body,
                declarator,
                literal,
                argumentsObject: owned ? argumentsVariable : undefined,
                slots: new Map(),
                argumentsUses: [],
                argumentsWritten: false,
                declared: false,
                refusal: undefined,
            };
            const reason = declarationRefusal(candidate, declaration, scopes);
            if (reason !== undefined) candidate.refusal = { reason, node: declarator };
            candidates.push(candidate);
        }
    }
    return candidates;
};

/**
 * Records one use `S[...]` of a candidate (the identifier at `path`). Refuses the array when it is used as anything
 * but `S[index]` (passed, aliased, reassigned, resized through `length`), when a slot is called as a method of the
 * array (the callee would get the array as `this`), deleted (a `var` can't be), or used inside `with`.
 */
const recordUse = (candidate: Candidate, path: Path, scopes: ScopeInfo): void => {
    const reference = scopes.referenceOf(path.node);
    if (reference === undefined) return;
    if (reference.init === true) {
        candidate.declared = true;
        return;
    }
    const refuse = (reason: string): void => {
        candidate.refusal ??= { reason, node: path.parent ?? path.node };
    };
    if (!candidate.declared && !insideHoistedFunction(path, candidate)) return refuse("the array is used before its declaration");
    if (reference.tainted) return refuse("the array is used inside with");
    const slot = indexedBy(path);
    if (slot === undefined) return refuse("the array is used other than as S[constant index]");
    const { member, node, index } = slot;
    if (isCallee(member)) return refuse("a slot is called as a method of the array (the callee gets the array as this)");
    if (member.parent?.type === "UnaryExpression" && member.parent.operator === "delete") return refuse("a slot is deleted");
    if (index === 0) {
        if (member.isWriteTarget()) {
            candidate.argumentsWritten = true;
            return;
        }
        const element = indexedBy(member);
        const deleted = element?.member.parent?.type === "UnaryExpression" && element.member.parent.operator === "delete";
        const plain = element !== undefined && !deleted && !isCallee(element.member);
        candidate.argumentsUses.push({ member: node, from: reference.from, element: plain ? { node: element.node, index: element.index, write: element.member.isWriteTarget() } : undefined });
        return;
    }
    let info = candidate.slots.get(index);
    if (info === undefined) {
        info = { uses: [], firstWrite: undefined };
        candidate.slots.set(index, info);
    }
    info.uses.push({ member: node, from: reference.from });
    if (info.firstWrite === undefined && member.isWriteTarget()) info.firstWrite = firstWriteOf(member, candidate.body);
};

/** The statement `S[k] = value;` written by `member` when it sits directly in `body`; `null` for any other write. */
const firstWriteOf = (member: Path, body: FunctionBody): FirstWrite | null => {
    const assignment = member.parentPath;
    const statement = assignment?.parentPath;
    if (member.key !== "left" || assignment?.node.type !== "AssignmentExpression" || assignment.node.operator !== "=") return null;
    return statement?.node.type === "ExpressionStatement" && statement.parent === body ? { statement: statement.node, value: assignment.node.right } : null;
};

/**
 * Whether `path` is `arguments` handed to `(function () {...}).apply(thisArg, arguments)`. The callee is a fresh
 * function literal, so its `apply` is Function.prototype.apply (relies on model 7: builtins intact), which only reads
 * the object's length and elements to build the call's own argument list: the called function gets copies of the
 * values and never the object itself.
 */
const appliedTo = (path: Path): boolean => {
    const call = path.parent;
    // The second argument after a plain first one: behind a spread it could become `thisArg` (`apply(...[], arguments)`).
    if (call?.type !== "CallExpression" || path.key !== "arguments" || call.arguments[1] !== path.node || call.arguments[0]?.type === "SpreadElement") return false;
    const callee = call.callee;
    if (callee.type !== "MemberExpression" || propertyKey(callee) !== "apply") return false;
    return callee.object.type === "FunctionExpression" || callee.object.type === "ArrowFunctionExpression";
};

/**
 * `arguments` references that may let code write the arguments object or call through it: anything but a plain
 * read `arguments[i]` / `arguments.length` or a hand-over to a function literal's builtin `apply` (`appliedTo`). (A
 * write `arguments[i] = x` breaks `arguments[i] === parameter i` for unpassed arguments and in strict mode.)
 */
const recordArgumentsUse = (unsafe: Map<Variable, Node[]>, variable: Variable, path: Path): void => {
    const member = path.parentPath;
    const read = member !== null && path.key === "object" && member.node.type === "MemberExpression" && !member.isWriteTarget() && !isCallee(member);
    if (!read && !appliedTo(path)) unsafe.get(variable)?.push(path.node);
};

/**
 * The `arguments` of a read `[arguments][0]`: the literal is built for this one read of its element 0, which is the
 * `arguments` it holds. That identifier stays where it was, so it names the same binding (no function boundary or
 * shadowing can come between). Writes (`[arguments][0] = x` writes the throwaway array, not `arguments`), deletes and
 * calls (the array would be `this`) are left alone.
 */
const foldedArguments = (path: Path): Node | undefined => {
    const node = path.node;
    if (node.type !== "MemberExpression" || node.object.type !== "ArrayExpression" || propertyKey(node) !== "0") return undefined;
    const [only, ...rest] = node.object.elements;
    if (rest.length > 0 || only?.type !== "Identifier" || only.name !== "arguments" || path.isWriteTarget() || isCallee(path)) return undefined;
    return only;
};

interface Counts {
    folded: number;
    arrays: number;
    removed: number;
    keptForArguments: number;
    refused: number;
    slots: number;
    parameters: number;
    argumentsReads: number;
}

/** What one candidate's conversion replaces, plus the names it adds to scopes. */
interface Rewrite {
    readonly replacements: Map<Node, Node | typeof REMOVE>;
    readonly declarators: Map<VariableDeclarator, VariableDeclarator[]>;
    readonly added: Map<Scope, Set<string>>;
}

const declaratorOf = (name: string, init: Expression | null, position: Node): VariableDeclarator =>
    at<VariableDeclarator>({ type: "VariableDeclarator", id: identifier(name, position), init, definite: false }, position);

/**
 * Plans the conversion of one array's slots ≥ 1 into `var`s of its function. The name is `<array>_<index>`
 * (injective, and it says which slot it was), with `_<n>` appended until it is free: not bound in the function, not
 * a name the function's code reaches outside it (it would be shadowed), and not bound (by the analysis or by an
 * earlier conversion) in any scope between a use and the function.
 */
const convertSlots = (candidate: Candidate, rewrite: Rewrite, outside: (scope: Scope) => ReadonlySet<string>, log: PassLog): VariableDeclarator[] => {
    const { scope, literal, variable } = candidate;
    const added = rewrite.added.get(scope) ?? new Set<string>();
    rewrite.added.set(scope, added);
    const initialized = literal.elements.length;
    // Initialized slots (1 .. length-1, in the literal) and written or read ones, in index order.
    const indices = new Set<number>();
    for (let index = 1; index < initialized; index++) indices.add(index);
    for (const index of [...candidate.slots.keys()].toSorted((a, b) => a - b)) indices.add(index);
    const atDeclaration: VariableDeclarator[] = [];
    const atTop: VariableDeclarator[] = [];
    for (const index of indices) {
        const info = candidate.slots.get(index);
        const uses = info?.uses ?? [];
        const taken = (name: string): boolean => scope.set.has(name) || added.has(name) || outside(scope).has(name) || uses.some((use) => shadowedBetween(use.from, scope, name, rewrite.added));
        const base = `${variable.name}_${index}`;
        let name = base;
        for (let n = 1; taken(name); n++) name = `${base}_${n}`;
        if (name !== base) log.debug(`${base} is taken there, slot ${variable.name}[${index}] becomes ${name}`, candidate.declarator);
        added.add(name);
        for (const use of uses) rewrite.replacements.set(use.member, identifier(name, use.member));
        const firstWrite = info?.firstWrite;
        const element = literal.elements[index];
        if (index < initialized) {
            atDeclaration.push(declaratorOf(name, element === null || element === undefined || element.type === "SpreadElement" ? null : element, element ?? candidate.declarator));
        } else if (firstWrite !== undefined && firstWrite !== null) {
            const { statement, value } = firstWrite;
            rewrite.replacements.set(statement, at<VariableDeclaration>({ type: "VariableDeclaration", kind: "var", declare: false, declarations: [declaratorOf(name, value, statement)] }, statement));
        } else {
            atTop.push(declaratorOf(name, null, candidate.declarator));
        }
    }
    return [...atDeclaration, ...atTop];
};

/**
 * Why no `S[0][i]` can become parameter i; `undefined` when they may (each index is then judged by `parameterFor`).
 * The parameter list must be simple (parameter i is the only alias of `arguments[i]`), and the arguments object must
 * be reached only as `S[0][i]` with a constant i: `S[0]` never called on, deleted through or handed on, and the
 * function's other `arguments` uses plain reads or builtin `apply` hand-overs (`recordArgumentsUse`), so nothing but
 * those uses writes `arguments[i]`.
 */
const parametersRefusal = (candidate: Candidate, unsafe: ReadonlyMap<Variable, Node[]>): string | undefined => {
    const own = candidate.literal.elements[0];
    if (!hasSimpleParameters(candidate.fn.params)) return "the parameter list isn't simple";
    if (candidate.argumentsUses.some((use) => use.element === undefined)) return "S[0] is used other than as S[0][i]";
    const escapes = (candidate.argumentsObject === undefined ? [] : (unsafe.get(candidate.argumentsObject) ?? [])).filter((node) => node !== own);
    return escapes.length > 0 ? "the function uses arguments other than by reading it" : undefined;
};

/**
 * The parameter that the uses `S[0][index]` (all of them, given) can become, or why not. Both start as the value
 * passed, or undefined when none was.
 *
 * - Only reads: the parameter is never written (nor redeclared), so it equals `arguments[index]` at every read, in
 *   strict and sloppy mode alike (nothing writes `arguments[index]`). Each use is judged alone: where the
 *   parameter's name is shadowed, it stays a read of `arguments`.
 * - Some writes: the parameter is used nowhere else, so `arguments[index]` is a cell only these uses reach and the
 *   parameter can be that cell; then every use must become it.
 */
const parameterFor = (candidate: Candidate, index: number, uses: readonly ArgumentsUse[], scopes: ScopeInfo, added: ReadonlyMap<Scope, Set<string>>): string | { refused: string } => {
    const param = candidate.fn.params[index];
    if (param?.type !== "Identifier") return { refused: `there is no parameter ${index}` };
    const variable = scopes.variableOf(param);
    if (variable === undefined || variable.defs.length !== 1) return { refused: `parameter ${param.name} is redeclared` };
    if (!uses.some((use) => use.element?.write === true)) return variable.references.some((r) => r.isWrite()) ? { refused: `parameter ${param.name} is written` } : param.name;
    if (variable.references.length > 0) return { refused: `S[0][${index}] is written and parameter ${param.name} is also used directly` };
    if (uses.some((use) => shadowedBetween(use.from, candidate.scope, param.name, added))) return { refused: `S[0][${index}] is written and parameter ${param.name} is shadowed at a use` };
    return param.name;
};

/**
 * Whether `arguments` written at a use from `from` names the function's own arguments object: no function with its
 * own `arguments` (non-arrow: eslint-scope binds it there) or class field/static block (where it is an error) between.
 */
const ownArgumentsVisible = (from: Scope, fnScope: Scope): boolean => {
    for (let scope: Scope | null = from; scope !== null && scope !== fnScope; scope = scope.upper) {
        if (scope.set.has("arguments") || scope.type === "class-field-initializer" || scope.type === "class-static-block") return false;
    }
    return true;
};

/** Converts `S[0]` uses into parameters or `arguments`, where exact. Returns how many uses keep the array. */
const convertArguments = (candidate: Candidate, rewrite: Rewrite, unsafe: ReadonlyMap<Variable, Node[]>, scopes: ScopeInfo, counts: Counts, log: PassLog): number => {
    const { argumentsUses: uses, scope } = candidate;
    if (uses.length === 0) return 0;
    if (candidate.argumentsWritten || candidate.argumentsObject === undefined) {
        log.debug(candidate.argumentsWritten ? "kept for S[0]: it is written" : "kept for S[0]: element 0 isn't this function's own unwritten arguments", candidate.declarator);
        return uses.length;
    }
    const refusal = parametersRefusal(candidate, unsafe);
    if (refusal !== undefined) log.debug(`S[0][i] stay uses of arguments: ${refusal}`, candidate.declarator);
    const byIndex = new Map<number, ArgumentsUse[]>();
    for (const use of uses) {
        if (use.element === undefined) continue;
        const group = byIndex.get(use.element.index);
        if (group === undefined) byIndex.set(use.element.index, [use]);
        else group.push(use);
    }
    const parameters = new Map<number, string | { refused: string }>();
    for (const [index, indexed] of byIndex) {
        const parameter = refusal === undefined ? parameterFor(candidate, index, indexed, scopes, rewrite.added) : { refused: refusal };
        parameters.set(index, parameter);
        if (refusal === undefined && typeof parameter !== "string") log.debug(`S[0][${index}] stays a use of arguments: ${parameter.refused}`, candidate.declarator);
    }
    let kept = 0;
    for (const use of uses) {
        const parameter = use.element === undefined ? undefined : parameters.get(use.element.index);
        if (use.element !== undefined && typeof parameter === "string") {
            if (!shadowedBetween(use.from, scope, parameter, rewrite.added)) {
                rewrite.replacements.set(use.element.node, identifier(parameter, use.element.node));
                counts.parameters++;
                continue;
            }
            log.debug(`S[0][${use.element.index}] stays a read of arguments: parameter ${parameter} is shadowed here`, use.element.node);
        }
        if (!ownArgumentsVisible(use.from, scope)) {
            log.debug("kept S[0]: arguments here is another function's own (or not allowed)", use.member);
            kept++;
            continue;
        }
        rewrite.replacements.set(use.member, identifier("arguments", use.member));
        counts.argumentsReads++;
    }
    return kept;
};

/** Plans one candidate: its `S[0]` uses, then its other slots, then what replaces its declarator. */
const convert = (
    candidate: Candidate,
    rewrite: Rewrite,
    unsafe: ReadonlyMap<Variable, Node[]>,
    outside: (scope: Scope) => ReadonlySet<string>,
    scopes: ScopeInfo,
    counts: Counts,
    log: PassLog
): void => {
    const kept = convertArguments(candidate, rewrite, unsafe, scopes, counts, log);
    const declarators = convertSlots(candidate, rewrite, outside, log);
    counts.slots += declarators.length;
    const { declarator, literal } = candidate;
    if (kept > 0) {
        const array = at<ArrayExpression>({ type: "ArrayExpression", elements: literal.elements.slice(0, 1) }, literal);
        declarators.unshift(at<VariableDeclarator>({ ...declarator, init: array }, declarator));
        counts.keptForArguments++;
    } else {
        counts.removed++;
    }
    rewrite.declarators.set(declarator, declarators);
    log.debug(`${candidate.variable.name}: ${candidate.slots.size} slot(s) to locals${kept > 0 ? `, kept for ${kept} use(s) of S[0]` : ", array removed"}`, declarator);
};

/**
 * Arguments arrays: `function f(a) { var S = [arguments]; S[3] = g(S[0][0]); return S[3]; }` becomes
 * `function f(a) { var S_3 = g(a); return S_3; }` (#9).
 *
 * Exact because the array is local and kept to itself: declared once by a `var` statement directly in the function
 * body, which nothing before it can use the array from (`insideHoistedFunction`), its initializer elements run no
 * code, and every use is `S[constant index]`, never called as a method of the array (it would be `this`), deleted,
 * or inside `with`, in a function without direct eval. Its slots then hold only what is written to them, exactly
 * like a `var` per slot: function-scoped and hoisted (reads before the first write see undefined), one binding per
 * invocation shared with closures. Slot 0 is the function's own `arguments` object (never reassigned): its uses
 * `S[0][i]` become parameter i when that is exact (`parametersRefusal`, `parameterFor`), other uses become
 * `arguments` where that name means the same object (`ownArgumentsVisible`); the array stays (as `[arguments]`)
 * only for uses neither covers. Parameters are never added (`length` would change). Names: `convertSlots`.
 *
 * Also folds the inline form `[arguments][0]` to `arguments` (`foldedArguments`).
 *
 * Runs between the simplify and cleanup groups: the passes before it (constants, code-locks, builders) read the slot
 * shapes, and cleanup then drops the locals whose reads constants already resolved.
 */
export const argumentsArrays: Pass = {
    name: "arguments-arrays",
    description: "Turn `var S = [arguments]` slot arrays into parameters and local variables",
    run({ program, log, scope }: PassContext): PassResult {
        const scopes = scope();
        const candidates = findCandidates(scopes);

        const sites = new Map<Node, Candidate>();
        const hoisted = new Map<Node, Candidate[]>();
        const argumentsSites = new Map<Node, Variable>();
        const unsafe = new Map<Variable, Node[]>();
        for (const candidate of candidates) {
            if (candidate.refusal !== undefined) continue;
            for (const reference of candidate.variable.references) sites.set(reference.identifier as unknown as Node, candidate);
            for (const variable of candidate.scope.variables) {
                if (!variable.defs.some((def) => def.type === "FunctionName")) continue;
                for (const reference of variable.references) {
                    const id = reference.identifier as unknown as Node;
                    hoisted.set(id, [...(hoisted.get(id) ?? []), candidate]);
                }
            }
            const args = candidate.argumentsObject;
            if (args === undefined || unsafe.has(args)) continue;
            unsafe.set(args, []);
            for (const reference of args.references) argumentsSites.set(reference.identifier as unknown as Node, args);
        }
        let folded = 0;
        traverse(program, {
            MemberExpression(path) {
                const replacement = foldedArguments(path);
                if (replacement === undefined) return;
                log.debug("[arguments][0] -> arguments", path.node);
                path.replace(replacement);
                folded++;
                // The walk doesn't visit the replacement itself: record it as the `arguments` use it now is.
                const args = argumentsSites.get(replacement);
                if (args !== undefined) recordArgumentsUse(unsafe, args, path);
            },
            Identifier(path) {
                const candidate = sites.get(path.node);
                if (candidate !== undefined) recordUse(candidate, path, scopes);
                for (const early of hoisted.get(path.node) ?? []) {
                    if (!early.declared) early.refusal ??= { reason: `${path.node.name} (it may use the array) is referenced before the declaration`, node: path.node };
                }
                const args = argumentsSites.get(path.node);
                if (args !== undefined) recordArgumentsUse(unsafe, args, path);
            },
        });

        const outsideNames = new Map<Scope, Set<string>>();
        const outside = (fnScope: Scope): ReadonlySet<string> => {
            let names = outsideNames.get(fnScope);
            if (names === undefined) {
                names = new Set(fnScope.through.map((reference) => reference.identifier.name));
                outsideNames.set(fnScope, names);
            }
            return names;
        };
        const counts: Counts = { folded, arrays: candidates.length, removed: 0, keptForArguments: 0, refused: 0, slots: 0, parameters: 0, argumentsReads: 0 };
        const rewrite: Rewrite = { replacements: new Map(), declarators: new Map(), added: new Map() };
        for (const candidate of candidates) {
            if (candidate.refusal !== undefined) {
                counts.refused++;
                log.debug(`kept ${candidate.variable.name}: ${candidate.refusal.reason}`, candidate.refusal.node);
                continue;
            }
            convert(candidate, rewrite, unsafe, outside, scopes, counts, log);
        }

        for (const candidate of candidates) {
            const declaration = candidate.variable.defs[0]?.parent as unknown as VariableDeclaration;
            if (candidate.refusal !== undefined || rewrite.replacements.has(declaration)) continue;
            const declarations = declaration.declarations.flatMap((d) => rewrite.declarators.get(d) ?? [d]);
            rewrite.replacements.set(declaration, declarations.length === 0 ? REMOVE : at<VariableDeclaration>({ ...declaration, declarations }, declaration));
        }
        traverse(program, {
            enter(path) {
                const replacement = rewrite.replacements.get(path.node);
                if (replacement === REMOVE) path.remove();
                else if (replacement !== undefined) path.replace(replacement);
            },
        });

        log.info(
            `${counts.arrays} arguments array(s): ${counts.removed} removed, ${counts.keptForArguments} kept for S[0], ${counts.refused} refused; ${counts.slots} slot(s) to locals, ${counts.parameters} S[0][i] to parameters, ${counts.argumentsReads} S[0] to arguments; ${folded} [arguments][0] folded`
        );
        const converted = counts.removed + counts.keptForArguments;
        // Folds only replace expressions; converting arrays adds and removes declarations.
        return { changed: converted + folded, bindingsChanged: converted > 0, stats: { ...counts } };
    },
};
