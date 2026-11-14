import type {
    ArrayExpression,
    Expression,
    ExpressionStatement,
    FunctionBody,
    Function as FunctionNode,
    FunctionLike,
    MemberExpression,
    Node,
    VariableDeclaration,
    VariableDeclarator,
} from "../core/ast.js";
import { isIndexKey, propertyKey } from "../core/ast.js";
import { at, identifier } from "../core/build.js";
import { pushAll } from "../core/list.js";
import type { Scope, ScopeInfo, Variable } from "../core/scope.js";
import type { Path } from "../core/traverse.js";
import { forEachChild, traverse, walkSkippingFunctions } from "../core/traverse.js";
import type { PassLog } from "../core/log.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

interface SlotUse {
    readonly member: MemberExpression;
    readonly from: Scope;
}

/** Only when the first write is a statement `S[k] = value;` in one of the array's blocks. */
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

/** `var S = [arguments, ...]`, or `var S;` written once by the statement `S = [arguments, ...];`. */
interface Candidate {
    readonly variable: Variable;
    readonly scope: Scope;
    readonly fn: FunctionLike;
    readonly body: FunctionBody;
    readonly declarator: VariableDeclarator;
    readonly literal: ArrayExpression;
    readonly assigned: Node | undefined;
    site: Node;
    /** The function body and the blocks between it and the site: statements in them run at most once per call. */
    readonly blocks: Set<Node>;
    siteBlock: Node;
    /** The function's own `arguments` object in element 0, never reassigned; `undefined` otherwise. */
    readonly argumentsObject: Variable | undefined;
    readonly slots: Map<number, SlotInfo>;
    readonly argumentsUses: ArgumentsUse[];
    argumentsWritten: boolean;
    /** The walk has passed the site (tree order is execution order within the function, see `siteRefusal`). */
    declared: boolean;
    refusal: { readonly reason: string; readonly node: Node } | undefined;
}

const REMOVE: unique symbol = Symbol("remove");

/**
 * Code before the site must not use the array (`S[k]` would throw where the local reads undefined). That code
 * reaches it only by naming it, or by calling a function declared in the function body (created on entry): so the
 * walk refuses references to the array before the site, except inside such a function, and references to such a
 * function before the site, except inside such a function (`recordUse`, `recordHoistedUse`): the first of them to run
 * is called through a reference outside them all.
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

const isArgumentsArray = (node: Node | null | undefined): node is ArrayExpression => {
    if (node?.type !== "ArrayExpression") return false;
    const first = node.elements[0];
    return first?.type === "Identifier" && first.name === "arguments";
};

const isCallee = (path: Path): boolean => (path.parent?.type === "CallExpression" && path.key === "callee") || (path.parent?.type === "TaggedTemplateExpression" && path.key === "tag");

const indexedBy = (path: Path): { member: Path; node: MemberExpression; index: number } | undefined => {
    const member = path.parentPath;
    const node = member?.node;
    if (member === null || node?.type !== "MemberExpression" || path.key !== "object") return undefined;
    const key = propertyKey(node);
    return key === undefined || !isIndexKey(key) ? undefined : { member, node, index: Number(key) };
};

/** Names bound per scope by the conversions: `added` declared, `removed` no longer declared (converted arrays). */
interface Bindings {
    readonly scopes: ScopeInfo;
    readonly added: Map<Scope, Set<string>>;
    readonly removed: Map<Scope, Set<string>>;
}

const binds = (scope: Scope, name: string, bindings: Bindings): boolean =>
    (bindings.scopes.bindsName(scope, name) && bindings.removed.get(scope)?.has(name) !== true) || bindings.added.get(scope)?.has(name) === true;

/** Whether a scope from `from` up to, not including, `fnScope` passes `test`. */
const anyScopeBetween = (from: Scope, fnScope: Scope, test: (scope: Scope) => boolean): boolean => {
    for (let scope: Scope | null = from; scope !== null && scope !== fnScope; scope = scope.upper) if (test(scope)) return true;
    return false;
};

const shadowedBetween = (from: Scope, fnScope: Scope, name: string, bindings: Bindings): boolean => anyScopeBetween(from, fnScope, (scope) => binds(scope, name, bindings));

const declarationRefusal = (candidate: Candidate, declaration: VariableDeclaration, scopes: ScopeInfo): string | undefined => {
    const { variable, scope, literal } = candidate;
    if (variable.defs.length !== 1) return "the array's name is declared more than once";
    if (declaration.kind !== "var") return `the array is declared with ${declaration.kind}`;
    if (scope.dynamic) return "the function (or one nested in it) calls eval directly: its references are unresolved";
    return literal.elements.slice(1).every((e) => evaluatesInertly(e, scopes)) ? undefined : "an initializer element runs code (it could use the array before it exists)";
};

/**
 * Finds the arrays, descendants before ancestors (reverse of the scope manager's pre-order), so the names a nested
 * function's conversion adds and removes are known when an enclosing function's slots are named. Refusals that need
 * no walk are decided here.
 */
const findCandidates = (scopes: ScopeInfo): Candidate[] => {
    const candidates: Candidate[] = [];
    for (const scope of scopes.manager.scopes.toReversed()) {
        if (scope.type !== "function") continue;
        // eslint-scope's function scopes are those of functions and arrows; one without a block body declares no var.
        const fn = scope.block as unknown as FunctionLike;
        const body = fn.body !== null && fn.body.type === "BlockStatement" ? fn.body : undefined;
        if (body === undefined) continue;
        for (const variable of scope.variables) {
            const def = variable.defs[0];
            if (def?.type !== "Variable") continue;
            const declarator = def.node as unknown as VariableDeclarator;
            let literal: ArrayExpression;
            let assigned: Node | undefined;
            if (declarator.init !== null) {
                if (!isArgumentsArray(declarator.init)) continue;
                literal = declarator.init;
            } else {
                // The first write that creates such an array: another write of the name is a use `recordUse` refuses.
                const write = scopes.references(variable)?.find((r) => r.isWrite() && isArgumentsArray(r.writeExpr as unknown as Node | null | undefined));
                if (write === undefined) continue;
                literal = write.writeExpr as unknown as ArrayExpression;
                assigned = write.identifier as unknown as Node;
            }
            const declaration = def.parent as unknown as VariableDeclaration;
            const argumentsVariable = scopes.variableOf(literal.elements[0] as Node);
            const argumentsReferences = argumentsVariable === undefined ? undefined : scopes.references(argumentsVariable);
            const owned = argumentsVariable?.scope === scope && argumentsVariable.defs.length === 0 && argumentsReferences !== undefined && argumentsReferences.every((r) => !r.isWrite());
            const candidate: Candidate = {
                variable,
                scope,
                fn,
                body,
                declarator,
                literal,
                assigned,
                site: declarator,
                blocks: new Set([body]),
                siteBlock: body,
                argumentsObject: owned ? argumentsVariable : undefined,
                slots: new Map(),
                argumentsUses: [],
                argumentsWritten: false,
                declared: false,
                refusal: undefined,
            };
            const reason = declarationRefusal(candidate, declaration, scopes);
            if (reason !== undefined) candidate.refusal = { reason, node: assigned ?? declarator };
            candidates.push(candidate);
        }
    }
    return candidates;
};

/** Labels don't reach into nested functions. */
const breaksTo = (node: Node, labels: ReadonlySet<string>): boolean => {
    let found = false;
    walkSkippingFunctions(node, (child) => {
        if (found || child.type === "ClassBody") return false;
        if (child.type !== "BreakStatement") return true;
        found = child.label !== null && labels.has(child.label.name);
        return false;
    });
    return found;
};

/**
 * Why the site statement (the `var` declaration, or the statement `S = [arguments, ...];`) doesn't allow the
 * conversion, after recording the blocks around it. It must sit in the function body, possibly in plain blocks and
 * labeled statements, so it runs at most once per call and the code after it in tree order runs after it: no loop,
 * branch or `try` around it, no function declared in such a block (created on the block's entry, it could run
 * before), and no `break` before it out of a labeled statement around it (it would skip the site and run the code
 * after it).
 */
const siteRefusal = (candidate: Candidate, statement: Path): string | undefined => {
    const labels = new Set<string>();
    const levels: { block: Node & { body: Node[] }; index: number }[] = [];
    for (let current = statement; ;) {
        const parent = current.parentPath;
        if (parent?.node.type === "LabeledStatement") {
            labels.add(parent.node.label.name);
            current = parent;
            continue;
        }
        if (parent?.node.type !== "BlockStatement" || current.index === null) return "the array is created in a statement that may run more than once or not at all (in a loop, branch, try or switch)";
        if (parent.node === candidate.body) break;
        if (parent.node.body.some((s) => s.type === "FunctionDeclaration")) return "a block around the array's creation declares a function (created on entry, it could run first)";
        levels.push({ block: parent.node, index: current.index });
        if (candidate.siteBlock === candidate.body) candidate.siteBlock = parent.node;
        candidate.blocks.add(parent.node);
        current = parent;
    }
    if (labels.size === 0) return undefined;
    for (const { block, index } of levels) {
        if (block.body.slice(0, index).some((s) => breaksTo(s, labels))) return "a break before the array's creation can leave a labeled statement around it (skipping the creation)";
    }
    return undefined;
};

const recordSite = (candidate: Candidate, path: Path): void => {
    candidate.declared = true;
    let statement: Path | null;
    if (candidate.assigned === undefined) {
        statement = path.parentPath?.parentPath ?? null;
    } else {
        const assignment = path.parentPath;
        if (path.key !== "left" || assignment?.node.type !== "AssignmentExpression" || assignment.node.operator !== "=" || assignment.parent?.type !== "ExpressionStatement") {
            candidate.refusal ??= { reason: "the array is assigned other than by a statement S = [arguments, ...]", node: path.parent ?? path.node };
            return;
        }
        statement = assignment.parentPath;
        if (statement !== null) candidate.site = statement.node;
    }
    const reason = statement === null ? "the array's creation isn't a statement" : siteRefusal(candidate, statement);
    if (reason !== undefined) candidate.refusal ??= { reason, node: candidate.site };
};

/**
 * Refuses the array when used as anything but `S[index]`, when a slot is called as a method (it would get the array
 * as `this`), deleted (a `var` can't be), or used inside `with`.
 */
const recordUse = (candidate: Candidate, path: Path, scopes: ScopeInfo): void => {
    const reference = scopes.referenceOf(path.node);
    if (reference === undefined) return;
    if (reference.init === true || path.node === candidate.assigned) return recordSite(candidate, path);
    const refuse = (reason: string): void => {
        candidate.refusal ??= { reason, node: path.parent ?? path.node };
    };
    if (!candidate.declared && !insideHoistedFunction(path, candidate)) return refuse("the array is used before it is created");
    if (reference.tainted) return refuse("the array is used inside with");
    const slot = indexedBy(path);
    if (slot === undefined) return refuse("the array is used other than as S[constant index]");
    const { member, node, index } = slot;
    if (isCallee(member)) return refuse("a slot is called as a method of the array (the callee gets the array as this)");
    if (member.parent?.type === "UnaryExpression" && member.parent.operator === "delete") return refuse("a slot is deleted");
    if (index === 0) {
        if (member.isWriteTarget()) {
            candidate.argumentsWritten = true;
            candidate.argumentsUses.push({ member: node, from: reference.from, element: undefined });
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
    if (info.firstWrite === undefined && member.isWriteTarget()) info.firstWrite = firstWriteOf(member, candidate.blocks);
};

/** The statement `S[k] = value;` written by `member` when it sits in one of `blocks`; `null` for any other write. */
const firstWriteOf = (member: Path, blocks: ReadonlySet<Node>): FirstWrite | null => {
    const assignment = member.parentPath;
    const statement = assignment?.parentPath;
    if (member.key !== "left" || assignment?.node.type !== "AssignmentExpression" || assignment.node.operator !== "=") return null;
    return statement?.node.type === "ExpressionStatement" && statement.parent !== null && blocks.has(statement.parent) ? { statement: statement.node, value: assignment.node.right } : null;
};

/**
 * The function literal `path` (an `arguments`) is handed to by `(function () {...}).apply(thisArg, arguments)`. The
 * callee is a fresh function literal, so its `apply` is Function.prototype.apply (relies on model 7: builtins intact),
 * which only reads the object's length and elements to build the call's own argument list: the called function gets
 * copies of the values and never the object itself.
 */
const appliedTo = (path: Path): FunctionLike | undefined => {
    const call = path.parent;
    // The second argument after a plain first one: behind a spread it could become `thisArg` (`apply(...[], arguments)`).
    if (call?.type !== "CallExpression" || path.key !== "arguments" || call.arguments[1] !== path.node || call.arguments[0]?.type === "SpreadElement") return undefined;
    const callee = call.callee;
    if (callee.type !== "MemberExpression" || propertyKey(callee) !== "apply") return undefined;
    return callee.object.type === "FunctionExpression" || callee.object.type === "ArrowFunctionExpression" ? callee.object : undefined;
};

/**
 * Whether the values a call passes to the function literal `fn` go nowhere: it declares no parameters, and has no
 * arguments object of its own (an arrow), or names it only as element 0 of arrays converted with no use of that
 * element (`owners`: the arrays by that identifier; once converted, nothing names the object). (`fn` sits in the
 * array's function, which calls no eval, so `fn` doesn't either.)
 */
const ignoresArguments = (fn: FunctionLike, scopes: ScopeInfo, owners: ReadonlyMap<Node, Candidate>): boolean => {
    if (fn.params.length > 0) return false;
    if (fn.type === "ArrowFunctionExpression") return true;
    // The function's own scope (inside the one a named function expression gives its name).
    const own = scopes.scopeOf(fn, true)?.set.get("arguments");
    const references = own === undefined ? undefined : scopes.references(own);
    return (
        references !== undefined &&
        references.every((reference) => {
            const owner = owners.get(reference.identifier as unknown as Node);
            return owner !== undefined && owner.refusal === undefined && owner.argumentsUses.length === 0;
        })
    );
};

/**
 * A function's `arguments` references other than through arrays: `unsafe` ones may let code write the arguments
 * object or call through it (anything but a plain read `arguments[i]` / `arguments.length` or a hand-over to a
 * function literal's builtin `apply`, see `appliedTo`; a write `arguments[i] = x` breaks `arguments[i] === parameter
 * i` for unpassed arguments and in strict mode); `elementReads` read its elements (plain reads but `.length`),
 * `indexed` are those with a constant index, and `applied` are the function literals it is handed to, which read them
 * all (see `ignoresArguments`).
 */
interface ArgumentsReferences {
    readonly unsafe: Node[];
    readonly elementReads: Node[];
    readonly indexed: { readonly member: MemberExpression; readonly index: number }[];
    readonly applied: FunctionLike[];
}

const recordArgumentsUse = (references: ArgumentsReferences, path: Path): void => {
    const member = path.parentPath;
    if (member !== null && path.key === "object" && member.node.type === "MemberExpression" && !member.isWriteTarget() && !isCallee(member)) {
        if (propertyKey(member.node) !== "length") references.elementReads.push(path.node);
        const element = indexedBy(path);
        if (element !== undefined) references.indexed.push({ member: element.node, index: element.index });
        return;
    }
    const applied = appliedTo(path);
    if (applied === undefined) references.unsafe.push(path.node);
    else references.applied.push(applied);
};

/**
 * Whether the parameter list names `arguments` (outside nested non-arrow functions). eslint-scope never resolves such
 * a use (`__isValidResolution`), so it is missing from the recorded uses: `b = (arguments[0] = x)` would go unseen.
 */
const parametersNameArguments = (fn: FunctionLike): boolean => {
    const names = (node: Node): boolean => {
        if (node.type === "Identifier") return node.name === "arguments";
        if (node.type === "FunctionExpression" || node.type === "FunctionDeclaration") return false;
        let found = false;
        forEachChild(node, (child) => {
            found ||= names(child);
        });
        return found;
    };
    return fn.params.some((param) => names(param as Node));
};

/**
 * Direct reads `arguments[i]` of a function that reaches its arguments object only by such reads, `.length` and
 * builtin `apply` hand-overs (no `unsafe` use, none in the parameter list: nothing writes or deletes an element, in
 * either mapping mode) become parameter i: a plain name declared once and never written, so it holds the value
 * passed, or undefined, for the whole call, as `arguments[i]` does. The use must see the parameter's name (no binding
 * or `with` between). A function calling eval (or nesting a call) records no uses: eslint-scope leaves its references
 * unresolved.
 */
const convertDirectReads = (variable: Variable, references: ArgumentsReferences, scopes: ScopeInfo, rewrite: Rewrite): number => {
    const scope = variable.scope;
    const fn = scope.block as unknown as FunctionNode;
    if (references.unsafe.length > 0 || references.indexed.length === 0 || parametersNameArguments(fn)) return 0;
    let converted = 0;
    for (const { member, index } of references.indexed) {
        const param = fn.params[index];
        if (param?.type !== "Identifier") continue;
        const parameter = scopes.variableOf(param);
        const written = parameter === undefined ? undefined : scopes.references(parameter)?.some((r) => r.isWrite());
        if (parameter === undefined || parameter.defs.length !== 1 || written !== false) continue;
        const reference = scopes.referenceOf(member.object);
        if (reference === undefined || anyScopeBetween(reference.from, scope, (s) => s.type === "with") || shadowedBetween(reference.from, scope, param.name, rewrite)) continue;
        rewrite.replacements.set(member, identifier(param.name, member));
        converted++;
    }
    return converted;
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
    refused: number;
    slots: number;
    parameters: number;
    copies: number;
    argumentsReads: number;
    argumentsLocals: number;
    directReads: number;
}

interface Rewrite extends Bindings {
    readonly replacements: Map<Node, Node | typeof REMOVE>;
    readonly declarators: Map<VariableDeclarator, VariableDeclarator[]>;
}

const declaratorOf = (name: string, init: Expression | null, position: Node): VariableDeclarator =>
    at<VariableDeclarator>({ type: "VariableDeclarator", id: identifier(name, position), init, definite: false }, position);

interface Conversion {
    readonly candidate: Candidate;
    readonly rewrite: Rewrite;
    readonly outside: ReadonlySet<string>;
    readonly owners: ReadonlyMap<Node, Candidate>;
    readonly log: PassLog;
}

/**
 * A new `var` name of the candidate's function, `base` or `base_<n>`, free for the uses at `from`: not bound in the
 * function, not a name the function's code reaches outside it (it would be shadowed), and not bound (by the analysis
 * or by a conversion) in any scope between a use and the function.
 */
const freshName = ({ candidate, rewrite, outside, log }: Conversion, base: string, from: readonly Scope[], what: string): string => {
    const { scope } = candidate;
    const added = rewrite.added.get(scope) ?? new Set<string>();
    rewrite.added.set(scope, added);
    const taken = (name: string): boolean => binds(scope, name, rewrite) || outside.has(name) || from.some((use) => shadowedBetween(use, scope, name, rewrite));
    let name = base;
    for (let n = 1; taken(name); n++) name = `${base}_${n}`;
    if (name !== base) log.debug(`${base} is taken there, ${what} becomes ${name}`, candidate.site);
    added.add(name);
    return name;
};

/**
 * Plans the conversion of the array's slots ≥ 1 into `var`s of its function, named `<array>_<index>` (injective, and
 * it says which slot it was; see `freshName`). A slot initialized in the literal is declared at the site with its
 * element; one first written by a statement `S[k] = value;` in the function body or a block around the site is
 * declared there (`var x = v` runs as `x = v`, and the `var` is the function's wherever it sits); others at the site.
 */
const convertSlots = (conversion: Conversion): VariableDeclarator[] => {
    const { candidate, rewrite } = conversion;
    const { literal, variable } = candidate;
    const initialized = literal.elements.length;
    const indices = new Set<number>();
    for (let index = 1; index < initialized; index++) indices.add(index);
    for (const index of [...candidate.slots.keys()].toSorted((a, b) => a - b)) indices.add(index);
    const atSite: VariableDeclarator[] = [];
    const atTop: VariableDeclarator[] = [];
    for (const index of indices) {
        const info = candidate.slots.get(index);
        const uses = info?.uses ?? [];
        const name = freshName(
            conversion,
            `${variable.name}_${index}`,
            uses.map((use) => use.from),
            `slot ${variable.name}[${index}]`
        );
        for (const use of uses) rewrite.replacements.set(use.member, identifier(name, use.member));
        const firstWrite = info?.firstWrite;
        const element = literal.elements[index];
        if (index < initialized) {
            atSite.push(declaratorOf(name, element === null || element === undefined || element.type === "SpreadElement" ? null : element, element ?? candidate.site));
        } else if (firstWrite !== undefined && firstWrite !== null) {
            const { statement, value } = firstWrite;
            rewrite.replacements.set(statement, at<VariableDeclaration>({ type: "VariableDeclaration", kind: "var", declare: false, declarations: [declaratorOf(name, value, statement)] }, statement));
        } else {
            atTop.push(declaratorOf(name, null, candidate.site));
        }
    }
    return [...atSite, ...atTop];
};

/**
 * Why no `S[0][i]` can become parameter i; `undefined` when they may (each index is then judged by `parameterFor`).
 * The arguments object must be reached only as `S[0][i]` with a constant i: `S[0]` never written, called on, deleted
 * through or handed on, and the function's other `arguments` uses plain reads or builtin `apply` hand-overs
 * (`recordArgumentsUse`), none in the parameter list (`parametersNameArguments`), so nothing but those uses writes
 * `arguments[i]`.
 */
const parametersRefusal = (candidate: Candidate, references: ArgumentsReferences): string | undefined => {
    const own = candidate.literal.elements[0];
    if (candidate.argumentsUses.some((use) => use.element === undefined)) return "S[0] is used other than as S[0][i]";
    if (parametersNameArguments(candidate.fn)) return "the parameter list uses arguments";
    return references.unsafe.some((node) => node !== own) ? "the function uses arguments other than by reading it" : undefined;
};

/**
 * The parameter that the uses `S[0][index]` (all of them, given) can become, or why not. Parameter `index` must be a
 * plain name (no default, pattern or rest), so both start as the value passed, or undefined when none was, and
 * declared once (no other parameter of that name, which would be the one it binds; no function or `var` of it).
 *
 * - Only reads: the parameter is never written (nor redeclared), so it equals `arguments[index]` at every read, in
 *   strict and sloppy mode and with mapped or unmapped `arguments` alike (nothing writes `arguments[index]`).
 * - Some writes: the parameter is used nowhere else and the elements of `arguments` aren't read but through these
 *   uses (`elementsRead`; its `length` is, which element writes don't change), so `arguments[index]` is a cell only
 *   these uses reach and the parameter can be that cell; then every use must become it.
 */
const parameterFor = (candidate: Candidate, index: number, uses: readonly ArgumentsUse[], elementsRead: boolean, scopes: ScopeInfo, bindings: Bindings): string | { refused: string } => {
    const param = candidate.fn.params[index];
    if (param === undefined) return { refused: `there is no parameter ${index}` };
    if (param.type !== "Identifier") return { refused: `parameter ${index} has a default value, a pattern or is a rest parameter` };
    const variable = scopes.variableOf(param);
    if (variable === undefined || variable.defs.length !== 1) return { refused: `parameter ${param.name} is declared again` };
    const references = scopes.references(variable);
    if (references === undefined) return { refused: `a with statement may intercept a use of parameter ${param.name}` };
    if (!uses.some((use) => use.element?.write === true)) return references.some((r) => r.isWrite()) ? { refused: `parameter ${param.name} is written` } : param.name;
    if (references.length > 0) return { refused: `S[0][${index}] is written and parameter ${param.name} is also used directly` };
    if (elementsRead) return { refused: `S[0][${index}] is written and arguments is also read directly` };
    if (uses.some((use) => shadowedBetween(use.from, candidate.scope, param.name, bindings))) return { refused: `S[0][${index}] is written and parameter ${param.name} is shadowed at a use` };
    return param.name;
};

/**
 * Whether `arguments` written at a use from `from` names the function's own arguments object: no function with its
 * own `arguments` (non-arrow: eslint-scope binds it there) or class field/static block (where it is an error) between.
 */
const ownArgumentsVisible = (from: Scope, fnScope: Scope): boolean =>
    !anyScopeBetween(from, fnScope, (scope) => scope.set.has("arguments") || scope.type === "class-field-initializer" || scope.type === "class-static-block");

/**
 * Converts the `S[0]` uses. `S[0][i]` becomes parameter i where exact (`parametersRefusal`, `parameterFor`); where
 * that parameter's name is shadowed, a copy of it declared at the site (`var a_1 = a`): only read and never written,
 * the parameter holds one value for the whole call. Other uses become `arguments` where that name means the same
 * object (`ownArgumentsVisible`), and the rest a local declared at the site with element 0 (`var S_0 = arguments`):
 * element 0 is a slot like the others. Returns the declarators to add at the site.
 */
const convertArguments = (conversion: Conversion, references: ReadonlyMap<Variable, ArgumentsReferences>, scopes: ScopeInfo, counts: Counts): VariableDeclarator[] => {
    const { candidate, rewrite, log } = conversion;
    const { argumentsUses: uses, scope, literal, variable } = candidate;
    if (uses.length === 0) return [];
    const toLocal: ArgumentsUse[] = [];
    const declarators: VariableDeclarator[] = [];
    const own = candidate.argumentsObject === undefined ? undefined : references.get(candidate.argumentsObject);
    if (candidate.argumentsWritten || own === undefined) {
        log.debug(candidate.argumentsWritten ? "S[0] is written: it becomes a local" : "element 0 isn't this function's own unwritten arguments: S[0] becomes a local", candidate.site);
        pushAll(toLocal, uses);
    } else {
        const refusal = parametersRefusal(candidate, own);
        if (refusal !== undefined) log.debug(`S[0][i] stay uses of arguments: ${refusal}`, candidate.site);
        const byIndex = new Map<number, ArgumentsUse[]>();
        for (const use of uses) {
            if (use.element === undefined) continue;
            const group = byIndex.get(use.element.index);
            if (group === undefined) byIndex.set(use.element.index, [use]);
            else group.push(use);
        }
        const elementsRead = own.elementReads.length > 0 || own.applied.some((fn) => !ignoresArguments(fn, scopes, conversion.owners));
        const parameters = new Map<number, string | { refused: string }>();
        for (const [index, indexed] of byIndex) {
            const parameter = refusal === undefined ? parameterFor(candidate, index, indexed, elementsRead, scopes, rewrite) : { refused: refusal };
            parameters.set(index, parameter);
            if (refusal === undefined && typeof parameter !== "string") log.debug(`S[0][${index}] stays a use of arguments: ${parameter.refused}`, candidate.site);
        }
        // The copy is declared at the site: the parameter's name must mean the parameter there too.
        const siteScope = scopes.scopeOf(candidate.siteBlock) ?? scope;
        const copies = new Map<number, ArgumentsUse[]>();
        for (const use of uses) {
            const parameter = use.element === undefined ? undefined : parameters.get(use.element.index);
            if (use.element !== undefined && typeof parameter === "string") {
                if (!shadowedBetween(use.from, scope, parameter, rewrite)) {
                    rewrite.replacements.set(use.element.node, identifier(parameter, use.element.node));
                    counts.parameters++;
                    continue;
                }
                // `parameterFor` gives a written S[0][i] its parameter only where no use shadows it: this one reads.
                if (!shadowedBetween(siteScope, scope, parameter, rewrite)) {
                    log.debug(`S[0][${use.element.index}] reads a copy of parameter ${parameter}: its name is shadowed here`, use.element.node);
                    const group = copies.get(use.element.index);
                    if (group === undefined) copies.set(use.element.index, [use]);
                    else group.push(use);
                    continue;
                }
                log.debug(`S[0][${use.element.index}] stays a read of arguments: parameter ${parameter} is shadowed here and where the array is created`, use.element.node);
            }
            if (!ownArgumentsVisible(use.from, scope)) {
                log.debug("S[0] becomes a local: arguments here is another function's own (or not allowed)", use.member);
                toLocal.push(use);
                continue;
            }
            rewrite.replacements.set(use.member, identifier("arguments", use.member));
            counts.argumentsReads++;
        }
        for (const [index, group] of copies) {
            const parameter = parameters.get(index) as string;
            const name = freshName(
                conversion,
                `${parameter}_1`,
                group.map((use) => use.from),
                `the copy of parameter ${parameter}`
            );
            for (const use of group) if (use.element !== undefined) rewrite.replacements.set(use.element.node, identifier(name, use.element.node));
            declarators.push(declaratorOf(name, identifier(parameter, candidate.site), candidate.site));
            counts.copies++;
        }
    }
    if (toLocal.length > 0) {
        const name = freshName(
            conversion,
            `${variable.name}_0`,
            toLocal.map((use) => use.from),
            `slot ${variable.name}[0]`
        );
        for (const use of toLocal) rewrite.replacements.set(use.member, identifier(name, use.member));
        declarators.unshift(declaratorOf(name, literal.elements[0] as Expression, candidate.site));
        counts.argumentsLocals++;
    }
    return declarators;
};

const convert = (conversion: Conversion, references: ReadonlyMap<Variable, ArgumentsReferences>, scopes: ScopeInfo, counts: Counts): void => {
    const { candidate, rewrite, log } = conversion;
    const declarators = convertArguments(conversion, references, scopes, counts);
    const slots = convertSlots(conversion);
    counts.slots += slots.length;
    pushAll(declarators, slots);
    const { declarator, scope, variable, site } = candidate;
    const removed = rewrite.removed.get(scope) ?? new Set<string>();
    rewrite.removed.set(scope, removed);
    removed.add(variable.name);
    counts.removed++;
    if (candidate.assigned === undefined) {
        rewrite.declarators.set(declarator, declarators);
    } else {
        rewrite.declarators.set(declarator, []);
        rewrite.replacements.set(site, declarators.length === 0 ? REMOVE : at<VariableDeclaration>({ type: "VariableDeclaration", kind: "var", declare: false, declarations: declarators }, site));
    }
    log.debug(`${variable.name}: ${candidate.slots.size} slot(s) to locals, array removed`, site);
};

/**
 * Arguments arrays: `function f(a) { var S = [arguments]; S[3] = g(S[0][0]); return S[3]; }` becomes
 * `function f(a) { var S_3 = g(a); return S_3; }` (#9). Also the assignment form `var S; ... S = [arguments];`.
 *
 * Exact because the array is local and kept to itself: its name is a `var` declared once and written once, by its
 * creation, a statement that runs at most once per call before all code after it in tree order (`siteRefusal`), and
 * which nothing before it can use the array from (`insideHoistedFunction`); its initializer elements run no code; and
 * every use is `S[constant index]`, never called as a method of the array (it would be `this`), deleted, or inside
 * `with`, in a function without direct eval. Its slots then hold only what is written to them, exactly like a `var`
 * per slot: function-scoped and hoisted (reads before the first write see undefined), one binding per invocation
 * shared with closures. Slot 0 starts as the `arguments` the literal names there; while it is the function's own,
 * never reassigned, its uses become parameters, parameter copies or `arguments` where exact (`convertArguments`).
 * Parameters are never added (`length` would change). Names: `freshName`. An anonymous function or class stored in a
 * slot gets the local's name where it had none (model 12).
 *
 * Also folds the inline form `[arguments][0]` to `arguments` (`foldedArguments`), and turns direct reads
 * `arguments[i]` into parameters where exact (`convertDirectReads`).
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
        const argumentsSites = new Map<Node, ArgumentsReferences>();
        const references = new Map<Variable, ArgumentsReferences>();
        const declarations = new Map<Node, Candidate[]>();
        for (const candidate of candidates) {
            if (candidate.refusal !== undefined) continue;
            const own = scopes.references(candidate.variable);
            const names = candidate.scope.variables.filter((variable) => variable.defs.some((def) => def.type === "FunctionName"));
            const nameReferences = names.map((variable) => scopes.references(variable));
            if (own === undefined || nameReferences.includes(undefined)) {
                candidate.refusal = { reason: "a with statement may intercept a use of the array or of a function declared next to it", node: candidate.assigned ?? candidate.declarator };
                continue;
            }
            for (const reference of own) sites.set(reference.identifier as unknown as Node, candidate);
            if (candidate.assigned !== undefined) {
                const declaration = candidate.variable.defs[0]?.parent as unknown as Node;
                declarations.set(declaration, [...(declarations.get(declaration) ?? []), candidate]);
            }
            for (const list of nameReferences) {
                for (const reference of list ?? []) {
                    const id = reference.identifier as unknown as Node;
                    hoisted.set(id, [...(hoisted.get(id) ?? []), candidate]);
                }
            }
        }
        for (const fnScope of scopes.manager.scopes) {
            // A function calling eval (or nesting a call) records no uses (see `convertDirectReads`).
            const args = fnScope.type === "function" && !fnScope.dynamic ? fnScope.set.get("arguments") : undefined;
            const argumentsReferences = args === undefined || args.defs.length > 0 ? undefined : scopes.references(args);
            if (args === undefined || argumentsReferences === undefined || argumentsReferences.length === 0) continue;
            const entry: ArgumentsReferences = { unsafe: [], elementReads: [], indexed: [], applied: [] };
            references.set(args, entry);
            for (const reference of argumentsReferences) argumentsSites.set(reference.identifier as unknown as Node, entry);
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
                const entry = argumentsSites.get(replacement);
                if (entry !== undefined) recordArgumentsUse(entry, path);
            },
            VariableDeclaration(path) {
                // The assignment form drops the bare declarator: its declaration may be left empty, and go.
                for (const candidate of declarations.get(path.node) ?? []) {
                    if (!path.isInStatementList()) candidate.refusal ??= { reason: "the array's bare declaration isn't a statement", node: candidate.declarator };
                }
            },
            Identifier(path) {
                const candidate = sites.get(path.node);
                if (candidate !== undefined) recordUse(candidate, path, scopes);
                for (const early of hoisted.get(path.node) ?? []) {
                    if (!early.declared && !insideHoistedFunction(path, early))
                        early.refusal ??= { reason: `${path.node.name} (it may use the array) is referenced before the array is created`, node: path.node };
                }
                const entry = argumentsSites.get(path.node);
                if (entry !== undefined) recordArgumentsUse(entry, path);
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
        const counts: Counts = { folded, arrays: candidates.length, removed: 0, refused: 0, slots: 0, parameters: 0, copies: 0, argumentsReads: 0, argumentsLocals: 0, directReads: 0 };
        const rewrite: Rewrite = { scopes, replacements: new Map(), declarators: new Map(), added: new Map(), removed: new Map() };
        const owners = new Map(candidates.map((candidate) => [candidate.literal.elements[0] as Node, candidate]));
        for (const candidate of candidates) {
            if (candidate.refusal !== undefined) {
                counts.refused++;
                log.debug(`kept ${candidate.variable.name}: ${candidate.refusal.reason}`, candidate.refusal.node);
                continue;
            }
            convert({ candidate, rewrite, outside: outside(candidate.scope), owners, log }, references, scopes, counts);
        }
        for (const [variable, entry] of references) counts.directReads += convertDirectReads(variable, entry, scopes, rewrite);

        for (const candidate of candidates) {
            const declaration = candidate.variable.defs[0]?.parent as unknown as VariableDeclaration;
            if (candidate.refusal !== undefined || rewrite.replacements.has(declaration)) continue;
            const declarators = declaration.declarations.flatMap((d) => rewrite.declarators.get(d) ?? [d]);
            rewrite.replacements.set(declaration, declarators.length === 0 ? REMOVE : at<VariableDeclaration>({ ...declaration, declarations: declarators }, declaration));
        }
        if (rewrite.replacements.size > 0) {
            traverse(program, {
                enter(path) {
                    const replacement = rewrite.replacements.get(path.node);
                    if (replacement === REMOVE) path.remove();
                    else if (replacement !== undefined) path.replace(replacement);
                },
            });
        }

        log.info(
            `${counts.arrays} arguments array(s): ${counts.removed} removed, ${counts.refused} refused; ${counts.slots} slot(s) to locals, ${counts.parameters} S[0][i] to parameters, ${counts.copies} parameter copies, ${counts.argumentsReads} S[0] to arguments, ${counts.argumentsLocals} S[0] to locals; ${folded} [arguments][0] folded, ${counts.directReads} arguments[i] to parameters`
        );
        // Folds and direct reads only replace expressions; converting arrays adds and removes declarations.
        return { changed: counts.removed + folded + counts.directReads, bindingsChanged: counts.removed > 0, stats: { ...counts } };
    },
};
