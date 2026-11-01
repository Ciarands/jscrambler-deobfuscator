import type { ArrowFunctionExpression, Expression, Function as FunctionNode, MemberExpression, Node } from "./ast.js";
import { isIndexKey, memberKey } from "./ast.js";
import type { EvaluateEnv, Evaluation, Value } from "./evaluate.js";
import { binary, evaluate, FAIL, value } from "./evaluate.js";
import type { PassLog } from "./log.js";
import type { Reference, ScopeInfo, Variable } from "./scope.js";
import { forEachChild } from "./traverse.js";

/** Nodes whose document order the analysis compares (definitions and reads). */
const ORDERED: Record<string, true> = { Identifier: true, MemberExpression: true, VariableDeclarator: true, ExpressionStatement: true };

/** A constant and the node after which (in document order) it holds. */
type Constant = { readonly value: Value; readonly after: Node };

/**
 * Where a binding gets its value: `value` at `definition` (in `statement`), then the `steps` (statements `x = w;` and
 * `x += w;`) after it in the same statement list; the whole holds after `after` (the last of these writes).
 */
interface Definition {
    readonly value: Node;
    readonly definition: Node;
    readonly statement: Node;
    readonly steps: readonly { readonly operator: "=" | "+="; readonly value: Expression }[];
    readonly after: Node;
}

export type FunctionLike = FunctionNode | ArrowFunctionExpression;

/** A function a binding holds for good: from entry (`after` undefined: a declaration), or after `after` in `block`. */
interface FunctionBinding {
    readonly fn: FunctionLike;
    readonly after: Node | undefined;
    readonly block: Node;
}

/** `constantEnv`'s environment, plus what the functions it knows of are. */
export interface ConstantEnv extends EvaluateEnv {
    /**
     * The function a reference (`f` of `f(x)`) holds for good where it is, if any: a function declaration, never
     * written, or a function or arrow expression the binding gets once (like a constant),
     * when the reference comes after that.
     */
    readonly functionAt: (identifier: Node) => FunctionLike | undefined;
    /**
     * Whether code can reach the binding only by its name: always for one inside a function; for a script global,
     * when the program never spells the name as a property or string, has no `with` or direct `eval`, and uses the
     * global object only with keys that evaluate to other names (other scripts don't touch it: semantic model 2).
     */
    readonly onlyByName: (variable: Variable) => boolean;
}

/** A constant array: what each element evaluates to, and the definition (in `block`) after which the array holds. */
interface Table {
    readonly elements: readonly Evaluation[];
    readonly after: Node;
    readonly block: Node;
}

/** A holder (variable or `arguments`-array slot) written once, by a statement directly in `block`, with an array. */
interface Alias {
    readonly table: Variable;
    readonly after: Node;
    readonly block: Node;
}

/** The only write of an `arguments`-array slot, when it is a plain statement `a[k] = value;` directly in the body. */
interface SlotWrite {
    readonly value: Expression;
    readonly statement: Node;
}

/** How an `arguments`-style array (only ever used as `a[index]`) is used, slot by slot. */
interface SlotArray {
    readonly block: Node;
    /** The only write of each slot, `undefined` when it has several, or one that isn't a plain top-level statement. */
    readonly writes: Map<string, SlotWrite | undefined>;
    /** What every write of each slot assigns: `undefined` for initializer elements and writes other than `=`. */
    readonly assigned: Map<string, (Expression | undefined)[]>;
    /** The members reading each slot. */
    readonly reads: Map<string, Node[]>;
}

/** Why a candidate isn't constant, at which node. */
type Refusal = { readonly reason: string; readonly node: Node };

/** What the whole program spells out, for script globals; collected in one walk when a script global is first asked about. */
interface ProgramNames {
    /** Every string literal, template text and static property name: a global so named may be reached as a property. */
    readonly spelled: Set<string>;
    /** Computed members on an expression that is the global object (`window[k]`, top-level `this[k]`). */
    readonly globalMembers: MemberExpression[];
}

/** Unresolved names that hold the global object (or, for `top`/`parent`, may: in a top-level window). */
const GLOBAL_OBJECT_NAMES: Record<string, true> = { globalThis: true, window: true, self: true, frames: true, top: true, parent: true };

/** Nodes whose code gets its own `this`: functions (not arrows), class fields and static blocks. */
const BINDS_THIS: Record<string, true> = { FunctionDeclaration: true, FunctionExpression: true, PropertyDefinition: true, AccessorProperty: true, StaticBlock: true };

const functionBody = (block: Node): readonly Node[] | undefined =>
    block.type === "Program"
        ? block.body
        : (block.type === "FunctionDeclaration" || block.type === "FunctionExpression" || block.type === "ArrowFunctionExpression") && block.body !== null && block.body.type === "BlockStatement"
          ? block.body.body
          : undefined;

/** The name a node spells out as a string or a static property key, if any. */
const spelledName = (node: Node): string | undefined => {
    switch (node.type) {
        case "Literal":
            return typeof node.value === "string" ? node.value : undefined;
        case "TemplateElement":
            return node.value.cooked ?? undefined;
        case "MemberExpression":
            return !node.computed && node.property.type === "Identifier" ? node.property.name : undefined;
        case "Property":
        case "MethodDefinition":
        case "PropertyDefinition":
        case "AccessorProperty":
            return !node.computed && node.key.type === "Identifier" ? node.key.name : undefined;
        default:
            return undefined;
    }
};

/**
 * Whether `member` (its parent `above`, and `above`'s parent `outer`) is written: assigned (also by `+=`, `++`,
 * `delete`), or a destructuring or for-in/of target.
 */
const isWritten = (member: Node, above: Node | undefined, outer: Node | undefined): boolean => {
    switch (above?.type) {
        case "AssignmentExpression":
        case "AssignmentPattern":
            return above.left === member;
        case "UpdateExpression":
        case "ArrayPattern":
        case "RestElement":
            return true;
        case "UnaryExpression":
            return above.operator === "delete";
        case "Property":
            return above.value === member && outer?.type === "ObjectPattern";
        case "ForInStatement":
        case "ForOfStatement":
            return above.left === member;
        default:
            return false;
    }
};

/** A static index key of a member (`a[3]`, never `a.x` or `a[k]`), as a string. */
const literalIndex = (member: MemberExpression): string | undefined => {
    const key = memberKey(member);
    return key === undefined || !isIndexKey(String(key)) || (member.computed && member.property.type !== "Literal") ? undefined : String(key);
};

/**
 * How the value of `member` (its parent `above`) may reach code that changes it, or `undefined` when it is only
 * converted or tested: a computed key, an operand of a unary (not `delete`) or binary operator (not `instanceof`,
 * which calls a method of its right operand), a test, or a discarded statement value.
 */
const escapingUse = (member: Node, above: Node | undefined): string | undefined => {
    switch (above?.type) {
        case "MemberExpression":
            return above.computed && above.property === member ? undefined : "is used as an object";
        case "UnaryExpression":
            return above.operator === "delete" ? "is deleted" : undefined;
        case "BinaryExpression":
            return above.operator === "instanceof" ? "is an instanceof operand" : undefined;
        case "IfStatement":
        case "WhileStatement":
        case "DoWhileStatement":
        case "ForStatement":
        case "ConditionalExpression":
            return "test" in above && above.test === member ? undefined : `flows out of a ${above.type}`;
        case "ExpressionStatement":
            return undefined;
        default:
            return `flows into a ${above?.type ?? "program"}`;
    }
};

/**
 * An evaluation environment that sees through constant bindings, constant `arguments`-array slots and constant arrays:
 *
 * - `var n = 1259;` makes later reads of `n` evaluate to 1259;
 * - `var s = "ab"; s += "cd";` makes reads of `s` after the append evaluate to "abcd";
 * - `var a = [arguments]; a[5] = "x";` makes later reads of `a[5]` evaluate to "x" (#13);
 * - `T = [(f(), "get"), "set"]; a[4] = T;` makes later reads of `a[4][1]` (and `T[1]`) evaluate to "set".
 *
 * A binding is constant when its only definition is a declarator whose initializer evaluates (or `var x;` and one
 * statement `x = v;`), it is never written again but by statements `x += w;` (with `w` constant) after it in the same
 * statement list, and the definition is a statement directly in its function (or program) body, so it runs exactly
 * once on entry (or in a nested list, for reads inside it). A slot is constant when its array is only ever used as
 * `a[constant]`, and the slot is written exactly once, by such a top-level statement, with a constant. Reads get the
 * value only when they come after the last write in execution order (`reachesAfter`).
 *
 * A constant array is a binding written exactly once, with an array literal, by a declarator or a plain assignment
 * statement directly in its body; its elements are what they evaluate to (a sequence: its last expression; the
 * others still run where the array is built), holes are `undefined`. Nothing may change its elements or length, so
 * every reference must be one of: a read `T[k]` (not written, not called: a method would get `T` as `this`) whose key
 * evaluates to an index or "length", or whose value is only converted or tested (`o[T[k]]`, `T[k] === x`,
 * `if (T[k])`: any other key may select an inherited getter returning `T` itself, and operators only read it,
 * semantic model 4), or a copy into a holder (a local variable, or an `arguments`-array slot) every read of which is
 * such a read. A holder written exactly once with the array (an alias) reads it: `a[4][k]` is element k when the read
 * comes after the copy and the copy after the array's definition. The keys a check evaluates may read the array
 * itself; they are evaluated assuming it unchanged, which is sound by induction over time: the first operation that
 * changed it would have to be one of these checked uses, none of which, with the array unchanged until then, changes
 * it or lets its value reach code that could. While assuming, a slot every write of which copies the array reads as
 * the array too (before the first copy it is `undefined`, and reading a key of it throws before any access).
 *
 * Script globals (`var` at the top of a script) are also properties of the global object, so they are refused when
 * code could reach one as a property: the program spells its name (`window.T`, `G[k].T`, `"T"`), uses `with` or a
 * direct `eval`, or reads or writes the global object (`globalThis`, `window`, `self`, top-level `this`...) with a key
 * that doesn't evaluate, or evaluates to the name. Other scripts don't touch them (semantic model 2).
 */
export const constantEnv = (scopes: ScopeInfo, log?: PassLog): ConstantEnv => {
    const cached = envs.get(scopes);
    if (cached !== undefined && cached.generation === scopes.generation) {
        cached.logRef.log = log;
        return cached.env;
    }
    const logRef: { log: PassLog | undefined } = { log };
    const env = buildConstantEnv(scopes, logRef);
    envs.set(scopes, { generation: scopes.generation, env, logRef });
    return env;
};

/**
 * One environment per scope analysis and generation: passes that run on a program nothing changed since share it,
 * with what it worked out (the analysis is refreshed, starting a generation, whenever a pass changed the program).
 * The log follows the pass asking.
 */
const envs = new WeakMap<ScopeInfo, { readonly generation: number; readonly env: ConstantEnv; readonly logRef: { log: PassLog | undefined } }>();

const buildConstantEnv = (scopes: ScopeInfo, logRef: { readonly log: PassLog | undefined }): ConstantEnv => {
    /** Each node's children in document order, by position: built per parent when an order question reaches it. */
    const childPositions = new Map<Node, Map<Node, number>>();
    const constants = new Map<Variable, Constant | undefined>();
    const functionBindings = new Map<Variable, FunctionBinding | undefined>();
    const slotArrays = new Map<Variable, SlotArray | undefined>();
    const slotValues = new Map<Node, Constant | undefined>();
    const tables = new Map<Variable, Table | undefined>();
    const aliases = new Map<Variable, Alias | undefined>();
    /** Keys being computed, per cache (one key may be in several: a variable is a constant and a table candidate). */
    const pending = new Map<object, Set<unknown>>();
    /** The array whose uses are being checked, read as unchanged by the keys the check evaluates (see above). */
    let validating: { readonly variable: Variable; readonly table: Table } | undefined;

    const program = scopes.manager.globalScope?.block as unknown as Node | undefined;
    const dynamic = scopes.manager.scopes.find((scope) => scope.type === "with" || scope.directCallToEvalScope);
    const hasWith = scopes.manager.scopes.some((scope) => scope.type === "with");

    /** Statements directly in a block's body (they run once per entry), by block. */
    const topLevels = new Map<Node, ReadonlySet<Node>>();
    const isTopLevel = (block: Node, statement: Node | undefined): boolean => {
        if (statement === undefined) return false;
        let set = topLevels.get(block);
        if (set === undefined) {
            set = new Set(functionBody(block) ?? []);
            topLevels.set(block, set);
        }
        return set.has(statement);
    };
    /** `node`'s ancestors from its parent up to the program (empty for nodes the analysis doesn't know). */
    const ancestorsOf = (node: Node): Node[] => {
        const chain: Node[] = [];
        for (let above = scopes.parentOf(node); above !== undefined; above = scopes.parentOf(above)) chain.push(above);
        return chain;
    };
    /** Whether `node` lies strictly inside `ancestor`. */
    const isWithin = (ancestor: Node, node: Node): boolean => {
        for (let above = scopes.parentOf(node); above !== undefined; above = scopes.parentOf(above)) if (above === ancestor) return true;
        return false;
    };
    const positionOf = (parent: Node, child: Node): number => {
        let positions = childPositions.get(parent);
        if (positions === undefined) {
            const found = new Map<Node, number>();
            forEachChild(parent, (node) => void found.set(node, found.size));
            positions = found;
            childPositions.set(parent, positions);
        }
        return positions.get(child) ?? -1;
    };
    /**
     * Whether `a` comes before `b` in document order (a depth-first walk in source order, the tree as it now is:
     * after unflattening, that is execution order). An ancestor comes before what it contains.
     */
    const precedes = (a: Node, b: Node): boolean => {
        if (a === b) return false;
        const above = ancestorsOf(a);
        const aChain = [a, ...above];
        const index = new Map(aChain.map((node, i) => [node, i]));
        let child = b;
        for (let parent = scopes.parentOf(b); parent !== undefined; child = parent, parent = scopes.parentOf(parent)) {
            if (parent === a) return true;
            const at = index.get(parent);
            if (at !== undefined) return at > 0 && positionOf(parent, aChain[at - 1] as Node) < positionOf(parent, child);
        }
        // `b` contains `a`, or they share no ancestor the analysis knows.
        return false;
    };
    /** The nearest function declaration around `use` inside `block`: hoisted, so callable before what precedes it. */
    const declarationAround = (block: Node, use: Node): Node | undefined => {
        for (let above = scopes.parentOf(use); above !== undefined && above !== block; above = scopes.parentOf(above)) if (above.type === "FunctionDeclaration") return above;
        return undefined;
    };

    /** Whether `node` is the global object: `this` where it is (`thisIsGlobal`), or an unresolved global name for it. */
    const isGlobalObject = (node: Node, thisIsGlobal: boolean): boolean =>
        node.type === "ThisExpression"
            ? thisIsGlobal
            : node.type === "Identifier" && GLOBAL_OBJECT_NAMES[node.name] === true && scopes.referenceOf(node) !== undefined && scopes.staticVariableOf(node) === undefined;

    /** Spelled names and global-object members of the whole program, from one walk when first needed. */
    let programNames: ProgramNames | undefined;
    const namesOf = (): ProgramNames => {
        if (programNames !== undefined) return programNames;
        const names: ProgramNames = { spelled: new Set(), globalMembers: [] };
        if (program === undefined) return (programNames = names);
        // One callback for the whole walk (no closure per node): `thisIsGlobal` describes the node whose children are
        // being visited (a script's top-level code, no function around it binding its own `this`).
        let thisIsGlobal = program.type === "Program" && program.sourceType === "script";
        const visit = (child: Node): void => {
            const name = spelledName(child);
            if (name !== undefined) names.spelled.add(name);
            if (child.type === "MemberExpression" && child.computed && isGlobalObject(child.object, thisIsGlobal)) names.globalMembers.push(child);
            const outerThis = thisIsGlobal;
            thisIsGlobal = outerThis && BINDS_THIS[child.type] !== true;
            forEachChild(child, visit);
            thisIsGlobal = outerThis;
        };
        forEachChild(program, visit);
        return (programNames = names);
    };
    /** A node's parent; none for the name of `o.name`, which is no reference. */
    const parentOf = (node: Node): Node | undefined => {
        const above = scopes.parentOf(node);
        return above?.type === "MemberExpression" && !above.computed && above.property === node ? undefined : above;
    };

    /**
     * Verdicts of `runsAfter`, per definition: proven ones only (see there). A `false` is always final: assumptions
     * only ever make a check succeed.
     */
    const verdicts = new Map<Node, Map<Node, boolean>>();
    /** Per definition, the declarations `runsAfter` is checking for it. */
    const checking = new Map<Node, Set<Node>>();
    /** How many checks are running, and the declarations they found to run after (proven once all are done). */
    let depth = 0;
    let reached: { readonly known: Map<Node, boolean>; readonly declaration: Node }[] = [];

    /**
     * For a constant declared inside a nested statement list rather than directly in its body: that list. Control
     * enters a statement list only at its start (no jump lands inside one), so a use after the declaration and still
     * inside the list runs after it in the same pass through the list.
     */
    const limits = new Map<Node, Node>();

    /**
     * `use` runs after `definition`: it comes later in `block`'s document order (within the definition's statement
     * list, see `limits`) and, when it sits in a function declaration (hoisted), that function only runs after
     * `definition` too (`runsAfter`). A use in a function declaration runs when the function is called, wherever it
     * is declared: then only the calls count (a helper declared before the slot it reads is set). A definition inside
     * a declaration is in a nested list, whose `limits` its calls from outside don't meet.
     */
    const reachesAfter = (block: Node, definition: Node, use: Node): boolean => {
        if (ORDERED[definition.type] !== true || ORDERED[use.type] !== true || !isWithin(block, definition) || !isWithin(block, use)) return false;
        const declaration = declarationAround(block, use);
        if (declaration !== undefined) return runsAfter(block, definition, declaration);
        const limit = limits.get(definition);
        return precedes(definition, use) && (limit === undefined || isWithin(limit, use));
    };

    /**
     * The body of the function `declaration` (in `block`) only runs after `definition`: every reference to it does
     * (`reachesAfter`). Checked coinductively: a declaration already being checked (recursion, mutual recursion) is
     * assumed to run after. Proof: let C be the declarations a successful outermost check went through. Each of their
     * references either comes after `definition` outside any declaration, or sits in a member of C. A function's
     * object is only reached by evaluating its name (it is created when its scope is entered and only escapes through
     * a reference; `arguments.callee` and `f.caller` need it running already), so if a member of C ran before
     * `definition`, take the earliest evaluation of a reference to a member of C before `definition`: it can't be
     * outside the declarations (it would come after), so it is inside a member of C, which was then running before
     * `definition`, so a reference to that member was evaluated even earlier: a contradiction. Verdicts reached under
     * an assumption are only kept once the outermost check succeeds (they are then all proven); a failure is kept
     * right away.
     */
    const runsAfter = (block: Node, definition: Node, declaration: Node): boolean => {
        let known = verdicts.get(definition);
        let stack = checking.get(definition);
        if (known === undefined || stack === undefined) {
            known = new Map();
            stack = new Set();
            verdicts.set(definition, known);
            checking.set(definition, stack);
        }
        const verdict = known.get(declaration);
        if (verdict !== undefined) return verdict;
        if (stack.has(declaration)) return true;
        const fn = declaration.type === "FunctionDeclaration" && declaration.id !== null ? scopes.variableOf(declaration.id) : undefined;
        if (fn === undefined || globalSafe(fn) !== true) {
            known.set(declaration, false);
            return false;
        }
        const outermost = stack.size === 0;
        const mark = reached.length;
        stack.add(declaration);
        depth++;
        reached.push({ known, declaration });
        const safe = scopes.staticReferences(fn).every((reference) => reachesAfter(block, definition, reference.identifier as unknown as Node));
        stack.delete(declaration);
        depth--;
        if (!safe) known.set(declaration, false);
        // A failed outermost check for this definition proves none of what it assumed.
        if (outermost && !safe) reached.length = mark;
        if (depth === 0) {
            for (const proven of reached) proven.known.set(proven.declaration, true);
            reached = [];
        }
        return safe;
    };

    /**
     * `compute` once per key; `undefined` while it runs (`var a = b, b = a`). Never under another array's assumption,
     * and a success found while `runsAfter` assumes something isn't kept (it is recomputed when needed again).
     */
    const memo = <K, V>(cache: Map<K, V | undefined>, key: K, compute: () => V | undefined): V | undefined => {
        if (cache.has(key)) return cache.get(key);
        let running = pending.get(cache);
        if (running === undefined) {
            running = new Set();
            pending.set(cache, running);
        }
        if (running.has(key)) return undefined;
        running.add(key);
        const saved = validating;
        validating = undefined;
        try {
            const result = compute();
            if (depth === 0 || result === undefined || result === false) cache.set(key, result);
            return result;
        } finally {
            validating = saved;
            running.delete(key);
        }
    };

    /**
     * Why code could reach the script global `variable` as a property of the global object (see `constantEnv`); none
     * for any other binding. Keys are evaluated as the current check sees them. Only the first reason unless `all`.
     */
    const globalRefusals = (variable: Variable, all: boolean): Refusal[] => {
        if (variable.scope.type !== "global") return [];
        const node = variable.identifiers[0] as unknown as Node;
        if (dynamic !== undefined) return [{ reason: "the program uses with or direct eval", node: dynamic.block as unknown as Node }];
        const names = namesOf();
        if (names.spelled.has(variable.name)) return [{ reason: `the program spells ${variable.name} as a property or a string`, node }];
        const refusals: Refusal[] = [];
        for (const member of names.globalMembers) {
            const key = evaluate(member.property, env);
            if (key.ok) {
                if (String(key.value) === variable.name) refusals.push({ reason: `the global object is used with the key ${variable.name}`, node: member });
            } else if (!keyOfTable(member.property, variable.name)) {
                refusals.push({ reason: "the global object is used with an unknown key", node: member });
            }
            if (refusals.length > 0 && !all) break;
        }
        return refusals;
    };

    /**
     * Whether `key` reads a constant array (`T[k]`, through an alias too) none of whose elements is `name`, whatever
     * `k` is: an element, `undefined` past the end, or an inherited value (a function, `length`'s number, the
     * prototype's empty join), none of which spells an identifier but `undefined`. Before the array is there the
     * holder is `undefined`, and the read throws before any access.
     */
    const keyOfTable = (key: Node, name: string): boolean => {
        if (key.type !== "MemberExpression" || !key.computed || name === "undefined") return false;
        const holder = holderOf(key.object);
        const assumed = validating !== undefined && (holder?.table === validating.variable || holdsOnly(key.object, validating.variable));
        const table = assumed ? validating?.table : holder === undefined ? undefined : tableOf(holder.table);
        return table !== undefined && table.elements.every((element) => element.ok && String(element.value) !== name);
    };
    const globalChecks = new Map<Variable, boolean | undefined>();
    const globalSafe = (variable: Variable): boolean | undefined =>
        memo(globalChecks, variable, () => {
            const [refusal] = globalRefusals(variable, false);
            if (refusal !== undefined) logRef.log?.debug(`${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            return refusal === undefined;
        });

    /** The statement `x OP v;` a write reference (to `x`) is the target of, if it is one. */
    const assigningStatement = (write: Reference, operator: string): Node | undefined => {
        const id = write.identifier as unknown as Node;
        const assignment = parentOf(id);
        const statement = assignment === undefined ? undefined : parentOf(assignment);
        return assignment?.type === "AssignmentExpression" && assignment.operator === operator && assignment.left === id && statement?.type === "ExpressionStatement" ? statement : undefined;
    };

    /**
     * A binding's value and where it gets it: `var x = v;` (the declarator), or `var x;` written once, by a statement
     * `x = v;` (that statement). Or a binding written several times, all by its declarators (`var x = ""; var x =
     * "ab";` declares one binding) and statements `x = w;` and `x += w;` in one statement list (a string built in
     * pieces: `var s = "ab"; s += "cd";`), the first of them in document order an initializer or an `=`: reads after the
     * last write (`after`) see what they compute in order; reads before it aren't answered. The list runs its
     * statements in order and is only entered at its start, so a pass through it that reaches `after` ran each write
     * once, in order, from the first.
     */
    const findDefinition = (variable: Variable): Definition | undefined => {
        const [def] = variable.defs;
        if (def === undefined || (variable.defs.length > 1 && !variable.defs.every((other) => other.type === "Variable" && (other.parent as { kind?: string } | null)?.kind === "var")))
            return undefined;
        if (def.type !== "Variable") return undefined;
        const declarator = def.node as unknown as Node;
        const declaration = def.parent as unknown as Node | null;
        if (declarator.type !== "VariableDeclarator" || declarator.id.type !== "Identifier" || declaration?.type !== "VariableDeclaration") return undefined;
        /** The writes as statements (a declarator's in its declaration), with what each assigns. */
        const writes: { operator: "=" | "+="; value: Expression; definition: Node; statement: Node }[] = [];
        for (const write of scopes.staticReferences(variable)) {
            if (!write.isWrite()) continue;
            const initialized = write.init === true ? parentOf(write.identifier as unknown as Node) : undefined;
            if (initialized?.type === "VariableDeclarator" && initialized.init !== null) {
                writes.push({ operator: "=", value: initialized.init, definition: initialized, statement: parentOf(initialized) as Node });
                continue;
            }
            const operator = assigningStatement(write, "=") !== undefined ? "=" : assigningStatement(write, "+=") !== undefined ? "+=" : undefined;
            const statement = operator === undefined ? undefined : parentOf(parentOf(write.identifier as unknown as Node) as Node);
            if (operator === undefined || statement?.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") return undefined;
            writes.push({ operator, value: statement.expression.right, definition: statement, statement });
        }
        const [only] = writes;
        if (writes.length === 1 && only?.operator === "=") {
            // `var x; x = v;`: a `let` would be in its dead zone before the declaration, a `const` can't be assigned.
            if (only.definition !== declarator && declaration.kind !== "var") return undefined;
            return { value: only.value, definition: only.definition, statement: only.statement, steps: [], after: only.definition };
        }
        // (A `const` throws at its second write: nothing after that write runs.)
        if (writes.length < 2) return undefined;
        const list = parentOf(only?.statement as Node);
        if (writes.some((write) => parentOf(write.statement) !== list)) return undefined;
        writes.sort((a, b) => (precedes(a.definition, b.definition) ? -1 : 1));
        const [first, ...steps] = writes;
        const last = steps.at(-1);
        if (first === undefined || first.operator !== "=" || last === undefined) return undefined;
        return { value: first.value, definition: first.definition, statement: first.statement, steps, after: last.definition };
    };

    const definitions = new Map<Variable, Definition | undefined>();
    /** `findDefinition`, once per binding (constants and tables both ask). */
    const builtDefinition = (variable: Variable): Definition | undefined => {
        if (definitions.has(variable)) return definitions.get(variable);
        const found = findDefinition(variable);
        definitions.set(variable, found);
        return found;
    };

    /** A binding's one value (see `builtDefinition`), when it is written once. */
    const singleDefinition = (variable: Variable): Definition | undefined => {
        const built = builtDefinition(variable);
        return built?.steps.length === 0 ? built : undefined;
    };

    /**
     * Whether a definition's statement runs once per pass through its list: directly in the body, or in a nested
     * statement list, where reads count only inside that list, after the definition (`limits`).
     */
    const placed = (block: Node, statement: Node, definition: Node): boolean => {
        if (isTopLevel(block, statement)) return true;
        const list = parentOf(statement);
        const listed = list?.type === "SwitchCase" ? list.consequent : list?.type === "BlockStatement" || list?.type === "StaticBlock" ? list.body : [];
        if (list === undefined || !isWithin(block, list) || !(listed as readonly Node[]).includes(statement)) return false;
        limits.set(definition, list);
        return true;
    };

    const constantOf = (variable: Variable): Constant | undefined =>
        memo(constants, variable, () => {
            // A read of the binding that evaluating its value needs makes the value fail to evaluate.
            const built = builtDefinition(variable);
            if (built === undefined || !placed(variable.scope.block as unknown as Node, built.statement, built.after)) return undefined;
            // `x = w` gives `w`, whatever `x` held; `x += w` reads `x`, then evaluates `w`, then adds: on primitives,
            // what `binary` computes.
            let result = evaluate(built.value, env);
            for (const step of built.steps) {
                if (step.operator === "=") {
                    result = evaluate(step.value, env);
                    continue;
                }
                if (!result.ok) continue;
                const appended = evaluate(step.value, env);
                result = appended.ok ? binary("+", result.value, appended.value) : FAIL;
            }
            if (!result.ok || globalSafe(variable) !== true) return undefined;
            if (built.steps.length > 0) logRef.log?.debug(`${variable.name} is written ${built.steps.length + 1} times in one statement list: constant after the last`, built.after);
            return { value: result.value, after: built.after };
        });

    /**
     * The function a binding holds for good, and from where on: a function declaration, never written (from its
     * scope's entry: a block's for one in a block, which only references inside the block resolve to), or a function
     * or arrow expression it gets once, as constants do (after the definition).
     */
    const functionBindingOf = (variable: Variable): FunctionBinding | undefined =>
        memo(functionBindings, variable, () => {
            const block = variable.scope.block as unknown as Node;
            const [def] = variable.defs;
            if (variable.defs.length === 1 && def?.type === "FunctionName") {
                const declaration = def.node as unknown as Node;
                if (declaration.type !== "FunctionDeclaration") return undefined;
                if (scopes.staticReferences(variable).some((reference) => reference.isWrite()) || globalSafe(variable) !== true) return undefined;
                return { fn: declaration, after: undefined, block };
            }
            const single = singleDefinition(variable);
            const fn = single?.value;
            if (single === undefined || (fn?.type !== "FunctionExpression" && fn?.type !== "ArrowFunctionExpression")) return undefined;
            if (!placed(block, single.statement, single.definition) || globalSafe(variable) !== true) return undefined;
            return { fn, after: single.definition, block };
        });

    const functionAt = (identifier: Node): FunctionLike | undefined => {
        const variable = identifier.type === "Identifier" ? scopes.variableOf(identifier) : undefined;
        const binding = variable === undefined ? undefined : functionBindingOf(variable);
        if (binding === undefined) return undefined;
        return binding.after === undefined || reachesAfter(binding.block, binding.after, identifier) ? binding.fn : undefined;
    };

    /** The slots of an `arguments`-style array, or `undefined` when the array is used any other way. */
    const slotArrayOf = (variable: Variable): SlotArray | undefined =>
        memo(slotArrays, variable, () => {
            const [def] = variable.defs;
            if (variable.defs.length !== 1 || def === undefined || def.type !== "Variable") return undefined;
            const declarator = def.node as unknown as Node;
            if (declarator.type !== "VariableDeclarator" || declarator.init?.type !== "ArrayExpression") return undefined;
            const references = scopes.staticReferences(variable);
            if (references.filter((reference) => reference.isWrite()).length !== 1 || globalSafe(variable) !== true) return undefined;
            const block = variable.scope.block as unknown as Node;

            const writes = new Map<string, (SlotWrite | undefined)[]>();
            const assigned = new Map<string, (Expression | undefined)[]>();
            const reads = new Map<string, Node[]>();
            // Initializer elements are set on entry: a write, never a constant here (`[arguments]`).
            for (let index = 0; index < declarator.init.elements.length; index++) {
                writes.set(String(index), [undefined]);
                assigned.set(String(index), [undefined]);
            }
            for (const reference of references) {
                const id = reference.identifier as unknown as Node;
                if (reference.init) continue;
                // Only ever `a[index]`: a method (`a.splice(...)`), `a.length` or a computed key could move slots.
                const member = parentOf(id);
                if (member?.type !== "MemberExpression" || member.object !== id) return undefined;
                const key = literalIndex(member);
                if (key === undefined) return undefined;
                const above = parentOf(member);
                const outer = above === undefined ? undefined : parentOf(above);
                if (!isWritten(member, above, outer)) {
                    const list = reads.get(key);
                    if (list === undefined) reads.set(key, [member]);
                    else list.push(member);
                    continue;
                }
                const right = above?.type === "AssignmentExpression" && above.operator === "=" ? above.right : undefined;
                const plain = right !== undefined && outer?.type === "ExpressionStatement" && isTopLevel(block, outer);
                const list = writes.get(key) ?? [];
                list.push(plain ? { value: right, statement: outer } : undefined);
                writes.set(key, list);
                const values = assigned.get(key) ?? [];
                values.push(right);
                assigned.set(key, values);
            }
            const only = new Map<string, SlotWrite | undefined>();
            for (const [key, list] of writes) only.set(key, list.length === 1 ? list[0] : undefined);
            return { block, writes: only, assigned, reads };
        });

    /** The single write of slot `key` of the array `object` names, if `object` names a slot array. */
    const slotWriteOf = (object: Node, key: string): { array: SlotArray; write: SlotWrite | undefined } | undefined => {
        const variable = object.type === "Identifier" ? scopes.staticVariableOf(object) : undefined;
        const array = variable === undefined ? undefined : slotArrayOf(variable);
        return array === undefined ? undefined : { array, write: array.writes.get(key) };
    };

    const slotConstant = (write: SlotWrite): Constant | undefined =>
        memo(slotValues, write.statement, () => {
            const result = evaluate(write.value, env);
            return result.ok ? { value: result.value, after: write.statement } : undefined;
        });

    /** An array literal assigned to `variable` exactly once, directly in its body: the array and the assigning node. */
    const arrayDefinition = (variable: Variable): { array: Node; after: Node; id: Node } | undefined => {
        const [def] = variable.defs;
        if (variable.defs.length !== 1 || def === undefined || def.type !== "Variable") return undefined;
        const declarator = def.node as unknown as Node;
        if (declarator.type !== "VariableDeclarator" || declarator.id.type !== "Identifier") return undefined;
        const writes = scopes.staticReferences(variable).filter((reference) => reference.isWrite());
        const [write] = writes;
        if (writes.length !== 1 || write === undefined) return undefined;
        const block = variable.scope.block as unknown as Node;
        if (declarator.init !== null) {
            const declaration = def.parent as unknown as Node | null;
            if (declarator.init.type !== "ArrayExpression" || declaration === null || !isTopLevel(block, declaration)) return undefined;
            return { array: declarator.init, after: declarator, id: declarator.id };
        }
        const id = write.identifier as unknown as Node;
        const assignment = parentOf(id);
        if (assignment?.type !== "AssignmentExpression" || assignment.operator !== "=" || assignment.left !== id || assignment.right.type !== "ArrayExpression") return undefined;
        const statement = parentOf(assignment);
        if (statement?.type !== "ExpressionStatement" || !isTopLevel(block, statement)) return undefined;
        return { array: assignment.right, after: statement, id };
    };

    /** What each element of an array literal evaluates to; `undefined` when it spreads (its length is unknown). */
    const elementsOf = (array: Node): Evaluation[] | undefined => {
        if (array.type !== "ArrayExpression") return undefined;
        const elements: Evaluation[] = [];
        for (const element of array.elements) {
            // A hole reads `Array.prototype[i]`, which isn't there: relies on model 7: builtins intact.
            if (element === null) elements.push(value(undefined));
            else if (element.type === "SpreadElement") return undefined;
            else elements.push(evaluate(element.type === "SequenceExpression" ? (element.expressions.at(-1) as Expression) : element, env));
        }
        return elements;
    };

    /** A read `T[k]` (`member`, its object a reference to the array or a holder) that leaves the array as it is. */
    const checkRead = (member: Node): Refusal | undefined => {
        if (member.type !== "MemberExpression") return { reason: "used other than as an element read", node: member };
        const above = parentOf(member);
        const outer = above === undefined ? undefined : parentOf(above);
        if (isWritten(member, above, outer)) return { reason: "an element or its length is written", node: member };
        // A method would get the array as `this`.
        if ((above?.type === "CallExpression" && above.callee === member) || (above?.type === "TaggedTemplateExpression" && above.tag === member))
            return { reason: "a method is called on it", node: member };
        const key = member.computed ? evaluate(member.property, env) : value(member.property.name);
        if (key.ok && (String(key.value) === "length" || isIndexKey(String(key.value)))) return undefined;
        // Another key may select an inherited getter returning the array itself: harmless only where the value is
        // just converted or tested (operators only read, semantic model 4; converting an array runs
        // `Array.prototype.toString`/`join`, which only read: relies on model 7: builtins intact).
        const use = escapingUse(member, above);
        return use === undefined ? undefined : { reason: `read with a key that isn't a known index, its value ${use}`, node: member };
    };

    /** Every read of the holder variable `variable` is a `checkRead` read. */
    const checkHolder = (variable: Variable): Refusal | undefined => {
        for (const reference of scopes.staticReferences(variable)) {
            if (!reference.isRead()) continue;
            const id = reference.identifier as unknown as Node;
            const member = parentOf(id);
            const refusal = member?.type === "MemberExpression" && member.object === id ? checkRead(member) : { reason: "a copy is used other than as an element read", node: id };
            if (refusal !== undefined) return refusal;
        }
        return undefined;
    };

    /** Every one of `reads` (members reading a holder slot) is the object of a `checkRead` read. */
    const checkSlotReads = (reads: readonly Node[]): Refusal | undefined => {
        for (const read of reads) {
            const member = parentOf(read);
            const refusal = member?.type === "MemberExpression" && member.object === read ? checkRead(member) : { reason: "a copy is used other than as an element read", node: read };
            if (refusal !== undefined) return refusal;
        }
        return undefined;
    };

    /**
     * A use of the array (`id`, a reference other than its definition): an element read, or a copy into a holder
     * (`var A = T`, `A = T`, `a[4] = T`) whose reads are element reads. `checked`: holders already checked.
     */
    const checkUse = (id: Node, checked: Set<unknown>): Refusal | undefined => {
        const above = parentOf(id);
        if (above?.type === "MemberExpression" && above.object === id) return checkRead(above);
        // The copy's own value must go nowhere else: `var A = T`, or `A = T;` as a statement.
        const target =
            above?.type === "VariableDeclarator" && above.init === id
                ? above.id
                : above?.type === "AssignmentExpression" && above.operator === "=" && above.right === id && parentOf(above)?.type === "ExpressionStatement"
                  ? above.left
                  : undefined;
        if (target?.type === "Identifier") {
            const variable = scopes.staticVariableOf(target);
            if (variable === undefined || variable.scope.type === "global") return { reason: "copied into a global", node: id };
            // A sloppy function's `arguments` object aliases its parameters.
            if (variable.defs.some((def) => def.type === "Parameter")) return { reason: "copied into a parameter", node: id };
            if (checked.has(variable)) return undefined;
            checked.add(variable);
            return checkHolder(variable);
        }
        const key = target?.type === "MemberExpression" ? literalIndex(target) : undefined;
        if (target?.type === "MemberExpression" && key !== undefined) {
            const slot = slotWriteOf(target.object, key);
            if (slot === undefined) return { reason: "copied into an array used other than as slots", node: id };
            const reads = slot.array.reads.get(key) ?? [];
            if (checked.has(reads)) return undefined;
            checked.add(reads);
            return checkSlotReads(reads);
        }
        return { reason: "the array escapes (passed, returned, stored or iterated)", node: id };
    };

    /**
     * Why the array `variable` holds (defined by `id`) could change, checked with `table` assumed (see above): the
     * first reason, or every one when the log shows them.
     */
    const tableRefusals = (variable: Variable, id: Node, table: Table): Refusal[] => {
        if (hasWith) return [{ reason: "the program uses with", node: id }];
        const all = logRef.log?.debugging === true;
        const saved = validating;
        validating = { variable, table };
        try {
            const refusals = globalRefusals(variable, all);
            const holders = new Set<unknown>();
            for (const reference of scopes.staticReferences(variable)) {
                if (refusals.length > 0 && !all) break;
                const use = reference.identifier as unknown as Node;
                const refusal = use === id ? undefined : checkUse(use, holders);
                if (refusal !== undefined) refusals.push(refusal);
            }
            return refusals;
        } finally {
            validating = saved;
        }
    };

    const tableOf = (variable: Variable): Table | undefined =>
        memo(tables, variable, () => {
            const definition = arrayDefinition(variable);
            const elements = definition === undefined ? undefined : elementsOf(definition.array);
            // `[arguments]`: no element to resolve, nothing worth checking.
            if (definition === undefined || elements === undefined || !elements.some((element) => element.ok)) return undefined;
            const table: Table = { elements, after: definition.after, block: variable.scope.block as unknown as Node };
            const refusals = tableRefusals(variable, definition.id, table);
            for (const refusal of refusals) logRef.log?.debug(`array ${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            if (refusals.length > 0) return undefined;
            logRef.log?.debug(`array ${variable.name} is constant (${elements.length} elements)`, definition.after);
            return table;
        });

    /** `var A = T;` (or `var A;` and one later `A = T;`): an alias of the array `T` may name, for reads after it. */
    const aliasOf = (variable: Variable): Alias | undefined =>
        memo(aliases, variable, () => {
            const single = singleDefinition(variable);
            const block = variable.scope.block as unknown as Node;
            if (single?.value.type !== "Identifier" || !placed(block, single.statement, single.definition)) return undefined;
            const table = scopes.staticVariableOf(single.value);
            return table === undefined ? undefined : { table, after: single.definition, block };
        });

    /** The array an expression (`T`, an alias `A`, a slot alias `a[4]`) may hold, and the alias, if it is one. */
    const holderOf = (object: Node): { table: Variable; alias: Alias | undefined } | undefined => {
        if (object.type === "Identifier") {
            const variable = scopes.staticVariableOf(object);
            if (variable === undefined) return undefined;
            const alias = aliasOf(variable);
            return alias === undefined ? { table: variable, alias } : { table: alias.table, alias };
        }
        const key = object.type === "MemberExpression" ? literalIndex(object) : undefined;
        if (object.type !== "MemberExpression" || key === undefined) return undefined;
        const slot = slotWriteOf(object.object, key);
        const write = slot?.write;
        if (slot === undefined || write?.value.type !== "Identifier") return undefined;
        const table = scopes.staticVariableOf(write.value);
        return table === undefined ? undefined : { table, alias: { table, after: write.statement, block: slot.array.block } };
    };

    /**
     * Whether `object` is a slot `a[k]` every write of which assigns the array `variable` names (while it is assumed
     * unchanged, reading such a slot gives the array, or `undefined`, and then `a[k][key]` throws before any access).
     * An unwritten slot is `undefined` because no prototype has index properties: relies on model 7: builtins intact.
     */
    const holdsOnly = (object: Node, variable: Variable): boolean => {
        const key = object.type === "MemberExpression" ? literalIndex(object) : undefined;
        if (object.type !== "MemberExpression" || key === undefined) return false;
        const values = slotWriteOf(object.object, key)?.array.assigned.get(key);
        return values !== undefined && values.every((assigned) => assigned?.type === "Identifier" && scopes.staticVariableOf(assigned) === variable);
    };

    /** `T[k]` on a constant array (directly or through an alias): element k, when the read sees the array. */
    const tableRead = (member: MemberExpression): Evaluation => {
        const holder = holderOf(member.object);
        const assumed = validating !== undefined && (holder?.table === validating.variable || holdsOnly(member.object, validating.variable));
        const table = assumed ? validating?.table : holder === undefined ? undefined : tableOf(holder.table);
        if (table === undefined) return FAIL;
        if (!assumed && holder !== undefined) {
            const { alias } = holder;
            const sees = alias === undefined ? reachesAfter(table.block, table.after, member) : reachesAfter(alias.block, alias.after, member) && reachesAfter(table.block, table.after, alias.after);
            if (!sees) return FAIL;
        }
        const key = member.computed ? evaluate(member.property, env) : value(member.property.name);
        if (!key.ok) return FAIL;
        const name = String(key.value);
        if (name === "length") return value(table.elements.length);
        return isIndexKey(name) ? (table.elements[Number(name)] ?? FAIL) : FAIL;
    };

    const lookup = (node: Expression): Evaluation => {
        if (node.type === "Identifier") {
            const variable = scopes.variableOf(node);
            const constant = variable === undefined ? undefined : constantOf(variable);
            if (variable === undefined || constant === undefined) return FAIL;
            return reachesAfter(variable.scope.block as unknown as Node, constant.after, node) ? { ok: true, value: constant.value } : FAIL;
        }
        if (node.type !== "MemberExpression" || !("property" in node)) return FAIL;
        const key = node.object.type === "Identifier" ? literalIndex(node) : undefined;
        const slot = key === undefined ? undefined : slotWriteOf(node.object, key);
        const constant = slot?.write === undefined ? undefined : slotConstant(slot.write);
        if (slot !== undefined && constant !== undefined) {
            return reachesAfter(slot.array.block, constant.after, node) ? { ok: true, value: constant.value } : FAIL;
        }
        return tableRead(node);
    };

    const env: ConstantEnv = { ...globalsEnv(scopes), lookup, functionAt, onlyByName: (variable) => globalSafe(variable) === true };
    return env;
};

/**
 * An evaluation environment that only knows which identifiers name the global `undefined`, `NaN` and `Infinity`:
 * an identifier the analysis doesn't know (created by a pass since) names the global when no scope declares it.
 */
export const globalsEnv = (scopes: ScopeInfo): EvaluateEnv => ({
    isGlobal: (identifier: Node): boolean =>
        scopes.isGlobalReference(identifier) || (identifier.type === "Identifier" && scopes.referenceOf(identifier) === undefined && !scopes.declaresName(identifier.name)),
});
