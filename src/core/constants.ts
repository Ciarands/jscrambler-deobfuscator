import type { Expression, MemberExpression, Node } from "./ast.js";
import { isIndexKey, memberKey } from "./ast.js";
import type { EvaluateEnv, Evaluation, Value } from "./evaluate.js";
import { evaluate, FAIL, value } from "./evaluate.js";
import type { PassLog } from "./log.js";
import type { ScopeInfo, Variable } from "./scope.js";
import { forEachChild } from "./traverse.js";

/** Document order of one scope block, as the tree is now (after unflattening, that is execution order). */
interface BlockOrder {
    readonly index: Map<Node, number>;
    /** For nodes inside a function declaration: the nearest one. Hoisted, so callable before what precedes it. */
    readonly declaredIn: Map<Node, Node>;
    /** The last index inside each nested statement list (block, `case` body, static block). */
    readonly end: Map<Node, number>;
}

const ORDERED: Record<string, true> = { Identifier: true, MemberExpression: true, VariableDeclarator: true, ExpressionStatement: true };

/** A constant and the node after which (in document order) it holds. */
type Constant = { readonly value: Value; readonly after: Node };

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

/** What the whole program spells out, for script globals; collected in the one walk that builds the parents map. */
interface ProgramFacts {
    /** Parents of the nodes `parentOf` is asked about (see `PARENT_ASKED`). */
    readonly parents: Map<Node, Node>;
    /** Every string literal, template text and static property name: a global so named may be reached as a property. */
    readonly spelled: Set<string>;
    /** Computed members on an expression that is the global object (`window[k]`, top-level `this[k]`). */
    readonly globalMembers: MemberExpression[];
}

/**
 * The node types whose parent is asked for: references (identifiers, never the name of `o.name`), the members they
 * are the object of, declarations (for their statement list), and the members' parents an answer depends on: an
 * assignment (`a[k] = v;` as a statement) and a property (a destructuring target). Other parents are never read, so
 * leaving them out of the map (most of the program) changes no answer.
 */
const PARENT_ASKED: Record<string, true> = { Identifier: true, MemberExpression: true, VariableDeclaration: true, AssignmentExpression: true, Property: true };

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
 * - `var a = [arguments]; a[5] = "x";` makes later reads of `a[5]` evaluate to "x" (#13);
 * - `T = [(f(), "get"), "set"]; a[4] = T;` makes later reads of `a[4][1]` (and `T[1]`) evaluate to "set".
 *
 * A binding is constant when its only definition is a declarator whose initializer evaluates, it is never written
 * again, and the declaration is a statement directly in its function (or program) body, so it runs exactly once on
 * entry. A slot is constant when its array is only ever used as `a[constant]`, and the slot is written exactly once,
 * by such a top-level statement, with a constant. Reads get the value only when they come after the definition in
 * execution order (`reachesAfter`).
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
export const constantEnv = (scopes: ScopeInfo, log?: PassLog): EvaluateEnv => {
    const orders = new Map<Node, BlockOrder>();
    const constants = new Map<Variable, Constant | undefined>();
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
    const orderOf = (block: Node): BlockOrder => {
        const cached = orders.get(block);
        if (cached !== undefined) return cached;
        const order: BlockOrder = { index: new Map(), declaredIn: new Map(), end: new Map() };
        let next = 0;
        /** The nearest function declaration around the nodes being visited (one callback, no closure per node). */
        let declaration: Node | undefined;
        const walk = (node: Node): void => {
            if (ORDERED[node.type]) {
                order.index.set(node, next++);
                if (declaration !== undefined) order.declaredIn.set(node, declaration);
            }
            const outer = declaration;
            if (node !== block && node.type === "FunctionDeclaration") declaration = node;
            forEachChild(node, walk);
            declaration = outer;
            if (node.type === "BlockStatement" || node.type === "SwitchCase" || node.type === "StaticBlock") order.end.set(node, next - 1);
        };
        walk(block);
        orders.set(block, order);
        return order;
    };

    /** Whether `node` is the global object: `this` where it is (`thisIsGlobal`), or an unresolved global name for it. */
    const isGlobalObject = (node: Node, thisIsGlobal: boolean): boolean =>
        node.type === "ThisExpression"
            ? thisIsGlobal
            : node.type === "Identifier" && GLOBAL_OBJECT_NAMES[node.name] === true && scopes.referenceOf(node) !== undefined && scopes.staticVariableOf(node) === undefined;

    /** Parents and spelled names of the whole program, from one walk; built when the first candidate needs them. */
    let programFacts: ProgramFacts | undefined;
    const factsOf = (): ProgramFacts => {
        if (programFacts !== undefined) return programFacts;
        const facts: ProgramFacts = { parents: new Map(), spelled: new Set(), globalMembers: [] };
        if (program === undefined) return (programFacts = facts);
        // One callback for the whole walk (no closure per node): `parent` and `thisIsGlobal` describe the node whose
        // children are being visited.
        let parent: Node = program;
        let thisIsGlobal = program.type === "Program" && program.sourceType === "script";
        const visit = (child: Node): void => {
            const above = parent;
            if (PARENT_ASKED[child.type] === true && !(above.type === "MemberExpression" && !above.computed && above.property === child)) facts.parents.set(child, above);
            const name = spelledName(child);
            if (name !== undefined) facts.spelled.add(name);
            if (child.type === "MemberExpression" && child.computed && isGlobalObject(child.object, thisIsGlobal)) facts.globalMembers.push(child);
            const outerThis = thisIsGlobal;
            parent = child;
            thisIsGlobal = outerThis && BINDS_THIS[child.type] !== true;
            forEachChild(child, visit);
            parent = above;
            thisIsGlobal = outerThis;
        };
        forEachChild(program, visit);
        return (programFacts = facts);
    };
    const parentOf = (node: Node): Node | undefined => factsOf().parents.get(node);

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
     * For a constant declared inside a nested statement list rather than directly in its body: the last index of that
     * list. Control enters a statement list only at its start (no jump lands inside one), so a use after the
     * declaration and still inside the list runs after it in the same pass through the list.
     */
    const limits = new Map<Node, number>();

    /**
     * `use` runs after `definition`: it comes later in `block`'s document order (within the definition's statement
     * list, see `limits`) and, when it sits in a function declaration (hoisted), that function only runs after
     * `definition` too (`runsAfter`).
     */
    const reachesAfter = (block: Node, definition: Node, use: Node): boolean => {
        const order = orderOf(block);
        const at = order.index.get(definition);
        const position = order.index.get(use);
        if (at === undefined || position === undefined || position <= at || position > (limits.get(definition) ?? Number.POSITIVE_INFINITY)) return false;
        const declaration = order.declaredIn.get(use);
        return declaration === undefined || runsAfter(block, definition, declaration);
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
        const facts = factsOf();
        if (facts.spelled.has(variable.name)) return [{ reason: `the program spells ${variable.name} as a property or a string`, node }];
        const refusals: Refusal[] = [];
        for (const member of facts.globalMembers) {
            const key = evaluate(member.property, env);
            if (!key.ok) refusals.push({ reason: "the global object is used with an unknown key", node: member });
            else if (String(key.value) === variable.name) refusals.push({ reason: `the global object is used with the key ${variable.name}`, node: member });
            if (refusals.length > 0 && !all) break;
        }
        return refusals;
    };
    const globalChecks = new Map<Variable, boolean | undefined>();
    const globalSafe = (variable: Variable): boolean | undefined =>
        memo(globalChecks, variable, () => {
            const [refusal] = globalRefusals(variable, false);
            if (refusal !== undefined) log?.debug(`${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            return refusal === undefined;
        });

    const constantOf = (variable: Variable): Constant | undefined =>
        memo(constants, variable, () => {
            const [def] = variable.defs;
            if (variable.defs.length !== 1 || def === undefined || def.type !== "Variable") return undefined;
            const declarator = def.node as unknown as Node;
            const declaration = def.parent as unknown as Node | null;
            if (declarator.type !== "VariableDeclarator" || declarator.init === null || declarator.id.type !== "Identifier") return undefined;
            if (scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length !== 1) return undefined;
            const block = variable.scope.block as unknown as Node;
            if (declaration === null) return undefined;
            if (!isTopLevel(block, declaration)) {
                // Declared in a nested statement list: uses count only inside that list, after the declaration.
                const list = parentOf(declaration);
                const end = list === undefined ? undefined : orderOf(block).end.get(list);
                const listed = list?.type === "SwitchCase" ? list.consequent : list?.type === "BlockStatement" || list?.type === "StaticBlock" ? list.body : [];
                if (end === undefined || !(listed as readonly Node[]).includes(declaration)) return undefined;
                limits.set(declarator, end);
            }
            const result = evaluate(declarator.init, env);
            if (!result.ok || globalSafe(variable) !== true) return undefined;
            return { value: result.value, after: declarator };
        });

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
        const all = log?.debugging === true;
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
            for (const refusal of refusals) log?.debug(`array ${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            if (refusals.length > 0) return undefined;
            log?.debug(`array ${variable.name} is constant (${elements.length} elements)`, definition.after);
            return table;
        });

    /** `var A = T;` directly in its body, `A` never written again: an alias of the array `T` may name. */
    const aliasOf = (variable: Variable): Alias | undefined =>
        memo(aliases, variable, () => {
            const [def] = variable.defs;
            if (variable.defs.length !== 1 || def === undefined || def.type !== "Variable") return undefined;
            const declarator = def.node as unknown as Node;
            const declaration = def.parent as unknown as Node | null;
            if (declarator.type !== "VariableDeclarator" || declarator.init?.type !== "Identifier") return undefined;
            const block = variable.scope.block as unknown as Node;
            if (declaration === null || !isTopLevel(block, declaration)) return undefined;
            if (scopes.staticReferences(variable).filter((reference) => reference.isWrite()).length !== 1) return undefined;
            const table = scopes.staticVariableOf(declarator.init);
            return table === undefined ? undefined : { table, after: declarator, block };
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

    const env: EvaluateEnv = { ...globalsEnv(scopes), lookup };
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
