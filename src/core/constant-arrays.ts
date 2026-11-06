import type { Expression, MemberExpression, Node } from "./ast.js";
import { isIndexKey, memberKey } from "./ast.js";
import type { Constant } from "./constant-bindings.js";
import type { Analysis } from "./constants.js";
import type { Evaluation } from "./evaluate.js";
import { evaluate, FAIL, value } from "./evaluate.js";
import { referenceParent } from "./execution-order.js";
import type { Refusal } from "./global-escape.js";
import type { Variable } from "./scope.js";

/** `after`: the definition (in `block`) after which the array holds. */
interface Table {
    readonly elements: readonly Evaluation[];
    readonly after: Node;
    readonly block: Node;
}

interface Alias {
    readonly table: Variable;
    readonly after: Node;
    readonly block: Node;
}

interface SlotWrite {
    readonly value: Expression;
    readonly statement: Node;
}

interface SlotArray {
    readonly block: Node;
    /** `undefined` when a slot has several writes, or one that isn't a plain top-level statement. */
    readonly writes: Map<string, SlotWrite | undefined>;
    /** `undefined` entries: initializer elements and writes other than `=`. */
    readonly assigned: Map<string, (Expression | undefined)[]>;
    readonly reads: Map<string, Node[]>;
}

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

/** Constant `arguments`-array slots and constant arrays (see `constantEnv`). */
export class ConstantArrays {
    readonly #analysis: Pick<Analysis, "scopes" | "order" | "globals" | "bindings" | "env" | "log" | "memo">;
    readonly #hasWith: boolean;
    readonly #slotArrays = new Map<Variable, SlotArray | undefined>();
    readonly #slotValues = new Map<Node, Constant | undefined>();
    readonly #tables = new Map<Variable, Table | undefined>();
    readonly #aliases = new Map<Variable, Alias | undefined>();
    /** The array whose uses are being checked, read as unchanged by the keys the check evaluates (see `constantEnv`). */
    #validating: { readonly variable: Variable; readonly table: Table } | undefined;

    constructor(analysis: Pick<Analysis, "scopes" | "order" | "globals" | "bindings" | "env" | "log" | "memo">) {
        this.#analysis = analysis;
        this.#hasWith = analysis.scopes.manager.scopes.some((scope) => scope.type === "with");
    }

    /** Whether a check is assuming an array unchanged: what it evaluates meanwhile holds only for that check. */
    get validating(): boolean {
        return this.#validating !== undefined;
    }

    /** `compute`, with no array assumed unchanged. */
    unassumed<T>(compute: () => T): T {
        const saved = this.#validating;
        this.#validating = undefined;
        try {
            return compute();
        } finally {
            this.#validating = saved;
        }
    }

    /** A read of a constant slot (`a[5]`) or of a constant array's element or length (`T[1]`, `a[4][1]`, `A.length`). */
    read(member: MemberExpression): Evaluation {
        const key = member.object.type === "Identifier" ? literalIndex(member) : undefined;
        const slot = key === undefined ? undefined : this.#slotWriteOf(member.object, key);
        const constant = slot?.write === undefined ? undefined : this.#slotConstant(slot.write);
        if (slot !== undefined && constant !== undefined) {
            return this.#analysis.order.reachesAfter(slot.array.block, constant.after, member) ? { ok: true, value: constant.value } : FAIL;
        }
        return this.#tableRead(member);
    }

    /**
     * Whether `key` reads a constant array (`T[k]`, through an alias too) none of whose elements is `name`, whatever
     * `k` is: an element, `undefined` past the end, or an inherited value (a function, `length`'s number, the
     * prototype's empty join), none of which spells an identifier but `undefined`. Before the array is there the
     * holder is `undefined`, and the read throws before any access.
     */
    keyOfTable(key: Node, name: string): boolean {
        if (key.type !== "MemberExpression" || !key.computed || name === "undefined") return false;
        const table = this.#tableOfHolder(key.object, this.#holderOf(key.object)).table;
        return table !== undefined && table.elements.every((element) => element.ok && String(element.value) !== name);
    }

    #tableRead(member: MemberExpression): Evaluation {
        const holder = this.#holderOf(member.object);
        const { table, assumed } = this.#tableOfHolder(member.object, holder);
        if (table === undefined) return FAIL;
        if (!assumed && holder !== undefined) {
            const { order } = this.#analysis;
            const { alias } = holder;
            const sees =
                alias === undefined
                    ? order.reachesAfter(table.block, table.after, member)
                    : order.reachesAfter(alias.block, alias.after, member) && order.reachesAfter(table.block, table.after, alias.after);
            if (!sees) return FAIL;
        }
        const key = member.computed ? evaluate(member.property, this.#analysis.env) : value(member.property.name);
        if (!key.ok) return FAIL;
        const name = String(key.value);
        if (name === "length") return value(table.elements.length);
        return isIndexKey(name) ? (table.elements[Number(name)] ?? FAIL) : FAIL;
    }

    /** The array `object` (its `holder`) holds: the one being validated, assumed unchanged, or a constant one. */
    #tableOfHolder(object: Node, holder: { table: Variable } | undefined): { table: Table | undefined; assumed: boolean } {
        const validating = this.#validating;
        const assumed = validating !== undefined && (holder?.table === validating.variable || this.#holdsOnly(object, validating.variable));
        return { table: assumed ? validating?.table : holder === undefined ? undefined : this.#tableOf(holder.table), assumed };
    }

    #slotArrayOf(variable: Variable): SlotArray | undefined {
        return this.#analysis.memo(this.#slotArrays, variable, () => {
            const { scopes, order, globals } = this.#analysis;
            const [def] = variable.defs;
            if (variable.defs.length !== 1 || def === undefined || def.type !== "Variable") return undefined;
            const declarator = def.node as unknown as Node;
            if (declarator.type !== "VariableDeclarator" || declarator.init?.type !== "ArrayExpression") return undefined;
            const references = scopes.staticReferences(variable);
            if (references.filter((reference) => reference.isWrite()).length !== 1 || globals.safe(variable) !== true) return undefined;
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
                const member = referenceParent(scopes, id);
                if (member?.type !== "MemberExpression" || member.object !== id) return undefined;
                const key = literalIndex(member);
                if (key === undefined) return undefined;
                const above = referenceParent(scopes, member);
                const outer = above === undefined ? undefined : referenceParent(scopes, above);
                if (!isWritten(member, above, outer)) {
                    const list = reads.get(key);
                    if (list === undefined) reads.set(key, [member]);
                    else list.push(member);
                    continue;
                }
                const right = above?.type === "AssignmentExpression" && above.operator === "=" ? above.right : undefined;
                const plain = right !== undefined && outer?.type === "ExpressionStatement" && order.isTopLevel(block, outer);
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
    }

    #slotWriteOf(object: Node, key: string): { array: SlotArray; write: SlotWrite | undefined } | undefined {
        const variable = object.type === "Identifier" ? this.#analysis.scopes.staticVariableOf(object) : undefined;
        const array = variable === undefined ? undefined : this.#slotArrayOf(variable);
        return array === undefined ? undefined : { array, write: array.writes.get(key) };
    }

    #slotConstant(write: SlotWrite): Constant | undefined {
        return this.#analysis.memo(this.#slotValues, write.statement, () => {
            const result = evaluate(write.value, this.#analysis.env);
            return result.ok ? { value: result.value, after: write.statement } : undefined;
        });
    }

    #tableOf(variable: Variable): Table | undefined {
        return this.#analysis.memo(this.#tables, variable, () => {
            const { log } = this.#analysis;
            const definition = this.#arrayDefinition(variable);
            const elements = definition === undefined ? undefined : this.#elementsOf(definition.array);
            // `[arguments]`: no element to resolve, nothing worth checking.
            if (definition === undefined || elements === undefined || !elements.some((element) => element.ok)) return undefined;
            const table: Table = { elements, after: definition.after, block: variable.scope.block as unknown as Node };
            const refusals = this.#tableRefusals(variable, definition.id, table);
            for (const refusal of refusals) log?.debug(`array ${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            if (refusals.length > 0) return undefined;
            log?.debug(`array ${variable.name} is constant (${elements.length} elements)`, definition.after);
            return table;
        });
    }

    #arrayDefinition(variable: Variable): { array: Node; after: Node; id: Node } | undefined {
        const { scopes, order } = this.#analysis;
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
            if (declarator.init.type !== "ArrayExpression" || declaration === null || !order.isTopLevel(block, declaration)) return undefined;
            return { array: declarator.init, after: declarator, id: declarator.id };
        }
        const id = write.identifier as unknown as Node;
        const assignment = referenceParent(scopes, id);
        if (assignment?.type !== "AssignmentExpression" || assignment.operator !== "=" || assignment.left !== id || assignment.right.type !== "ArrayExpression") return undefined;
        const statement = referenceParent(scopes, assignment);
        if (statement?.type !== "ExpressionStatement" || !order.isTopLevel(block, statement)) return undefined;
        return { array: assignment.right, after: statement, id };
    }

    #elementsOf(array: Node): Evaluation[] | undefined {
        if (array.type !== "ArrayExpression") return undefined;
        const elements: Evaluation[] = [];
        for (const element of array.elements) {
            // A hole reads `Array.prototype[i]`, which isn't there: relies on model 7: builtins intact.
            if (element === null) elements.push(value(undefined));
            else if (element.type === "SpreadElement") return undefined;
            else elements.push(evaluate(element.type === "SequenceExpression" ? (element.expressions.at(-1) as Expression) : element, this.#analysis.env));
        }
        return elements;
    }

    /**
     * Why the array `variable` holds (defined by `id`) could change, checked with `table` assumed (see `constantEnv`):
     * the first reason, or every one when the log shows them.
     */
    #tableRefusals(variable: Variable, id: Node, table: Table): Refusal[] {
        if (this.#hasWith) return [{ reason: "the program uses with", node: id }];
        const { scopes, globals, log } = this.#analysis;
        const all = log?.debugging === true;
        const saved = this.#validating;
        this.#validating = { variable, table };
        try {
            const refusals = globals.refusals(variable, all);
            const holders = new Set<unknown>();
            for (const reference of scopes.staticReferences(variable)) {
                if (refusals.length > 0 && !all) break;
                const use = reference.identifier as unknown as Node;
                const refusal = use === id ? undefined : this.#checkUse(use, holders);
                if (refusal !== undefined) refusals.push(refusal);
            }
            return refusals;
        } finally {
            this.#validating = saved;
        }
    }

    /**
     * A use of the array (`id`, a reference other than its definition): an element read, or a copy into a holder
     * (`var A = T`, `A = T`, `a[4] = T`) whose reads are element reads. `checked`: holders already checked.
     */
    #checkUse(id: Node, checked: Set<unknown>): Refusal | undefined {
        const { scopes } = this.#analysis;
        const above = referenceParent(scopes, id);
        if (above?.type === "MemberExpression" && above.object === id) return this.#checkRead(above);
        // The copy's own value must go nowhere else: `var A = T`, or `A = T;` as a statement.
        const target =
            above?.type === "VariableDeclarator" && above.init === id
                ? above.id
                : above?.type === "AssignmentExpression" && above.operator === "=" && above.right === id && referenceParent(scopes, above)?.type === "ExpressionStatement"
                  ? above.left
                  : undefined;
        if (target?.type === "Identifier") {
            const variable = scopes.staticVariableOf(target);
            if (variable === undefined || variable.scope.type === "global") return { reason: "copied into a global", node: id };
            // A sloppy function's `arguments` object aliases its parameters.
            if (variable.defs.some((def) => def.type === "Parameter")) return { reason: "copied into a parameter", node: id };
            if (checked.has(variable)) return undefined;
            checked.add(variable);
            const reads = scopes.staticReferences(variable).filter((reference) => reference.isRead());
            return this.#checkReadsOf(reads.map((reference) => reference.identifier as unknown as Node));
        }
        const key = target?.type === "MemberExpression" ? literalIndex(target) : undefined;
        if (target?.type === "MemberExpression" && key !== undefined) {
            const slot = this.#slotWriteOf(target.object, key);
            if (slot === undefined) return { reason: "copied into an array used other than as slots", node: id };
            const reads = slot.array.reads.get(key) ?? [];
            if (checked.has(reads)) return undefined;
            checked.add(reads);
            return this.#checkReadsOf(reads);
        }
        return { reason: "the array escapes (passed, returned, stored or iterated)", node: id };
    }

    /** Each of a holder's reads (a local's references, or a slot's `a[k]`) is the object of an element read. */
    #checkReadsOf(reads: readonly Node[]): Refusal | undefined {
        for (const read of reads) {
            const member = referenceParent(this.#analysis.scopes, read);
            const refusal = member?.type === "MemberExpression" && member.object === read ? this.#checkRead(member) : { reason: "a copy is used other than as an element read", node: read };
            if (refusal !== undefined) return refusal;
        }
        return undefined;
    }

    /** A read `T[k]` (`member`, its object a reference to the array or a holder) that leaves the array as it is. */
    #checkRead(member: Node): Refusal | undefined {
        if (member.type !== "MemberExpression") return { reason: "used other than as an element read", node: member };
        const { scopes, env } = this.#analysis;
        const above = referenceParent(scopes, member);
        const outer = above === undefined ? undefined : referenceParent(scopes, above);
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
    }

    /** `var A = T;` (or `var A;` and one later `A = T;`): an alias of the array `T` may name, for reads after it. */
    #aliasOf(variable: Variable): Alias | undefined {
        return this.#analysis.memo(this.#aliases, variable, () => {
            const { scopes, order, bindings } = this.#analysis;
            const single = bindings.singleDefinition(variable);
            const block = variable.scope.block as unknown as Node;
            if (single?.value.type !== "Identifier" || !order.placed(block, single.statement, single.definition)) return undefined;
            const table = scopes.staticVariableOf(single.value);
            return table === undefined ? undefined : { table, after: single.definition, block };
        });
    }

    /** The array an expression (`T`, an alias `A`, a slot alias `a[4]`) may hold, and the alias, if it is one. */
    #holderOf(object: Node): { table: Variable; alias: Alias | undefined } | undefined {
        const { scopes } = this.#analysis;
        if (object.type === "Identifier") {
            const variable = scopes.staticVariableOf(object);
            if (variable === undefined) return undefined;
            const alias = this.#aliasOf(variable);
            return alias === undefined ? { table: variable, alias } : { table: alias.table, alias };
        }
        const key = object.type === "MemberExpression" ? literalIndex(object) : undefined;
        if (object.type !== "MemberExpression" || key === undefined) return undefined;
        const slot = this.#slotWriteOf(object.object, key);
        const write = slot?.write;
        if (slot === undefined || write?.value.type !== "Identifier") return undefined;
        const table = scopes.staticVariableOf(write.value);
        return table === undefined ? undefined : { table, alias: { table, after: write.statement, block: slot.array.block } };
    }

    /**
     * Whether `object` is a slot `a[k]` every write of which assigns the array `variable` names (while it is assumed
     * unchanged, reading such a slot gives the array, or `undefined`, and then `a[k][key]` throws before any access).
     * An unwritten slot is `undefined` because no prototype has index properties: relies on model 7: builtins intact.
     */
    #holdsOnly(object: Node, variable: Variable): boolean {
        const key = object.type === "MemberExpression" ? literalIndex(object) : undefined;
        if (object.type !== "MemberExpression" || key === undefined) return false;
        const values = this.#slotWriteOf(object.object, key)?.array.assigned.get(key);
        return values !== undefined && values.every((assigned) => assigned?.type === "Identifier" && this.#analysis.scopes.staticVariableOf(assigned) === variable);
    }
}
