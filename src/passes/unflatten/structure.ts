import type { Expression, Statement } from "../../core/ast.js";
import { at } from "../../core/build.js";
import type { At } from "../../core/build.js";
import type { Block, Machine, StateKey, Terminator } from "./match.js";

/**
 * Turn a machine's blocks back into structured code, following Ramsey, "Beyond Relooper: recursive translation of
 * unstructured control flow to structured control flow" (ICFP 2022):
 *
 * - A block that is the target of a back edge (a loop header) becomes `L: while (true) { ... }`; back edges become
 *   `continue L`.
 * - A block with two or more forward predecessors (a merge point) is placed after a labeled block
 *   `B: { ... }`; forward edges to it become `break B`.
 * - Any other block has exactly one predecessor and is written inline where it is jumped to.
 *
 * Every block is written exactly once, so no code is duplicated: a block reached by two edges, even two edges out of
 * one block (`S = a ? 2 : b ? 2 : 3`), is a merge point. Leaving the machine becomes `break` out of a label around the
 * whole result. Only reducible graphs are handled; anything else is refused.
 */

const EXIT = "exit";
export type NodeId = StateKey | typeof EXIT;

export type StructureResult = { readonly ok: true; readonly statements: Statement[] } | { readonly ok: false; readonly reason: string };

/** Every edge out of a block, in order, one per `goto` (so `c ? 2 : 2` inside a branch counts twice). */
const successorsOf = (terminator: Terminator, into: NodeId[] = []): NodeId[] => {
    if (terminator.kind === "goto") into.push(terminator.target);
    else if (terminator.kind === "evaluate") successorsOf(terminator.next, into);
    else if (terminator.kind === "branch") {
        successorsOf(terminator.consequent, into);
        successorsOf(terminator.alternate, into);
    }
    return into;
};

const edgesOf = (machine: Machine, id: NodeId): NodeId[] => {
    if (id === EXIT) return [];
    const block = machine.blocks.get(id);
    return block === undefined ? [] : successorsOf(block.terminator);
};

/** The states reachable from the entry, in reverse postorder. Cases left out can never run. */
export const reachableOrder = (machine: Machine): NodeId[] => {
    const order: NodeId[] = [];
    const visited = new Set<NodeId>([machine.entry]);
    const stack: { id: NodeId; next: number; succ: NodeId[] }[] = [{ id: machine.entry, next: 0, succ: edgesOf(machine, machine.entry) }];
    while (stack.length > 0) {
        const top = stack[stack.length - 1] as (typeof stack)[number];
        if (top.next < top.succ.length) {
            const child = top.succ[top.next++] as NodeId;
            if (!visited.has(child)) {
                visited.add(child);
                stack.push({ id: child, next: 0, succ: edgesOf(machine, child) });
            }
        } else {
            order.push(top.id);
            stack.pop();
        }
    }
    return order.toReversed();
};

interface Labels {
    /** Fresh label name not used anywhere in the program. */
    next(prefix: string): string;
}

type Context = { readonly kind: "loop" | "block"; readonly node: NodeId; readonly label: string };

/** Structured statements for `machine`, whose reachable states are `order` (from `reachableOrder`). */
export const structure = (machine: Machine, order: readonly NodeId[], position: At, labels: Labels): StructureResult => {
    const blocks = machine.blocks;
    const successors = new Map<NodeId, NodeId[]>(order.map((id) => [id, edgesOf(machine, id)]));
    const edges = (id: NodeId): readonly NodeId[] => successors.get(id) ?? [];
    const rpo = new Map<NodeId, number>(order.map((id, index) => [id, index]));
    const rank = (id: NodeId): number => rpo.get(id) ?? -1;

    const predecessors = new Map<NodeId, NodeId[]>(order.map((id) => [id, []]));
    for (const id of order) for (const s of edges(id)) predecessors.get(s)?.push(id);

    // Dominators: Cooper, Harvey & Kennedy, "A Simple, Fast Dominance Algorithm".
    const idom = new Map<NodeId, NodeId>([[machine.entry, machine.entry]]);
    const intersect = (a: NodeId, b: NodeId): NodeId => {
        let x = a;
        let y = b;
        while (x !== y) {
            while (rank(x) > rank(y)) x = idom.get(x) as NodeId;
            while (rank(y) > rank(x)) y = idom.get(y) as NodeId;
        }
        return x;
    };
    for (let changed = true; changed;) {
        changed = false;
        for (const id of order) {
            if (id === machine.entry) continue;
            let candidate: NodeId | undefined;
            for (const p of predecessors.get(id) ?? []) if (idom.has(p)) candidate = candidate === undefined ? p : intersect(p, candidate);
            if (candidate !== undefined && idom.get(id) !== candidate) {
                idom.set(id, candidate);
                changed = true;
            }
        }
    }
    const dominates = (a: NodeId, b: NodeId): boolean => {
        for (let x = b; ; x = idom.get(x) as NodeId) {
            if (x === a) return true;
            if (x === machine.entry) return false;
        }
    };

    const isBackward = (from: NodeId, to: NodeId): boolean => rank(to) <= rank(from);
    const loopHeaders = new Set<NodeId>();
    const forwardPredecessors = new Map<NodeId, number>();
    for (const id of order) {
        for (const s of edges(id)) {
            if (isBackward(id, s)) {
                if (!dominates(s, id)) return { ok: false, reason: "control flow is irreducible" };
                loopHeaders.add(s);
            } else {
                forwardPredecessors.set(s, (forwardPredecessors.get(s) ?? 0) + 1);
            }
        }
    }
    const isMerge = (id: NodeId): boolean => (forwardPredecessors.get(id) ?? 0) >= 2;
    const children = new Map<NodeId, NodeId[]>(order.map((id) => [id, []]));
    for (const id of order) if (id !== machine.entry) children.get(idom.get(id) as NodeId)?.push(id);

    const exitLabel = labels.next("exit");
    let exitUsed = false;

    // Builders. Every new node takes the machine's position, so logs and scope analysis keep working.
    const block = (body: Statement[]): Statement => at({ type: "BlockStatement", body }, position);
    const labeled = (label: string, body: Statement): Statement => at({ type: "LabeledStatement", label: at({ type: "Identifier", name: label }, position), body }, position);
    const jump = (type: "BreakStatement" | "ContinueStatement", label: string): Statement => at({ type, label: at({ type: "Identifier", name: label }, position) }, position);
    const loopForever = (body: Statement[]): Statement => at({ type: "WhileStatement", test: at({ type: "Literal", value: true, raw: "true" }, position), body: block(body) }, position);
    const ifElse = (test: Expression, consequent: Statement[], alternate: Statement[]): Statement =>
        at({ type: "IfStatement", test, consequent: block(consequent), alternate: alternate.length > 0 ? block(alternate) : null }, position);

    const contextLabel = (context: readonly Context[], kind: Context["kind"], node: NodeId): string | undefined => context.find((c) => c.kind === kind && c.node === node)?.label;

    let failure: string | undefined;

    const doTree = (x: NodeId, context: readonly Context[]): Statement[] => {
        const merges = (children.get(x) ?? []).filter(isMerge).toSorted((a, b) => rank(b) - rank(a));
        if (loopHeaders.has(x)) {
            const label = labels.next("loop");
            return [labeled(label, loopForever(nodeWithin(x, merges, [{ kind: "loop", node: x, label }, ...context])))];
        }
        return nodeWithin(x, merges, context);
    };

    const nodeWithin = (x: NodeId, merges: readonly NodeId[], context: readonly Context[]): Statement[] => {
        const [y, ...rest] = merges;
        if (y === undefined) {
            if (x === EXIT) {
                exitUsed = true;
                return [jump("BreakStatement", exitLabel)];
            }
            const b = blocks.get(x) as Block;
            return [...b.statements, ...control(x, b.terminator, context)];
        }
        const label = labels.next("block");
        return [labeled(label, block(nodeWithin(x, rest, [{ kind: "block", node: y, label }, ...context]))), ...doTree(y, context)];
    };

    const control = (x: NodeId, terminator: Terminator, context: readonly Context[]): Statement[] => {
        if (terminator.kind === "end") return [];
        if (terminator.kind === "goto") return doBranch(x, terminator.target, context);
        if (terminator.kind === "evaluate") return [at<Statement>({ type: "ExpressionStatement", expression: terminator.expression }, terminator.expression), ...control(x, terminator.next, context)];
        return [ifElse(terminator.test, control(x, terminator.consequent, context), control(x, terminator.alternate, context))];
    };

    const doBranch = (from: NodeId, to: NodeId, context: readonly Context[]): Statement[] => {
        if (isBackward(from, to)) {
            const label = contextLabel(context, "loop", to);
            if (label === undefined) {
                failure ??= `no enclosing loop for back edge to ${to}`;
                return [];
            }
            return [jump("ContinueStatement", label)];
        }
        if (isMerge(to)) {
            const label = contextLabel(context, "block", to);
            if (label === undefined) {
                failure ??= `no enclosing block for merge point ${to}`;
                return [];
            }
            return [jump("BreakStatement", label)];
        }
        return doTree(to, context);
    };

    const body = doTree(machine.entry, []);
    if (failure !== undefined) return { ok: false, reason: failure };
    return { ok: true, statements: exitUsed ? [labeled(exitLabel, block(body))] : body };
};
