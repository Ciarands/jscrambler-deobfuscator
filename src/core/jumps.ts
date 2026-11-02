import type { BlockStatement, BreakStatement, ContinueStatement, IfStatement, Node, Statement } from "./ast.js";
import { isBreakTarget, isLoopNode } from "./ast.js";
import { forEachChild, walkSkippingFunctions } from "./traverse.js";

/** Labels and the jumps that name them, for the passes that remove or move labels. Labels don't reach into functions. */

export type JumpKind = "BreakStatement" | "ContinueStatement";
export type Jump = BreakStatement | ContinueStatement;

/** A `let`/`const`/`class` or (labelled) function declaration: it binds in its block, so it can't leave a block that goes. */
export const isBlockScoped = (statement: Statement): boolean => {
    let item = statement;
    while (item.type === "LabeledStatement") item = item.body;
    return (item.type === "VariableDeclaration" && item.kind !== "var") || item.type === "ClassDeclaration" || item.type === "FunctionDeclaration";
};

/** `node` is a jump naming `label` (of `kind`, when given). */
export const isJumpTo = (node: Node | null | undefined, label: string, kind?: JumpKind): node is Jump =>
    (kind === undefined ? node?.type === "BreakStatement" || node?.type === "ContinueStatement" : node?.type === kind) && (node as Jump).label?.name === label;

/** `if (c) { ...; break label; }` with no `else` (or `continue label`, for that `kind`). */
export const isJumpingIf = (statement: Statement | undefined, label: string, kind: JumpKind): statement is IfStatement & { consequent: BlockStatement } =>
    statement?.type === "IfStatement" && statement.alternate === null && statement.consequent.type === "BlockStatement" && isJumpTo(statement.consequent.body.at(-1), label, kind);

const forEachJump = (root: Node, fn: (jump: Jump) => void): void => {
    walkSkippingFunctions(root, (node) => {
        if (node.type !== "BreakStatement" && node.type !== "ContinueStatement") return true;
        fn(node);
        return false;
    });
};

/** The jumps naming `label` (of `kind`, when given) in `roots` and under them. */
export const labeledJumps = (roots: Node | readonly Node[], label: string, kind?: JumpKind): Jump[] => {
    const found: Jump[] = [];
    const collect = (jump: Jump): void => {
        if (isJumpTo(jump, label, kind)) found.push(jump);
    };
    if (Array.isArray(roots)) for (const root of roots as readonly Node[]) forEachJump(root, collect);
    else forEachJump(roots as Node, collect);
    return found;
};

export interface JumpCount {
    breaks: number;
    continues: number;
}

/**
 * Jumps to each label name, kept current by the caller as jumps go. By name, so two sibling labels sharing one are
 * counted together: every check on the counts stays conservative.
 */
export class JumpCounts {
    readonly #counts = new Map<string, JumpCount>();

    of(label: string): JumpCount {
        let count = this.#counts.get(label);
        if (count === undefined) {
            count = { breaks: 0, continues: 0 };
            this.#counts.set(label, count);
        }
        return count;
    }

    used(label: string): boolean {
        const count = this.of(label);
        return count.breaks + count.continues > 0;
    }

    /** Add `delta` for every labeled jump in `node`. */
    add(node: Node, delta: number): void {
        forEachJump(node, (jump) => {
            if (jump.label === null) return;
            const count = this.of(jump.label.name);
            if (jump.type === "BreakStatement") count.breaks += delta;
            else count.continues += delta;
        });
    }
}

/** A plain `break` under `roots` outside their loops and `switch`es: it leaves the loop they sit in. */
export const hasPlainBreak = (roots: readonly Node[]): boolean => {
    let found = false;
    const visit = (node: Node): boolean => {
        if (found || isBreakTarget(node)) return false;
        if (node.type !== "BreakStatement") return true;
        found = node.label === null;
        return false;
    };
    for (const root of roots) walkSkippingFunctions(root, visit);
    return found;
};

/**
 * The jumps to `label` under `node`'s children, when none is in a loop of `node`, nor in a `switch` of it when it is
 * (or becomes, `as`) a `break`: then the jump without its label, or the unlabeled jump it becomes, reaches the loop
 * around `node` (or `node`'s own, for its children). `undefined` otherwise.
 */
export const plainJumps = (node: Node, label: string, as: "same" | JumpKind): Jump[] | undefined => {
    const jumps: Jump[] = [];
    let plain = true;
    let loops = 0;
    let switches = 0;
    const enter = (child: Node): boolean => {
        if (!plain) return false;
        if (isJumpTo(child, label)) {
            if (loops > 0 || ((as === "same" ? child.type : as) === "BreakStatement" && switches > 0)) plain = false;
            else jumps.push(child);
            return false;
        }
        if (isLoopNode(child)) loops++;
        if (child.type === "SwitchStatement") switches++;
        return true;
    };
    const leave = (child: Node): void => {
        if (isLoopNode(child)) loops--;
        if (child.type === "SwitchStatement") switches--;
    };
    forEachChild(node, (child) => walkSkippingFunctions(child, enter, leave));
    return plain ? jumps : undefined;
};

export const unlabelJumps = (jumps: readonly Jump[]): void => {
    for (const jump of jumps) jump.label = null;
};
