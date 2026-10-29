import type { BlockStatement, Expression, Function as FunctionDeclaration, IfStatement, LabelIdentifier, Node, Statement } from "../../core/ast.js";
import { isBreakTarget, isFunctionNode, isJump } from "../../core/ast.js";
import { at } from "../../core/build.js";
import { bindingNames, hoistedDeclarations, placeholderDeclaration } from "../../core/hoisting.js";
import type { PassLog } from "../../core/log.js";
import { forEachChild } from "../../core/traverse.js";

/**
 * Readability clean-ups for code produced by `structure`. Each rewrite keeps behaviour identical:
 *
 * - a `break L` / `continue L` in tail position of L's own body goes where execution would go anyway, so it is dropped;
 * - labels nobody jumps to are removed (a labeled block without users is spliced into its parent);
 * - statements after an unconditional jump are unreachable and dropped, leaving what they declare (see `Dropped`);
 * - `if (c) { ...jump } else { B }` becomes `if (c) { ...jump } B`;
 * - `if (c) {} else { B }` becomes `if (!c) { B }`;
 * - `L: while (true)` loops of known shapes become `while (c)` / `do ... while (c)` (`recognizeLoop`).
 *
 * Statements only leave their block when none of them is a lexical declaration (`let`, `const`, `class`, a block
 * function): those would change scope.
 */

type JumpKind = "BreakStatement" | "ContinueStatement";

interface JumpCount {
    breaks: number;
    continues: number;
}

/** What tidy dropped as unreachable that still binds names for the whole function. */
export interface Dropped {
    /** `var` names: they bind wherever they are, so a placeholder anywhere in the function keeps them. */
    readonly vars: Set<string>;
    /** Functions declared in nested blocks: they bind a function-wide name only when Annex B applies. */
    readonly functions: FunctionDeclaration[];
}

interface Context {
    readonly log: PassLog;
    /** Rewrites in the current round. */
    changed: number;
    /**
     * Jumps to each label name, from one walk over the whole output, kept current as jumps are removed. By name, so
     * two sibling labels sharing one are counted together: every check stays conservative.
     */
    readonly jumps: Map<string, JumpCount>;
    readonly dropped: Dropped;
}

const change = (cx: Context, decision: string, node: Node): void => {
    cx.changed++;
    cx.log.debug(`tidy: ${decision}`, node);
};

const countOf = (cx: Context, label: string): JumpCount => {
    let count = cx.jumps.get(label);
    if (count === undefined) {
        count = { breaks: 0, continues: 0 };
        cx.jumps.set(label, count);
    }
    return count;
};

const used = (cx: Context, label: string): boolean => {
    const count = countOf(cx, label);
    return count.breaks + count.continues > 0;
};

/** Add `delta` for every labeled jump in `node` (functions are their own label scope and not entered). */
const countJumps = (cx: Context, node: Node, delta: number): void => {
    if (isFunctionNode(node)) return;
    if ((node.type === "BreakStatement" || node.type === "ContinueStatement") && node.label !== null) {
        const count = countOf(cx, node.label.name);
        if (node.type === "BreakStatement") count.breaks += delta;
        else count.continues += delta;
        return;
    }
    forEachChild(node, (child) => countJumps(cx, child, delta));
};

/** Labeled jumps of `kind` to `label` inside `statements`. For the few checks the totals can't answer. */
const jumpsIn = (statements: readonly Statement[], label: string, kind: JumpKind): number => {
    let found = 0;
    const walk = (node: Node): void => {
        if (isFunctionNode(node)) return;
        if (node.type === kind && node.label?.name === label) found++;
        else forEachChild(node, walk);
    };
    for (const statement of statements) walk(statement);
    return found;
};

/** A declaration scoped to the statement list it sits in. */
const isLexical = (s: Statement): boolean => (s.type === "VariableDeclaration" && s.kind !== "var") || s.type === "ClassDeclaration" || s.type === "FunctionDeclaration";

const declaresLexically = (statements: readonly Statement[]): boolean => statements.some(isLexical);

const asBlock = (s: Statement | null): BlockStatement | undefined => (s?.type === "BlockStatement" ? s : undefined);

/** Remove jumps to `label` in tail position of `statements`: the last statement, through ifs and nested blocks. */
const dropTailJumps = (cx: Context, statements: Statement[], label: string, kind: JumpKind): void => {
    const last = statements.at(-1);
    if (last === undefined) return;
    if (last.type === kind && last.label?.name === label) {
        statements.pop();
        countJumps(cx, last, -1);
        change(cx, `dropped ${kind === "BreakStatement" ? "break" : "continue"} ${label} in tail position`, last);
        dropTailJumps(cx, statements, label, kind);
        return;
    }
    if (last.type === "IfStatement") {
        const consequent = asBlock(last.consequent);
        if (consequent) dropTailJumps(cx, consequent.body, label, kind);
        const alternate = asBlock(last.alternate);
        if (alternate) dropTailJumps(cx, alternate.body, label, kind);
        return;
    }
    // Falling off the end of a block in tail position also reaches the end of the enclosing body.
    if (last.type === "LabeledStatement" && last.body.type === "BlockStatement") dropTailJumps(cx, last.body.body, label, kind);
    if (last.type === "BlockStatement") dropTailJumps(cx, last.body, label, kind);
};

const negate = (test: Expression): Expression =>
    test.type === "UnaryExpression" && test.operator === "!" ? test.argument : at({ type: "UnaryExpression", operator: "!", prefix: true, argument: test }, test);

const isLiteralTrue = (node: Expression): boolean => node.type === "Literal" && node.value === true;

/** Whether an unlabeled `break` in `node` would leave `node` itself: one walk, stopping at loops, switches, functions. */
const hasOwnBreak = (statements: readonly Statement[]): boolean => {
    let found = false;
    const walk = (node: Node): void => {
        if (found || isFunctionNode(node) || isBreakTarget(node)) return;
        if (node.type === "BreakStatement") found = node.label === null;
        else forEachChild(node, walk);
    };
    for (const statement of statements) walk(statement);
    return found;
};

/**
 * Whether running `statements` can finish by reaching their end (rather than always jumping, returning or throwing).
 * Conservative: when unsure, says yes.
 */
const canCompleteNormally = (cx: Context, statements: readonly Statement[]): boolean => statements.every((s) => statementCanComplete(cx, s));

const statementCanComplete = (cx: Context, s: Statement): boolean => {
    switch (s.type) {
        case "ReturnStatement":
        case "ThrowStatement":
        case "BreakStatement":
        case "ContinueStatement":
            return false;
        case "BlockStatement":
            return canCompleteNormally(cx, s.body);
        case "IfStatement":
            return s.alternate === null || statementCanComplete(cx, s.consequent) || statementCanComplete(cx, s.alternate);
        case "LabeledStatement":
            return statementCanComplete(cx, s.body) || countOf(cx, s.label.name).breaks > 0;
        case "WhileStatement":
            if (!isLiteralTrue(s.test)) return true;
            return s.body.type !== "BlockStatement" || hasOwnBreak(s.body.body);
        default:
            return true;
    }
};

const blockAt = (statements: Statement[], position: Statement): BlockStatement => at<BlockStatement>({ type: "BlockStatement", body: statements }, position);

/** A branch of an if: an `else if` stays a bare IfStatement, anything else becomes a block. */
const branchOf = (body: Statement[], like: Statement): Statement => (body.length === 1 && body[0]?.type === "IfStatement" && like.type === "IfStatement" ? body[0] : blockAt(body, like));

/**
 * Turn `L: while (true) { ... }` into a conditional loop when its body has one of these shapes:
 *
 *     if (c) { B; continue L } R      ->  while (c) { B } R      B: no break L. R: no jumps to L, never finishes.
 *     if (c) { X } R                  ->  while (!c) { R } X     X: never finishes, no jumps to L. R: no break L.
 *     B; if (c) { continue L } X      ->  do { B } while (c); X  B: no jumps to L. X: never finishes, no jumps to L.
 *
 * The caller has checked that the body declares nothing lexically. Returns the replacement statements, or undefined.
 */
const recognizeLoop = (cx: Context, labelNode: LabelIdentifier, body: readonly Statement[]): Statement[] | undefined => {
    const label = labelNode.name;
    const count = countOf(cx, label);
    const wrap = (loop: Statement): Statement => (used(cx, label) ? at<Statement>({ type: "LabeledStatement", label: labelNode, body: loop }, loop) : loop);

    const first = body[0];
    if (count.breaks === 0 && first?.type === "IfStatement" && first.alternate === null && first.consequent.type === "BlockStatement" && !declaresLexically(first.consequent.body)) {
        const then = first.consequent.body;
        const rest = body.slice(1);
        const last = then.at(-1);
        // while (c) { B } R: every continue L is in the if (so none in R).
        if (last?.type === "ContinueStatement" && last.label?.name === label && !canCompleteNormally(cx, rest) && jumpsIn(then, label, "ContinueStatement") === count.continues) {
            countJumps(cx, last, -1);
            return [wrap(at<Statement>({ type: "WhileStatement", test: first.test, body: blockAt(then.slice(0, -1), first) }, first)), ...rest];
        }
        // while (!c) { R } X: no continue L in X.
        if (!canCompleteNormally(cx, then) && jumpsIn(then, label, "ContinueStatement") === 0) {
            return [wrap(at<Statement>({ type: "WhileStatement", test: negate(first.test), body: blockAt(rest, first) }, first)), ...then];
        }
    }

    // do { B } while (c); X: the check's continue is the only jump to L.
    if (count.breaks !== 0 || count.continues !== 1) return undefined;
    const index = body.findIndex(
        (s) =>
            s.type === "IfStatement" &&
            s.alternate === null &&
            s.consequent.type === "BlockStatement" &&
            s.consequent.body.length === 1 &&
            s.consequent.body[0]?.type === "ContinueStatement" &&
            s.consequent.body[0].label?.name === label
    );
    const check = body[index];
    if (index > 0 && check?.type === "IfStatement") {
        const before = body.slice(0, index);
        const after = body.slice(index + 1);
        if (!canCompleteNormally(cx, after) && !hasOwnBreak(before)) {
            countJumps(cx, check, -1);
            return [at<Statement>({ type: "DoWhileStatement", test: check.test, body: blockAt(before, check) }, check), ...after];
        }
    }
    return undefined;
};

/**
 * `B: { if (a) { X; break B } if (b) { Y; break B } Z }` -> `if (a) { X } else if (b) { Y } else { Z }`, when every
 * jump to B is the last statement of one of those ifs: the trailing breaks consumed must add up to all of B's jumps.
 */
const ifChain = (cx: Context, statements: readonly Statement[], label: string): Statement[] | undefined => {
    const count = countOf(cx, label);
    if (count.continues !== 0) return undefined;
    const heads: { head: IfStatement; branch: BlockStatement }[] = [];
    while (heads.length < count.breaks) {
        const s = statements[heads.length];
        if (s?.type !== "IfStatement" || s.alternate !== null || s.consequent.type !== "BlockStatement") return undefined;
        const last = s.consequent.body.at(-1);
        if (last?.type !== "BreakStatement" || last.label?.name !== label) return undefined;
        heads.push({ head: s, branch: s.consequent });
    }
    const innermost = heads.at(-1);
    if (innermost === undefined) return undefined;
    const rest = statements.slice(heads.length);
    let alternate: Statement | null = rest.length === 0 ? null : rest.length === 1 && rest[0]?.type === "IfStatement" ? rest[0] : blockAt(rest, innermost.head);
    for (const { head, branch } of heads.toReversed()) alternate = { ...head, consequent: { ...branch, body: branch.body.slice(0, -1) }, alternate };
    count.breaks = 0;
    return alternate === null ? [] : [alternate];
};

/**
 * What unreachable `dead` statements leave in place: their own lexical declarations as `let` placeholders (still in
 * their temporal dead zone, as the originals would be forever) and their function declarations whole (hoisted, may be
 * called). Their `var`s and nested block functions go to `cx.dropped`; their labeled jumps leave the counts.
 */
const deadRemainder = (cx: Context, dead: readonly Statement[]): Statement[] => {
    const kept: Statement[] = [];
    const lexicalNames = new Set<string>();
    let origin: Statement | undefined;
    for (const s of dead) {
        if (s.type === "FunctionDeclaration" || (s.type === "VariableDeclaration" && s.kind === "let" && s.declarations.every((d) => d.init === null))) {
            kept.push(s);
            continue;
        }
        if (s.type === "VariableDeclaration" && s.kind !== "var") for (const d of s.declarations) bindingNames(d.id, lexicalNames);
        else if (s.type === "ClassDeclaration" && s.id !== null) lexicalNames.add(s.id.name);
        else hoistedDeclarations(s, cx.dropped);
        origin ??= s;
        countJumps(cx, s, -1);
        change(cx, "dropped unreachable statement", s);
    }
    return origin === undefined ? kept : [...placeholderDeclaration("let", lexicalNames, origin), ...kept];
};

const tidyList = (cx: Context, statements: readonly Statement[]): Statement[] => {
    const out: Statement[] = [];
    // Everything after an unconditional jump.
    let dead: Statement[] | undefined;
    const push = (s: Statement): void => {
        if (dead !== undefined) dead.push(s);
        else {
            out.push(s);
            if (isJump(s)) dead = [];
        }
    };

    for (const original of statements) {
        if (dead !== undefined) {
            dead.push(original);
            continue;
        }
        let statement = original;

        if (statement.type === "LabeledStatement" && statement.body.type === "BlockStatement") {
            const body = statement.body;
            const label = statement.label.name;
            body.body = tidyList(cx, body.body);
            dropTailJumps(cx, body.body, label, "BreakStatement");
            if (!declaresLexically(body.body)) {
                if (!used(cx, label)) {
                    change(cx, `removed unused label ${label}`, statement);
                    for (const s of body.body) push(s);
                    continue;
                }
                const chained = ifChain(cx, body.body, label);
                if (chained !== undefined) {
                    change(cx, `turned block ${label} into an if-else chain`, statement);
                    for (const s of chained) push(s);
                    continue;
                }
            } else if (!used(cx, label)) {
                change(cx, `removed unused label ${label}`, statement);
                statement = body;
            }
        } else if (statement.type === "LabeledStatement" && statement.body.type === "WhileStatement" && statement.body.body.type === "BlockStatement") {
            const loop = statement.body;
            const label = statement.label.name;
            const body = loop.body as BlockStatement;
            body.body = tidyList(cx, body.body);
            dropTailJumps(cx, body.body, label, "ContinueStatement");
            const rewritten = isLiteralTrue(loop.test) && !declaresLexically(body.body) ? recognizeLoop(cx, statement.label, body.body) : undefined;
            if (rewritten !== undefined) {
                change(cx, `rebuilt loop ${label}`, statement);
                for (const s of rewritten) push(s);
                continue;
            }
            if (!used(cx, label)) {
                change(cx, `removed unused label ${label}`, statement);
                statement = loop;
            }
        } else if (statement.type === "IfStatement") {
            // Branches as statement lists. An `else if` is a bare IfStatement, not a block: it is a real branch.
            const thenBody = tidyList(cx, statement.consequent.type === "BlockStatement" ? statement.consequent.body : [statement.consequent]);
            const elseBody = statement.alternate === null ? [] : tidyList(cx, statement.alternate.type === "BlockStatement" ? statement.alternate.body : [statement.alternate]);
            const consequent = branchOf(thenBody, statement.consequent);
            if (elseBody.length === 0) {
                if (statement.alternate !== null) change(cx, "dropped empty else", statement);
                statement = { ...statement, consequent, alternate: null };
            } else if (thenBody.length === 0) {
                change(cx, "inverted if with an empty branch", statement);
                statement = { ...statement, test: negate(statement.test), consequent: branchOf(elseBody, statement.alternate ?? statement), alternate: null };
            } else if (isJump(thenBody.at(-1)) && !declaresLexically(elseBody)) {
                change(cx, "moved else out after a branch that jumps", statement);
                push({ ...statement, consequent, alternate: null });
                for (const s of elseBody) push(s);
                continue;
            } else {
                statement = { ...statement, consequent, alternate: branchOf(elseBody, statement.alternate ?? statement) };
            }
        } else if (statement.type === "BlockStatement") {
            statement.body = tidyList(cx, statement.body);
        }
        push(statement);
    }
    if (dead !== undefined) out.push(...deadRemainder(cx, dead));
    return out;
};

const MAX_ROUNDS = 8;

/**
 * Tidy the statements `structure` produced for one machine, until nothing changes. Also returns what unreachable
 * code it dropped still declares, for the machine's preamble.
 */
export const tidy = (statements: Statement[], log: PassLog): { statements: Statement[]; dropped: Dropped } => {
    const cx: Context = { log, changed: 0, jumps: new Map(), dropped: { vars: new Set(), functions: [] } };
    for (const statement of statements) countJumps(cx, statement, 1);
    let current = statements;
    for (let round = 1; ; round++) {
        cx.changed = 0;
        current = tidyList(cx, current);
        if (cx.changed === 0) break;
        if (round === MAX_ROUNDS) {
            log.warn(`tidy: still changing after ${MAX_ROUNDS} rounds, stopping`, current[0]);
            break;
        }
    }
    return { statements: current, dropped: cx.dropped };
};
