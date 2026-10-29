import type { Expression, ForStatement, Node, Statement, SwitchCase, SwitchStatement } from "../../core/ast.js";
import { isBreakTarget, isFunctionNode, isLoopNode } from "../../core/ast.js";
import { at } from "../../core/build.js";
import { sameReference } from "../../core/equal.js";
import { evaluate } from "../../core/evaluate.js";
import { forEachChild } from "../../core/traverse.js";

/** Canonical key of a state value: `n:5`, `s:abc`, `o:3`... Two states are the same iff their keys are equal. */
export type StateKey = string;

/**
 * Key of the block a computed initial state starts with (`var S = c() ? 2 : 5`): no case, just the choice. Never a
 * state value's key (those carry a `x:` prefix).
 */
const ENTRY: StateKey = "entry";

export type Terminator =
    | { readonly kind: "goto"; readonly target: StateKey | "exit" }
    | { readonly kind: "branch"; readonly test: Expression; readonly consequent: Terminator; readonly alternate: Terminator }
    /** `S = c ? 2 : 2`: `c` still runs for its effects, then `next`. */
    | { readonly kind: "evaluate"; readonly expression: Expression; readonly next: Terminator }
    /** The block ends in `return` or `throw`; it has no successor. */
    | { readonly kind: "end" };

export interface Block {
    readonly key: StateKey;
    /**
     * The case body without its transition, and without its function declarations: the switch hoists those to its
     * top, so they belong to every case (`declarations.ts` decides where they go).
     */
    readonly statements: Statement[];
    /** What follows a case-level `return`/`throw`: never runs, but its declarations still count. */
    readonly dead: readonly Statement[];
    readonly terminator: Terminator;
    /** The `case` this block came from; `null` for the block that picks a computed initial state. */
    readonly origin: SwitchCase | null;
}

export interface Machine {
    /** The variable (or `arguments` slot like `a[4]`) holding the state. */
    readonly state: Expression;
    readonly entry: StateKey | "exit";
    readonly blocks: ReadonlyMap<StateKey, Block>;
    /** The `switch (S)` itself: its cases share one block scope. */
    readonly dispatch: SwitchStatement;
    /** Cases whose label repeats an earlier one: never dispatched to, but their declarations still count. */
    readonly duplicates: readonly SwitchCase[];
    /** Earlier sibling statement that only sets the initial state (`var S = 2;`). Removable with the machine. */
    readonly initializer: Statement | null;
    /** What the loop's init clause does besides setting the state (`var a` in `for (var a, S = 2; ...)`), in order. */
    readonly preamble: Statement[];
}

/** Where a candidate loop sits: the matcher only needs these, not the walker's path. */
export interface MachineSite {
    readonly loop: ForStatement;
    /** The statement list holding the loop, or `null` when it's a lone statement (`if (x) for (...)`). */
    readonly siblings: readonly Statement[] | null;
    /** The loop's index in `siblings`. */
    readonly index: number | null;
    /** The loop is the body of a labeled statement. */
    readonly labeled: boolean;
}

/** The variable an identifier resolves to, or `undefined` when unknown (unresolved, or not in the analysed program). */
export type Resolve = (identifier: Node) => object | undefined;

/**
 * Why a loop was left alone, as a stable code (for counting and control flow) plus a human-readable reason (for logs).
 *
 * - `not-a-machine`: an ordinary loop, nothing to report;
 * - `shape`: looks like a machine, but some part doesn't fit exactly;
 * - `non-constant-state`: a state value the evaluator (and the runtime model) can't turn into a key;
 * - `state-escapes`: the state is used somewhere unflattening would change what it sees;
 * - `escaping-jump`: a case body breaks or continues out of the machine;
 * - `block-scoped-declaration`: moving case code out of the switch would change what a declaration binds;
 * - `lexical-loop-init`: a `let` in the loop's init clause whose per-iteration copies can be told apart;
 * - `unstructured`: the control flow graph is irreducible.
 */
export type RefusalCode = "not-a-machine" | "shape" | "non-constant-state" | "state-escapes" | "escaping-jump" | "block-scoped-declaration" | "lexical-loop-init" | "unstructured";

export interface Refusal {
    readonly ok: false;
    readonly code: RefusalCode;
    readonly reason: string;
    readonly node?: Node;
}

export const refuse = (code: RefusalCode, reason: string, node?: Node): Refusal => (node === undefined ? { ok: false, code, reason } : { ok: false, code, reason, node });

export type MatchResult = { readonly ok: true; readonly machine: Machine } | Refusal;

const constantKey = (node: Node): StateKey | undefined => {
    const result = evaluate(node);
    if (!result.ok) return undefined;
    return typeof result.value === "number" ? `n:${result.value}` : typeof result.value === "string" ? `s:${result.value}` : undefined;
};

/** `S` itself for an identifier state, `a` for `a[4]`. */
const rootIdentifier = (node: Node): Node | undefined => {
    let current = node;
    while (current.type === "MemberExpression") current = current.object;
    return current.type === "Identifier" ? current : undefined;
};

/** Recognises references to the state, telling apart same-named variables when the resolver knows both bindings. */
type IsState = (node: Node) => boolean;

const stateMatcher = (state: Expression, resolve: Resolve | undefined): IsState => {
    const stateRoot = rootIdentifier(state);
    const stateBinding = resolve !== undefined && stateRoot !== undefined ? resolve(stateRoot) : undefined;
    return (node) => {
        if ((node.type !== "Identifier" && node.type !== "MemberExpression") || !sameReference(node, state)) return false;
        if (stateBinding === undefined || resolve === undefined) return true;
        const root = rootIdentifier(node);
        const binding = root === undefined ? undefined : resolve(root);
        // Only a provably different variable (minified names reused in a nested function) is not the state.
        return binding === undefined || binding === stateBinding;
    };
};

/** The value in `S = value;` or `var S = value;` (single declarator). */
const stateAssignment = (statement: Node | undefined | null, isState: IsState): Expression | undefined => {
    if (statement?.type === "ExpressionStatement") {
        const e = statement.expression;
        if (e.type === "AssignmentExpression" && e.operator === "=" && isState(e.left)) return e.right;
    }
    if (statement?.type === "VariableDeclaration" && statement.kind === "var" && statement.declarations.length === 1) {
        const d = statement.declarations[0];
        if (d?.id.type === "Identifier" && d.init && isState(d.id)) return d.init;
    }
    return undefined;
};

/**
 * The loop init's state value plus everything else the init does, kept as statements in their original order.
 * `last`: the state is the init's final effect, so the rest can run first without reordering anything.
 */
const initAssignment = (init: NonNullable<ForStatement["init"]>, isState: IsState): { value: Expression; preamble: Statement[]; last: boolean } | undefined => {
    if (init.type === "VariableDeclaration") {
        if (init.kind !== "var") return undefined;
        const index = init.declarations.findIndex((d) => d.id.type === "Identifier" && isState(d.id));
        const declarator = init.declarations[index];
        if (declarator?.init === undefined || declarator.init === null) return undefined;
        const others = init.declarations.filter((_, i) => i !== index);
        return { value: declarator.init, preamble: others.length === 0 ? [] : [{ ...init, declarations: others }], last: index === init.declarations.length - 1 };
    }
    const expressions = init.type === "SequenceExpression" ? init.expressions : [init];
    const last = expressions.at(-1);
    if (last?.type !== "AssignmentExpression" || last.operator !== "=" || !isState(last.left)) return undefined;
    return { value: last.right, preamble: expressions.slice(0, -1).map((expression) => at<Statement>({ type: "ExpressionStatement", expression }, expression)), last: true };
};

/**
 * Whether `node` contains the state reference anywhere: reads, writes, closures. Names that aren't references (`o.S`,
 * `{ S: 1 }`, `S: for`, `break S`) don't count, even when they spell the state's name.
 */
const mentionsState = (node: Node, isState: IsState): boolean => {
    if (isState(node)) return true;
    switch (node.type) {
        case "MemberExpression":
            return mentionsState(node.object, isState) || (node.computed && mentionsState(node.property, isState));
        case "Property":
            return (node.computed && mentionsState(node.key, isState)) || mentionsState(node.value, isState);
        case "MethodDefinition":
        case "PropertyDefinition":
            return (
                node.decorators.some((decorator) => mentionsState(decorator, isState)) ||
                (node.computed && mentionsState(node.key, isState)) ||
                (node.value !== null && mentionsState(node.value, isState))
            );
        case "LabeledStatement":
            return mentionsState(node.body, isState);
        case "BreakStatement":
        case "ContinueStatement":
            return false;
        default: {
            let found = false;
            forEachChild(node, (child) => {
                if (!found && mentionsState(child, isState)) found = true;
            });
            return found;
        }
    }
};

/**
 * A `break`/`continue` inside a case body that targets the switch or the machine loop instead of something inside
 * the body. Such jumps skip the state update, so the case can't become a plain block.
 */
const escapingJump = (statements: readonly Statement[]): Node | undefined => {
    const labels: string[] = [];
    let loops = 0;
    let breakables = 0;
    let found: Node | undefined;
    const walk = (node: Node): void => {
        if (found !== undefined || isFunctionNode(node)) return;
        if (node.type === "LabeledStatement") {
            labels.push(node.label.name);
            walk(node.body);
            labels.pop();
            return;
        }
        if (node.type === "BreakStatement") {
            if (node.label ? !labels.includes(node.label.name) : breakables === 0) found = node;
            return;
        }
        if (node.type === "ContinueStatement") {
            if (node.label ? !labels.includes(node.label.name) : loops === 0) found = node;
            return;
        }
        const isLoop = isLoopNode(node);
        const isBreakable = isBreakTarget(node);
        if (isLoop) loops++;
        if (isBreakable) breakables++;
        forEachChild(node, walk);
        if (isLoop) loops--;
        if (isBreakable) breakables--;
    };
    for (const statement of statements) walk(statement);
    return found;
};

type KeyOf = (node: Node) => StateKey | undefined;

type TerminatorResult = { readonly ok: true; readonly terminator: Terminator } | Refusal;

/**
 * `(t ? a : b)[k]` (any member chain over a conditional) as `t ? a[k] : b[k]`: the same reads in the same order, so
 * each side is a state value of its own (`(7 === x ? T[31][14] : T[51][60])[19]`). Only ever keyed, never
 * emitted.
 */
const distribute = (node: Expression): (Expression & { type: "ConditionalExpression" }) | undefined => {
    if (node.type !== "MemberExpression") return undefined;
    const inner = node.object.type === "ConditionalExpression" ? node.object : distribute(node.object);
    if (inner === undefined) return undefined;
    return { ...inner, consequent: { ...node, object: inner.consequent }, alternate: { ...node, object: inner.alternate } };
};

/** `S = c ? a : b` (possibly nested) as a terminator over state keys, or the reason it can't be one. */
const terminatorOf = (value: Expression, isState: IsState, terminal: StateKey, known: (key: StateKey) => boolean, keyOf: KeyOf): TerminatorResult => {
    const distributed = distribute(value);
    if (distributed !== undefined) return terminatorOf(distributed, isState, terminal, known, keyOf);
    if (value.type === "ConditionalExpression") {
        if (mentionsState(value.test, isState)) return refuse("state-escapes", "next state depends on the current state", value.test);
        const consequent = terminatorOf(value.consequent, isState, terminal, known, keyOf);
        if (!consequent.ok) return consequent;
        const alternate = terminatorOf(value.alternate, isState, terminal, known, keyOf);
        if (!alternate.ok) return alternate;
        const [a, b] = [consequent.terminator, alternate.terminator];
        const test = value.test;
        // Both sides go to the same place: the test only runs for its effects.
        if (a.kind === "goto" && b.kind === "goto" && a.target === b.target) return { ok: true, terminator: { kind: "evaluate", expression: test, next: a } };
        // `t ? 3 : u ? 3 : 0` is `t || u ? 3 : 0`, and `t ? (u ? 3 : 0) : 0` is `t && u ? 3 : 0`: same tests, same order.
        const logical = (operator: "||" | "&&", right: Expression): Expression => at<Expression>({ type: "LogicalExpression", operator, left: test, right }, value);
        if (a.kind === "goto" && b.kind === "branch" && b.consequent.kind === "goto" && b.consequent.target === a.target)
            return { ok: true, terminator: { kind: "branch", test: logical("||", b.test), consequent: a, alternate: b.alternate } };
        if (b.kind === "goto" && a.kind === "branch" && a.alternate.kind === "goto" && a.alternate.target === b.target)
            return { ok: true, terminator: { kind: "branch", test: logical("&&", a.test), consequent: a.consequent, alternate: b } };
        return { ok: true, terminator: { kind: "branch", test, consequent: a, alternate: b } };
    }
    const key = keyOf(value);
    if (key === undefined) return refuse("non-constant-state", "next state is not a constant", value);
    if (key === terminal) return { ok: true, terminator: { kind: "goto", target: "exit" } };
    if (!known(key)) return refuse("non-constant-state", `next state ${key} has no case`, value);
    return { ok: true, terminator: { kind: "goto", target: key } };
};

/**
 * Recognise a control-flow-flattened loop and turn it into blocks with explicit successors:
 *
 *     var S = 2;                       // or for (var S = 2; ...)
 *     for (; S !== 9;) switch (S) {    // or 9 !== S
 *       case 2: ...; S = c ? 5 : 9; break;
 *       case 5: ...; return x;
 *     }
 *
 * Anything that doesn't fit exactly is refused, with the reason. `resolve` (optional) tells same-named variables apart;
 * `stateKey` (optional) gives keys to states the static evaluator can't (cyclic-array rows, by identity).
 *
 * Declarations are not judged here: what moving case code out of the switch does to them takes scope analysis
 * (`declarations.ts`).
 */
export const matchMachine = ({ loop, siblings, index, labeled }: MachineSite, resolve?: Resolve, stateKey?: KeyOf): MatchResult => {
    const keyOf: KeyOf = (node) => constantKey(node) ?? stateKey?.(node);
    if (loop.update !== null) return refuse("not-a-machine", "loop has an update clause");
    const test = loop.test;
    if (test?.type !== "BinaryExpression" || test.operator !== "!==") return refuse("not-a-machine", "loop test is not `S !== end`");

    const body = loop.body.type === "BlockStatement" && loop.body.body.length === 1 ? loop.body.body[0] : loop.body;
    if (body?.type !== "SwitchStatement") return refuse("not-a-machine", "loop body is not a single switch");
    const state = body.discriminant;
    if (state.type !== "Identifier" && state.type !== "MemberExpression") return refuse("shape", "switch is not on a variable", state);
    const terminalNode = sameReference(test.left, state) ? test.right : sameReference(test.right, state) ? test.left : undefined;
    if (terminalNode === undefined) return refuse("shape", "loop test and switch use different variables", test);
    const terminal = keyOf(terminalNode);
    if (terminal === undefined) return refuse("non-constant-state", "end state is not a constant", terminalNode);
    if (labeled) return refuse("shape", "machine loop is labeled", loop);
    const isState = stateMatcher(state, resolve);

    // Initial state: the loop's init clause, or the closest earlier sibling that assigns it. An init that doesn't
    // touch the state (`for (c.l49(); ...)`) just runs first: it becomes the preamble.
    let entryValue: Expression | undefined;
    let initializer: Statement | null = null;
    let preamble: Statement[] = [];
    // Whether evaluating the initial state where the machine starts, after the preamble, keeps every effect in order.
    let entryInPlace = false;
    if (loop.init !== null) {
        const found = initAssignment(loop.init, isState);
        if (found !== undefined) {
            const reordered = found.preamble.find((statement) => mentionsState(statement, isState));
            if (reordered) return refuse("state-escapes", "loop init uses the state besides setting it", reordered);
            entryValue = found.value;
            preamble = found.preamble;
            entryInPlace = found.last;
        } else {
            const init = loop.init;
            const statement = init.type === "VariableDeclaration" ? init : at<Statement>({ type: "ExpressionStatement", expression: init }, init);
            if (mentionsState(statement, isState)) return refuse("shape", "loop init doesn't set the state", init);
            preamble = [statement];
        }
    }
    if (entryValue === undefined) {
        if (siblings === null || index === null) return refuse("shape", "machine is not in a statement list, can't find its initial state", loop);
        for (let i = index - 1; i >= 0; i--) {
            const sibling = siblings[i];
            if (sibling === undefined) break;
            const value = stateAssignment(sibling, isState);
            if (value !== undefined) {
                entryValue = value;
                initializer = sibling;
                entryInPlace = i === index - 1 && preamble.length === 0;
                break;
            }
            if (mentionsState(sibling, isState)) return refuse("state-escapes", "state is used between its initialization and the loop", sibling);
        }
        if (entryValue === undefined) return refuse("shape", "no initial state before the loop", loop);
    }

    const keys = new Map<StateKey, SwitchCase>();
    const duplicates: SwitchCase[] = [];
    for (const switchCase of body.cases) {
        if (switchCase.test === null) return refuse("shape", "switch has a default case", switchCase);
        const key = keyOf(switchCase.test);
        if (key === undefined) return refuse("non-constant-state", "case label is not a constant", switchCase.test);
        if (keys.has(key)) duplicates.push(switchCase);
        else keys.set(key, switchCase);
    }
    const known = (key: StateKey) => keys.has(key);

    // The initial state, like any transition: a constant, or a choice between constants (`c() ? T[43][5] : T[39][52]`).
    const start = terminatorOf(entryValue, isState, terminal, known, keyOf);
    if (!start.ok) return refuse(start.code, `initial state: ${start.reason}`, start.node);
    const blocks = new Map<StateKey, Block>();
    let entry: StateKey | "exit";
    if (start.terminator.kind === "goto") entry = start.terminator.target;
    else {
        // Its tests run where the machine starts, so they must have run there, right before the loop, in the original.
        if (!entryInPlace) return refuse("shape", "computed initial state isn't set right before the loop", entryValue);
        entry = ENTRY;
        blocks.set(ENTRY, { key: ENTRY, statements: [], dead: [], terminator: start.terminator, origin: null });
    }
    for (const [caseIndex, switchCase] of body.cases.entries()) {
        const key = keyOf(switchCase.test as Expression) as StateKey;
        if (keys.get(key) !== switchCase) continue; // duplicate label, never reached

        const all = switchCase.consequent.filter((statement) => statement.type !== "FunctionDeclaration");
        const lastStatement = all.at(-1);
        const endsWithBreak = lastStatement?.type === "BreakStatement" && lastStatement.label === null;
        if (endsWithBreak) all.pop();
        // Nothing after a case-level `return`/`throw` runs: not a transition, not a fall-through.
        const end = all.findIndex((statement) => statement.type === "ReturnStatement" || statement.type === "ThrowStatement");
        const statements = end === -1 ? all : all.slice(0, end + 1);
        const dead = end === -1 ? [] : all.slice(end + 1);
        const jump = escapingJump(statements);
        if (jump) return refuse("escaping-jump", "case body jumps out of the switch early", jump);

        // Either a fixed terminator, or the value the case assigns to the state (`transition`).
        let terminator: Terminator | undefined;
        let transition: Expression | undefined;
        const tail = statements.at(-1);
        const value = stateAssignment(tail, isState);
        if (tail?.type === "ReturnStatement" || tail?.type === "ThrowStatement") {
            terminator = { kind: "end" };
        } else if (value !== undefined) {
            if (!endsWithBreak) return refuse("shape", "case sets the state and falls through", switchCase);
            statements.pop();
            transition = value;
        } else if (
            endsWithBreak &&
            tail?.type === "VariableDeclaration" &&
            tail.kind === "var" &&
            tail.declarations.length > 1 &&
            tail.declarations.at(-1)?.id.type === "Identifier" &&
            isState(tail.declarations.at(-1)?.id as Node) &&
            tail.declarations.at(-1)?.init
        ) {
            // `var c = f(), S = 4; break;` (minified): the last declarator is the transition, the rest stays.
            const declarator = tail.declarations.at(-1) as NonNullable<(typeof tail.declarations)[number]>;
            statements[statements.length - 1] = { ...tail, declarations: tail.declarations.slice(0, -1) };
            transition = declarator.init as Expression;
        } else if (tail?.type === "ExpressionStatement" && tail.expression.type === "SequenceExpression" && endsWithBreak) {
            const expressions = tail.expression.expressions;
            const lastExpression = expressions.at(-1);
            const seqValue = lastExpression?.type === "AssignmentExpression" && lastExpression.operator === "=" && isState(lastExpression.left) ? lastExpression.right : undefined;
            if (seqValue === undefined) {
                terminator = { kind: "goto", target: key };
            } else {
                const rest = expressions.slice(0, -1);
                statements[statements.length - 1] = { ...tail, expression: rest.length === 1 ? (rest[0] as Expression) : { ...tail.expression, expressions: rest } };
                transition = seqValue;
            }
        } else if (endsWithBreak) {
            // `break` without a state change dispatches the same state again.
            terminator = { kind: "goto", target: key };
        } else {
            // No break: falls through into the next case's body.
            const next = body.cases[caseIndex + 1];
            if (next === undefined) return refuse("shape", "last case falls off the switch without setting the state", switchCase);
            const nextKey = keyOf(next.test as Expression) as StateKey;
            if (keys.get(nextKey) !== next) return refuse("shape", "case falls through into a case with a duplicate label", switchCase);
            terminator = { kind: "goto", target: nextKey };
        }
        if (transition !== undefined) {
            const result = terminatorOf(transition, isState, terminal, known, keyOf);
            if (!result.ok) return result;
            terminator = result.terminator;
        }
        if (terminator === undefined) return refuse("shape", "case has no recognisable transition", switchCase);

        for (const statement of statements) if (mentionsState(statement, isState)) return refuse("state-escapes", "state is used inside a case body", statement);
        // Case-level function declarations aren't in `statements`, but they can still close over the state.
        for (const statement of switchCase.consequent)
            if (statement.type === "FunctionDeclaration" && mentionsState(statement, isState)) return refuse("state-escapes", "state is used inside a case body", statement);
        blocks.set(key, { key, statements, dead, terminator, origin: switchCase });
    }

    return { ok: true, machine: { state, entry, blocks, dispatch: body, duplicates, initializer, preamble } };
};
