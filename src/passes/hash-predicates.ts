import type { Expression, ForStatement, IfStatement, Node, Statement, VariableDeclaration, WhileStatement } from "../core/ast.js";
import { memberPath } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import type { EvaluateEnv, Evaluation, Value } from "../core/evaluate.js";
import { evaluate, FAIL, value } from "../core/evaluate.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { forEachChild, traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { builderOf, definitionOf } from "./emulate/builders.js";
import type { StorageAnalysis } from "./emulate/effects.js";
import { storageAnalysis } from "./emulate/effects.js";
import type { PropertyPath } from "./emulate/guest.js";
import type { RuntimeModel } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import { PurityProver } from "./hash-purity.js";

/** A loop is simulated for at most this many iterations. */
const MAX_ITERATIONS = 10_000;

/** Compound assignment operators and the binary operator each applies. */
const COMPOUND: ReadonlyMap<string, string> = new Map(["+=", "-=", "*=", "/=", "%=", "**=", "<<=", ">>=", ">>>=", "&=", "|=", "^="].map((op) => [op, op.slice(0, -1)]));

type Predicate = IfStatement | ForStatement | WhileStatement;

/** Known values of locals at a point of a statement list. */
type Env = Map<Variable, Value>;

const samePath = (a: PropertyPath, b: PropertyPath): boolean => a.length === b.length && a.every((key, i) => key === b[i]);

/** The statements an expression statement's assignments are applied by: a sequence's items, or the expression itself. */
const itemsOf = (expression: Expression): readonly Expression[] => (expression.type === "SequenceExpression" ? expression.expressions : [expression]);

/** Names something in `node` writes (assignment and update targets, initialised or lexical declarations, loop heads). */
const writtenNames = (node: Node): Set<string> => {
    const names = new Set<string>();
    traverse(node, {
        Identifier(path) {
            const parent = path.parent;
            const declared = parent?.type === "VariableDeclarator" && path.key === "id" && (parent.init !== null || node.type !== "VariableDeclaration" || node.kind !== "var");
            if (declared || path.isWriteTarget()) names.add(path.node.name);
        },
    });
    return names;
};

/**
 * How the walk over a list goes on after a predicate: `walk` the statements that replaced it, `skip` that many
 * statements (what they leave is in the env already), or else apply the predicate statement itself.
 */
interface Next {
    readonly walk?: true;
    readonly skip?: number;
}

const NO_FINAL = "a local the loop writes has no known final value";

const replaceAll = (env: Env, from: Env): void => {
    env.clear();
    for (const [variable, known] of from) env.set(variable, known);
};

/** Whether code in `node` (outside nested functions) may leave a loop iteration early: `break` or `continue`. */
const jumpsOut = (node: Node): boolean => {
    if (node.type === "BreakStatement" || node.type === "ContinueStatement") return true;
    if (node.type === "FunctionExpression" || node.type === "FunctionDeclaration" || node.type === "ArrowFunctionExpression") return false;
    let found = false;
    forEachChild(node, (child) => {
        found ||= jumpsOut(child);
    });
    return found;
};

const statementOf = (expression: Expression): Statement => at<Statement>({ type: "ExpressionStatement", expression }, expression);

/**
 * A loop that runs once as straight-line code: its init, its body (in a block when it declares block-scoped names)
 * and its update, in that order. Not when the body may jump out of the iteration, or the init is block-scoped.
 */
const onceUnrolled = (loop: ForStatement | WhileStatement): Statement[] | string => {
    if (jumpsOut(loop.body)) return "it runs once, but its body may break or continue";
    const init = loop.type === "ForStatement" ? loop.init : null;
    if (init?.type === "VariableDeclaration" && init.kind !== "var") return "it runs once, but its init is block-scoped";
    const statements: Statement[] = init === null ? [] : [init.type === "VariableDeclaration" ? init : statementOf(init)];
    const body = loop.body;
    const scoped = body.type === "BlockStatement" && body.body.some((s) => (s.type === "VariableDeclaration" && s.kind !== "var") || s.type === "ClassDeclaration" || s.type === "FunctionDeclaration");
    statements.push(...(body.type === "BlockStatement" && !scoped ? body.body : [body]));
    if (loop.type === "ForStatement" && loop.update !== null) statements.push(statementOf(loop.update));
    return statements;
};

/**
 * Hash opaque predicates: jscrambler's `if`s and loops whose test compares a pure hash of a local's digits with a
 * constant, around straight-line assignments of those locals:
 *
 *     a = 576049076; O = 1928372057; S = 2;
 *     for (var d = 1; G.U.h(d.toString(), d.toString().length, 77300) !== a; d++) { S += 2; }
 *     if (G.U.h(S.toString(), S.toString().length, 42066) !== O) { decoy(); }
 *
 * A test is decided by evaluating it: the hash is a method a prelude builder put on the storage object (reached
 * directly or through a wrapper, read where nothing changes it after the prelude, still the function the builder
 * made), proven pure (`PurityProver`), and run in the guest with the arguments' values, which must repeat. Some
 * builds add clauses comparing the runtime's cyclic-array rows by identity (unflatten's runtime state keys).
 *
 * Locals' values come from a forward pass over the statement list holding the predicate: assignments and declarations
 * of constants set them, any other write (by name, for nodes the scope analysis doesn't know) forgets them. Only
 * locals no closure captures are followed (of their own function, declared by `var`/`let`/`const`), so a call in
 * between can't change them; and none in a program with `with`.
 *
 * Then an `if`'s test becomes its value (simplify drops the dead branch); a loop whose test is false at once gets the
 * test `false` (simplify keeps its init); a loop that runs N times, whose body and update only set followed locals to
 * values that evaluate, is replaced by the final values of what it writes; a loop that runs once with any other body
 * becomes that iteration's code. Anything else stays, with its reason logged. Relies on model 7: builtins intact (the
 * guest's hash runs on the standard builtins, `n.toString()` is the standard conversion).
 */
export const hashPredicates: Pass = {
    name: "hash-predicates",
    description: "Decide opaque predicates built on the runtime's pure hash function",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || runtime.guest.broken !== undefined) {
            log.info("no usable runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        if (!anyPureMethod(runtime, scopes)) {
            log.info("no method a prelude builder made is a pure hash, no hash predicates");
            return { changed: 0 };
        }
        const analysis = storageAnalysis(program, runtime, scopes, log);
        const hashes = new HashFunctions(runtime, analysis, scopes, log);
        const lists = new Map<Statement[], Set<Statement>>();
        traverse(program, {
            enter(path) {
                const node = path.node;
                if ((node.type !== "IfStatement" && node.type !== "ForStatement" && node.type !== "WhileStatement") || node.test === null || !path.isInStatementList()) return;
                if (!hashes.mentionedIn(node.test)) return;
                const parent = path.parent;
                const list = (parent?.type === "SwitchCase" ? parent.consequent : (parent as { body: Statement[] }).body) as Statement[];
                lists.set(list, (lists.get(list) ?? new Set()).add(node));
            },
        });
        if (lists.size === 0) {
            log.info("no hash predicates found");
            return { changed: 0 };
        }
        const hasWith = scopes.manager.scopes.some((s) => s.type === "with");
        const folder = new Folder(runtime, analysis, hashes, scopes, log, facts, hasWith);
        // Inner lists first (the walk found them after the lists holding them): unrolling an outer loop moves its body's
        // statements into the outer list, and the inner list is then decided already.
        for (const [list, predicates] of [...lists].toReversed()) folder.scan(list, predicates);

        const { counts, refusals } = folder;
        const kept = [...refusals].map(([reason, count]) => `${count} (${reason})`).join(", ");
        log.info(`decided ${counts.ifs} if test(s), ${counts.neverRun} loop(s) that never run, ${counts.unrolled} loop(s) replaced by their final values; kept ${kept || "none"}`);
        const changed = counts.ifs + counts.neverRun + counts.unrolled;
        // Decided tests become literals; unrolled loops reuse their own nodes (`#finals`, `onceUnrolled`): no binding changes.
        return { changed, bindingsChanged: false, stats: { ...counts, kept: [...refusals.values()].reduce((sum, n) => sum + n, 0) } };
    },
};

/**
 * Whether some method a prelude builder made may be a pure hash: a plain function of the builder of a
 * `G.k = (function () {...})()` statement the guest ran, among the methods the guest saw it build, proven pure. Every
 * hash `HashFunctions.targetOf` finds is one; without any, no test can be decided and the program isn't searched.
 * The proofs use a prover of their own, so the ones the search makes don't depend on these.
 */
const anyPureMethod = (runtime: RuntimeModel, scopes: ScopeInfo): boolean => {
    const prover = new PurityProver(scopes);
    for (const [statement, identities] of runtime.built) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") continue;
        const right = statement.expression.right;
        if (right.type !== "CallExpression" || right.callee.type !== "FunctionExpression" || right.arguments.length > 0) continue;
        const iife = right.callee;
        const builder = builderOf(iife, scopes);
        if (typeof builder === "string") continue;
        for (const [name, fn] of builder.methods) if (identities.methods.has(name) && prover.impurity(fn, iife) === undefined) return true;
    }
    return false;
};

/** Calls of the runtime's pure hash functions: which callees are such, and their values for known arguments. */
class HashFunctions {
    readonly #runtime: RuntimeModel;
    readonly #analysis: StorageAnalysis;
    readonly #scopes: ScopeInfo;
    readonly #log: PassContext["log"];
    readonly #prover: PurityProver;
    /** By callee path: the hash's path on the storage object, or why the callee isn't one. */
    readonly #targets = new Map<string, PropertyPath | string>();
    readonly #results = new Map<string, Evaluation>();

    constructor(runtime: RuntimeModel, analysis: StorageAnalysis, scopes: ScopeInfo, log: PassContext["log"]) {
        this.#runtime = runtime;
        this.#analysis = analysis;
        this.#scopes = scopes;
        this.#log = log;
        this.#prover = new PurityProver(scopes);
    }

    /** Whether `node` calls a pure hash function somewhere (not inside nested functions). */
    mentionedIn(node: Node): boolean {
        if (node.type === "CallExpression" && typeof this.targetOf(node.callee) !== "string") return true;
        if (node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression") return false;
        let found = false;
        forEachChild(node, (child) => {
            found ||= this.mentionedIn(child);
        });
        return found;
    }

    /** The hash a callee reaches (directly or through a wrapper), or why it isn't one. */
    targetOf(callee: Node): PropertyPath | string {
        const path = memberPath(callee);
        if (path === undefined || !this.#analysis.matcher.isStorage(path.root)) return "not a call on the storage object";
        const id = JSON.stringify(path.keys);
        let target = this.#targets.get(id);
        if (target === undefined) {
            target = this.#resolveTarget(path.keys);
            this.#targets.set(id, target);
            const name = `${this.#runtime.storage}.${path.keys.join(".")}`;
            this.#log.debug(typeof target === "string" ? `${name} isn't a pure hash: ${target}` : `${name} is a pure hash`, callee);
        }
        return target;
    }

    #resolveTarget(keys: PropertyPath): PropertyPath | string {
        const [first] = keys;
        const wrapper = keys.length === 1 && first !== undefined ? this.#runtime.wrappers.get(first) : undefined;
        const target = wrapper?.target ?? keys;
        if (wrapper !== undefined && (wrapper.receiver === undefined || !samePath(wrapper.receiver, target.slice(0, -1)))) return "its wrapper applies it to another this";
        const name = target.at(-1);
        if (target.length < 2 || name === undefined) return "it isn't a method of a holder the prelude built";
        const definition = definitionOf(this.#runtime, this.#analysis.matcher.isStorage, target.slice(0, -1));
        if (typeof definition === "string") return definition;
        const builder = builderOf(definition.iife, this.#scopes);
        if (typeof builder === "string") return builder;
        const fn = builder.methods.get(name);
        if (fn === undefined) return `its builder gives it no plain function ${name}`;
        const built = this.#runtime.built.get(definition.statement)?.methods.get(name);
        if (built === undefined || this.#runtime.guest.stateKey(target) !== `o:${built}`) return "the guest no longer holds the builder's function there";
        const impure = this.#prover.impurity(fn, definition.iife);
        return impure === undefined ? target : `it isn't pure: ${impure}`;
    }

    /**
     * The value of a call of a pure hash, with its arguments evaluated by `evaluateIn`; `reason` gets why not. The
     * call's reads (wrapper, hash) must see the snapshot's values, and the guest's answer must repeat.
     */
    valueOf(call: Node & { type: "CallExpression" }, evaluateIn: (node: Node) => Evaluation, reason: (why: string) => void): Evaluation {
        const target = this.targetOf(call.callee);
        const path = memberPath(call.callee);
        if (typeof target === "string" || path === undefined) return FAIL;
        const stale = this.#analysis.effects.staleAt(path.root, path.keys) ?? this.#analysis.effects.staleAt(path.root, target);
        if (stale !== undefined) {
            reason(stale.reason);
            return FAIL;
        }
        const args: Value[] = [];
        for (const arg of call.arguments) {
            const known = arg.type === "SpreadElement" ? FAIL : evaluateIn(arg);
            if (!known.ok) {
                reason("an argument of the hash isn't known");
                return FAIL;
            }
            args.push(known.value);
        }
        const id = JSON.stringify([target, args]);
        let result = this.#results.get(id);
        if (result === undefined) {
            const [answer] = this.#runtime.guest.resolve([{ path: target, args }]);
            result = answer !== undefined && answer.ok && "value" in answer && answer.repeatable ? value(answer.value) : FAIL;
            this.#results.set(id, result);
        }
        if (!result.ok) reason("the guest's hash doesn't answer");
        return result;
    }
}

/** The forward pass over statement lists holding predicates, and the folds. */
class Folder {
    readonly counts = { ifs: 0, neverRun: 0, unrolled: 0 };
    readonly refusals = new Map<string, number>();
    readonly #runtime: RuntimeModel;
    readonly #analysis: StorageAnalysis;
    readonly #hashes: HashFunctions;
    readonly #scopes: ScopeInfo;
    readonly #log: PassContext["log"];
    readonly #facts: PassContext["facts"];
    readonly #hasWith: boolean;
    /** Per variable, whether its values are followed (see `#followed`). */
    readonly #followedCache = new Map<Variable, boolean>();

    constructor(runtime: RuntimeModel, analysis: StorageAnalysis, hashes: HashFunctions, scopes: ScopeInfo, log: PassContext["log"], facts: PassContext["facts"], hasWith: boolean) {
        this.#runtime = runtime;
        this.#analysis = analysis;
        this.#hashes = hashes;
        this.#scopes = scopes;
        this.#log = log;
        this.#facts = facts;
        this.#hasWith = hasWith;
    }

    /** Walk `list` up to its last predicate, following locals' values and deciding each predicate. */
    scan(list: Statement[], predicates: ReadonlySet<Statement>): void {
        const env: Env = new Map();
        let left = predicates.size;
        for (let i = 0; i < list.length && left > 0; i++) {
            const statement = list[i] as Statement;
            if (predicates.has(statement)) {
                left--;
                const next = this.#decide(statement as Predicate, env, list);
                if (next.walk) {
                    i--; // the replacement statements are the program's own: walk them
                    continue;
                }
                if (next.skip !== undefined) {
                    i += next.skip - 1; // `env` already holds what they leave
                    continue;
                }
            }
            this.#transfer(statement, env);
        }
    }

    /** A local whose value only its own function's statements set: declared by `var`/`let`/`const`, no closure reads it. */
    #followed(variable: Variable): boolean {
        let known = this.#followedCache.get(variable);
        if (known === undefined) {
            const scope = variable.scope;
            known =
                !this.#hasWith &&
                scope.type !== "global" &&
                scope.type !== "module" &&
                variable.defs.length > 0 &&
                variable.defs.every((def) => def.type === "Variable") &&
                this.#scopes.staticReferences(variable).every((reference) => reference.from.variableScope === scope.variableScope);
            this.#followedCache.set(variable, known);
        }
        return known;
    }

    #variableOf(node: Node): Variable | undefined {
        const variable = node.type === "Identifier" ? this.#scopes.variableOf(node) : undefined;
        return variable !== undefined && this.#followed(variable) ? variable : undefined;
    }

    /** Evaluation with followed locals, `x.toString()` of known primitives (model 7), hash calls and the runtime's state. */
    #evaluator(env: Env, reason: (why: string) => void): (node: Node) => Evaluation {
        const evaluateIn = (node: Node): Evaluation => evaluate(node, hooks);
        const hooks: EvaluateEnv = {
            isGlobal: (id) => this.#scopes.isGlobalReference(id),
            lookup: (node) => {
                switch (node.type) {
                    case "Identifier": {
                        const variable = this.#variableOf(node);
                        return variable !== undefined && env.has(variable) ? value(env.get(variable)) : FAIL;
                    }
                    case "CallExpression": {
                        const callee = node.callee;
                        if (callee.type === "MemberExpression" && !callee.computed && callee.property.type === "Identifier" && callee.property.name === "toString" && node.arguments.length === 0) {
                            const receiver = evaluateIn(callee.object);
                            return receiver.ok && (typeof receiver.value === "number" || typeof receiver.value === "string" || typeof receiver.value === "boolean")
                                ? value(String(receiver.value))
                                : FAIL;
                        }
                        return this.#hashes.valueOf(node, evaluateIn, reason);
                    }
                    case "MemberExpression": {
                        const key = this.#stateKey(node, reason);
                        if (key?.startsWith("n:")) return value(Number(key.slice(2)));
                        return key?.startsWith("s:") ? value(key.slice(2)) : FAIL;
                    }
                    case "BinaryExpression":
                        return this.#identity(node, reason);
                    default:
                        return FAIL;
                }
            },
        };
        return evaluateIn;
    }

    /** The guest's state key for a constant-key chain on the storage object nothing changes after the prelude. */
    #stateKey(node: Node, reason: (why: string) => void): string | undefined {
        const path = memberPath(node);
        if (path === undefined || !this.#analysis.matcher.isStorage(path.root)) return undefined;
        const stale = this.#analysis.effects.staleAt(path.root, path.keys);
        if (stale !== undefined) {
            reason(stale.reason);
            return undefined;
        }
        return this.#runtime.guest.stateKey(path.keys);
    }

    /** `R1 == R2` (also `!=`, `===`, `!==`) for two of the runtime's objects (cyclic-array rows): by identity. */
    #identity(node: Node & { type: "BinaryExpression" }, reason: (why: string) => void): Evaluation {
        const { operator } = node;
        if (operator !== "==" && operator !== "!=" && operator !== "===" && operator !== "!==") return FAIL;
        const left = this.#stateKey(node.left, reason);
        const right = this.#stateKey(node.right, reason);
        if (left === undefined || right === undefined || !left.startsWith("o:") || !right.startsWith("o:")) return FAIL;
        return value((left === right) === (operator === "==" || operator === "==="));
    }

    /** Apply a statement to `env`: assignments of values that evaluate set locals, any other write forgets them. */
    #transfer(statement: Statement, env: Env): void {
        if (statement.type === "ExpressionStatement") {
            for (const item of itemsOf(statement.expression)) this.#assign(item, env);
            return;
        }
        if (statement.type === "VariableDeclaration") {
            this.#declare(statement, env);
            return;
        }
        this.#forget(writtenNames(statement), env);
    }

    #forget(names: ReadonlySet<string>, env: Env): void {
        if (names.size === 0) return;
        for (const variable of env.keys()) if (names.has(variable.name)) env.delete(variable);
    }

    /** Apply one assignment or update; returns whether it set a followed local to a known value. */
    #assign(expression: Expression, env: Env): boolean {
        const evaluateIn = this.#evaluator(env, () => undefined);
        let target: Node | undefined;
        let result: Evaluation = FAIL;
        if (expression.type === "AssignmentExpression" && expression.left.type === "Identifier") {
            target = expression.left;
            const operator = COMPOUND.get(expression.operator);
            if (expression.operator === "=") result = evaluateIn(expression.right);
            else if (operator !== undefined) result = evaluateIn(at({ type: "BinaryExpression", operator, left: expression.left, right: expression.right }, expression));
        } else if (expression.type === "UpdateExpression" && expression.argument.type === "Identifier") {
            target = expression.argument;
            const old = evaluateIn(target);
            if (old.ok && typeof old.value === "number") result = value(expression.operator === "++" ? old.value + 1 : old.value - 1);
        }
        this.#forget(writtenNames(expression), env);
        const variable = target === undefined ? undefined : this.#variableOf(target);
        if (variable === undefined || !result.ok) return false;
        env.set(variable, result.value);
        return true;
    }

    /** Apply a declaration; returns whether every declarator set a followed local to a known value. */
    #declare(declaration: VariableDeclaration, env: Env): boolean {
        let all = true;
        for (const declarator of declaration.declarations) {
            const variable = this.#variableOf(declarator.id);
            const result = declarator.init === null ? (declaration.kind === "var" ? undefined : value(undefined)) : this.#evaluator(env, () => undefined)(declarator.init);
            if (declarator.init !== null || declaration.kind !== "var") this.#forget(writtenNames(declarator), env);
            if (variable !== undefined && result?.ok === true) env.set(variable, result.value);
            else if (result !== undefined) all = false;
        }
        return all;
    }

    #refuse(reason: string, node: Node): Next {
        this.refusals.set(reason, (this.refusals.get(reason) ?? 0) + 1);
        this.#log.debug(`kept: ${reason}`, node);
        return {};
    }

    /** Decide a predicate of `list` with the values in `env`; how the walk goes on (see `Next`). */
    #decide(predicate: Predicate, env: Env, list: Statement[]): Next {
        let why = "its test reads something whose value isn't known";
        const reason = (text: string): void => {
            why = text;
        };
        if (predicate.type === "IfStatement") {
            const test = this.#evaluator(env, reason)(predicate.test);
            if (!test.ok) return this.#refuse(why, predicate);
            predicate.test = valueToNode(Boolean(test.value), predicate.test);
            this.counts.ifs++;
            this.#log.debug(`if test is ${String(Boolean(test.value))}`, predicate);
            return {};
        }
        return this.#loop(predicate, env, list, reason, () => why);
    }

    /**
     * Run a loop on known values. Never runs: its test becomes `false` (its init stays). Runs N times with a body that
     * only sets followed locals to known values: replaced by what it leaves (`#finals`). Runs once with any other body
     * that can't jump out of the iteration (no `break`/`continue`): replaced by its init, body and update, in order.
     */
    #loop(loop: ForStatement | WhileStatement, env: Env, list: Statement[], reason: (why: string) => void, why: () => string): Next {
        const test = loop.test;
        if (test === null) return {};
        const local: Env = new Map(env);
        const init = loop.type === "ForStatement" ? loop.init : null;
        if (init !== null && !(init.type === "VariableDeclaration" ? this.#declare(init, local) : itemsOf(init).every((item) => this.#assign(item, local)))) {
            return this.#refuse("its init doesn't set known values", loop);
        }
        const body = loop.body.type === "BlockStatement" ? loop.body.body : [loop.body];
        const update = loop.type === "ForStatement" ? loop.update : null;
        // Counting: every iteration so far only set followed locals to known values. A loop that did more may run once.
        let counting = true;
        const evaluateIn = this.#evaluator(local, reason);
        let iterations = 0;
        for (;;) {
            const decided = evaluateIn(test);
            if (!decided.ok) return this.#refuse(why(), loop);
            if (!decided.value) break;
            if (iterations === MAX_ITERATIONS) return this.#refuse(`it runs more than ${MAX_ITERATIONS} times`, loop);
            for (const statement of body) counting = this.#apply(statement, local) && counting;
            if (update !== null) for (const item of itemsOf(update)) counting = this.#assign(item, local) && counting;
            iterations++;
            if (!counting && iterations > 1) return this.#refuse("it runs more than once, and its body does more than set locals to known values", loop);
        }
        if (iterations === 0) {
            loop.test = valueToNode(false, test);
            replaceAll(env, local);
            this.counts.neverRun++;
            this.#log.debug("the loop never runs", loop);
            return { skip: 1 };
        }
        const replacement = counting ? this.#finals(loop, local) : onceUnrolled(loop);
        if (typeof replacement === "string") return this.#refuse(replacement, loop);
        this.#facts.replaced([loop], replacement);
        list.splice(list.indexOf(loop), 1, ...replacement);
        this.counts.unrolled++;
        this.#log.debug(`the loop runs ${iterations} time(s): replaced by ${counting ? "its final values" : "its one iteration"}`, loop);
        if (!counting) return { walk: true };
        replaceAll(env, local);
        return { skip: replacement.length };
    }

    /** Apply a statement of a loop's body to `env`; whether it only set followed locals to known values. */
    #apply(statement: Statement, env: Env): boolean {
        if (statement.type !== "ExpressionStatement") {
            this.#transfer(statement, env);
            return false;
        }
        let known = true;
        for (const item of itemsOf(statement.expression)) known = this.#assign(item, env) && known;
        return known;
    }

    /**
     * What a loop that ran (to `local`) leaves: its `var` init declaring the final values, then the final value of each
     * other local it writes. A lexical init lives only in the loop. A reason instead when a final value isn't known.
     * The loop's own nodes are reused (its declarators get their final values, its first write of each other local
     * becomes that local's assignment), so the scope analysis knows every reference in the result: no binding changes.
     */
    #finals(loop: ForStatement | WhileStatement, local: Env): Statement[] | string {
        const finalOf = (node: Node): Expression | undefined => {
            const variable = this.#variableOf(node);
            return variable === undefined || !local.has(variable) ? undefined : valueToNode(local.get(variable), node);
        };
        const declared = new Set<string>();
        const init = loop.type === "ForStatement" ? loop.init : null;
        const declaration = init?.type === "VariableDeclaration" ? init : undefined;
        for (const declarator of declaration?.declarations ?? []) if (declarator.id.type === "Identifier") declared.add(declarator.id.name);
        // A `var` init keeps its declarators, each with its final value.
        const declaredFinals = declaration?.kind === "var" ? declaration.declarations.map((declarator) => finalOf(declarator.id)) : [];
        if (declaredFinals.some((final) => final === undefined)) return NO_FINAL;
        const written = new Map<string, Node>();
        const body = loop.body.type === "BlockStatement" ? loop.body.body : [loop.body];
        const update = loop.type === "ForStatement" ? loop.update : null;
        for (const part of [...(init === null || declaration !== undefined ? [] : [init]), ...body, ...(update === null ? [] : [update])]) {
            traverse(part, {
                Identifier(path) {
                    if (path.isWriteTarget() && !declared.has(path.node.name) && !written.has(path.node.name)) written.set(path.node.name, path.node);
                },
            });
        }
        const writtenFinals = [...written.values()].map((node) => [node, finalOf(node)] as const);
        if (writtenFinals.some(([, final]) => final === undefined)) return NO_FINAL;
        // Every final is known: only now the loop's nodes are taken apart.
        const statements: Statement[] = [];
        if (declaration?.kind === "var") {
            for (const [i, declarator] of declaration.declarations.entries()) declarator.init = declaredFinals[i] as Expression;
            statements.push(declaration);
        }
        for (const [node, final] of writtenFinals) {
            const assignment = at<Expression>({ type: "AssignmentExpression", operator: "=", left: node as Expression, right: final as Expression }, loop);
            statements.push(at<Statement>({ type: "ExpressionStatement", expression: assignment }, loop));
        }
        return statements;
    }
}
