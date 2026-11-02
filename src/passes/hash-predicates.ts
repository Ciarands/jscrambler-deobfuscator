import type { Expression, ForStatement, Function as FunctionNode, FunctionLike, IdentifierReference, IfStatement, Node, Statement, VariableDeclaration, WhileStatement } from "../core/ast.js";
import { memberPath } from "../core/ast.js";
import { at, valueToNode } from "../core/build.js";
import type { EvaluateEnv, Evaluation, Value } from "../core/evaluate.js";
import { evaluate, FAIL, value } from "../core/evaluate.js";
import type { OuterBinding } from "../core/interpret.js";
import { argumentsKey, Interpreter } from "../core/interpret.js";
import { pushAll, sameItems, spliceList } from "../core/list.js";
import type { ScopeInfo, Variable } from "../core/scope.js";
import { forEachChild, traverse, walkSkippingFunctions } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import { builderOf, definitionOf } from "./runtime/builders.js";
import type { StorageAnalysis } from "./runtime/effects.js";
import { storageAnalysis } from "./runtime/effects.js";
import type { PropertyPath, RuntimeModel } from "./runtime/model.js";
import { RUNTIME } from "./runtime/model.js";
import { rootStatements, storageMatcher } from "./runtime/storage.js";
import { PurityProver } from "./hash-purity.js";

const MAX_ITERATIONS = 10_000;

/** Interpreter steps one hash call may take, and all of one run's calls together (past it: partial output). */
const CALL_STEPS = 1_000_000;
const TOTAL_STEPS = 20_000_000;

/** The globals `PurityProver` lets a hash read (`Math`'s exact members, `String.prototype.charCodeAt.bind`). */
const HASH_GLOBALS: ReadonlySet<string> = new Set(["undefined", "NaN", "Infinity", "Math", "String"]);

const COMPOUND: ReadonlyMap<string, string> = new Map(["+=", "-=", "*=", "/=", "%=", "**=", "<<=", ">>=", ">>>=", "&=", "|=", "^="].map((op) => [op, op.slice(0, -1)]));

type Predicate = IfStatement | ForStatement | WhileStatement;

type Env = Map<Variable, Value>;

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

const jumpsOut = (node: Node): boolean => {
    let found = false;
    walkSkippingFunctions(node, (child) => {
        if (child.type === "BreakStatement" || child.type === "ContinueStatement") found = true;
        return !found;
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
    pushAll(statements, body.type === "BlockStatement" && !scoped ? body.body : [body]);
    if (loop.type === "ForStatement" && loop.update !== null) statements.push(statementOf(loop.update));
    return statements;
};

/**
 * Hash opaque predicates: `if`s and loops whose test compares a pure hash of a local's digits with a constant:
 *
 *     for (var d = 1; G.U.h(d.toString(), d.toString().length, 77300) !== a; d++) { S += 2; }
 *
 * The hash is a prelude-built storage method, read where nothing changes it after the prelude, proven pure
 * (`PurityProver`) and interpreted over its AST on the host (`Interpreter`). Locals' values come from a forward pass over the
 * statement list; only locals no closure captures are followed, so a call in between can't change them, and none
 * in a program with `with`. Some builds add clauses comparing the runtime's cyclic-array rows by identity. Relies on
 * model 7 (builtins intact).
 */
export const hashPredicates: Pass = {
    name: "hash-predicates",
    description: "Decide opaque predicates built on the runtime's pure hash function",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined) {
            log.info("no runtime, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        if (!anyPureMethod(runtime, storageMatcher(program, runtime, scopes).isStorage, scopes)) {
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
        const folder = new Folder(analysis, hashes, scopes, log, facts, hasWith);
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
 * Whether some method a root builder `G.k = (function () {...})()` makes may be a pure hash; without one no test can be
 * decided. Uses its own prover, so the search's proofs don't depend on these.
 */
const anyPureMethod = (runtime: RuntimeModel, isStorage: (node: Node) => boolean, scopes: ScopeInfo): boolean => {
    const prover = new PurityProver(scopes);
    for (const statement of rootStatements(runtime.root)) {
        if (statement.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression" || statement.expression.left.type !== "MemberExpression") continue;
        const { left, right } = statement.expression;
        if (!isStorage(left.object) || right.type !== "CallExpression" || right.callee.type !== "FunctionExpression" || right.arguments.length > 0) continue;
        const iife = right.callee;
        const builder = builderOf(iife, scopes);
        if (typeof builder === "string") continue;
        for (const fn of builder.methods.values()) if (prover.impurity(fn, iife) === undefined) return true;
    }
    return false;
};

/** A storage path holding a builder's pure hash, interpreted over its builder's bindings. */
interface Target {
    readonly path: PropertyPath;
    readonly fn: FunctionLike;
    readonly interpreter: Interpreter;
}

/** Calls of the runtime's pure hash functions: which callees are such, and their values for known arguments. */
class HashFunctions {
    readonly #runtime: RuntimeModel;
    readonly #analysis: StorageAnalysis;
    readonly #scopes: ScopeInfo;
    readonly #log: PassContext["log"];
    readonly #prover: PurityProver;
    /** By callee path: the hash, or why the callee isn't one. */
    readonly #targets = new Map<string, Target | string>();
    readonly #results = new Map<string, Evaluation>();
    #steps = 0;

    constructor(runtime: RuntimeModel, analysis: StorageAnalysis, scopes: ScopeInfo, log: PassContext["log"]) {
        this.#runtime = runtime;
        this.#analysis = analysis;
        this.#scopes = scopes;
        this.#log = log;
        this.#prover = new PurityProver(scopes);
    }

    mentionedIn(node: Node): boolean {
        if (node.type === "CallExpression" && typeof this.targetOf(node.callee) !== "string") return true;
        if (node.type === "FunctionExpression" || node.type === "ArrowFunctionExpression") return false;
        let found = false;
        forEachChild(node, (child) => {
            found ||= this.mentionedIn(child);
        });
        return found;
    }

    targetOf(callee: Node): Target | string {
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

    #resolveTarget(keys: PropertyPath): Target | string {
        const [first] = keys;
        const wrapper = keys.length === 1 && first !== undefined ? this.#runtime.wrappers.get(first) : undefined;
        const target = wrapper?.target ?? keys;
        if (wrapper !== undefined && (wrapper.receiver === undefined || !sameItems(wrapper.receiver, target.slice(0, -1)))) return "its wrapper applies it to another this";
        const name = target.at(-1);
        if (target.length < 2 || name === undefined) return "it isn't a method of a holder the prelude built";
        const definition = definitionOf(this.#runtime, this.#analysis.matcher.isStorage, target.slice(0, -1));
        if (typeof definition === "string") return definition;
        const builder = builderOf(definition.iife, this.#scopes);
        if (typeof builder === "string") return builder;
        const fn = builder.methods.get(name);
        if (fn === undefined) return `its builder gives it no plain function ${name}`;
        const held = this.#analysis.effects.snapshot.functionAt(target);
        if (held !== fn) return typeof held === "string" ? `after the prelude it may hold another function: ${held}` : "after the prelude it holds another function";
        const impure = this.#prover.impurity(fn, definition.iife);
        if (impure !== undefined) return `it isn't pure: ${impure}`;
        return { path: target, fn, interpreter: new Interpreter({ outer: (identifier) => this.#builderBinding(identifier, definition.iife) }) };
    }

    /** A name a proven hash (or a builder local it uses) doesn't declare: a builder local bound once for good, or a global. */
    #builderBinding(identifier: IdentifierReference, builder: FunctionNode): OuterBinding | string {
        const variable = this.#scopes.staticVariableOf(identifier);
        if (variable === undefined) return HASH_GLOBALS.has(identifier.name) ? { global: identifier.name } : `it reads the global ${identifier.name}`;
        const refusal = this.#prover.bound(variable, builder);
        if (refusal !== undefined) return refusal;
        const def = variable.defs[0]?.node as Node | undefined;
        if (def === undefined) return `it reads ${identifier.name}, which may change`;
        if (def.type === "FunctionDeclaration") return { function: def };
        const init = def.type === "VariableDeclarator" ? def.init : null;
        if (init?.type === "FunctionExpression" || init?.type === "ArrowFunctionExpression") return { function: init };
        if (init?.type === "Literal" && (init.value === null || typeof init.value === "string" || typeof init.value === "number" || typeof init.value === "boolean")) return { value: init.value };
        return `it reads ${identifier.name}, which may change`;
    }

    /** The call's reads (wrapper, hash) must see the snapshot's values; the hash is interpreted on the arguments. */
    valueOf(call: Node & { type: "CallExpression" }, evaluateIn: (node: Node) => Evaluation, reason: (why: string) => void): Evaluation {
        const target = this.targetOf(call.callee);
        const path = memberPath(call.callee);
        if (typeof target === "string" || path === undefined) return FAIL;
        const stale = this.#analysis.effects.staleAt(path.root, path.keys) ?? this.#analysis.effects.staleAt(path.root, target.path);
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
        const id = `${JSON.stringify(target.path)}(${argumentsKey(args)})`;
        let result = this.#results.get(id);
        if (result === undefined) {
            const left = TOTAL_STEPS - this.#steps;
            if (left <= 0) {
                reason("the hashes' step budget is used up");
                return FAIL;
            }
            const answer = target.interpreter.call(target.fn, args, Math.min(CALL_STEPS, left));
            this.#steps += answer.steps;
            if (!answer.ok && answer.exhausted && this.#steps >= TOTAL_STEPS) this.#log.warn(`the hashes' step budget of ${TOTAL_STEPS} is used up: later hash predicates stay as they are`);
            if (!answer.ok) this.#log.debug(`the hash doesn't answer: ${answer.reason}`, call);
            result = answer.ok ? value(answer.value) : FAIL;
            this.#results.set(id, result);
        }
        if (!result.ok) reason("the hash doesn't answer");
        return result;
    }
}

class Folder {
    readonly counts = { ifs: 0, neverRun: 0, unrolled: 0 };
    readonly refusals = new Map<string, number>();
    readonly #analysis: StorageAnalysis;
    readonly #hashes: HashFunctions;
    readonly #scopes: ScopeInfo;
    readonly #log: PassContext["log"];
    readonly #facts: PassContext["facts"];
    readonly #hasWith: boolean;
    readonly #followedCache = new Map<Variable, boolean>();

    constructor(analysis: StorageAnalysis, hashes: HashFunctions, scopes: ScopeInfo, log: PassContext["log"], facts: PassContext["facts"], hasWith: boolean) {
        this.#analysis = analysis;
        this.#hashes = hashes;
        this.#scopes = scopes;
        this.#log = log;
        this.#facts = facts;
        this.#hasWith = hasWith;
    }

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

    /** The value's key (`Snapshot`) for a constant-key chain on the storage object nothing changes after the prelude. */
    #stateKey(node: Node, reason: (why: string) => void): string | undefined {
        const path = memberPath(node);
        if (path === undefined || !this.#analysis.matcher.isStorage(path.root)) return undefined;
        const stale = this.#analysis.effects.staleAt(path.root, path.keys);
        if (stale !== undefined) {
            reason(stale.reason);
            return undefined;
        }
        const key = this.#analysis.effects.snapshot.keyAt(path.keys);
        if (typeof key === "string") reason(key);
        return typeof key === "string" ? undefined : key.key;
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
        spliceList(list, list.indexOf(loop), 1, replacement);
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
     * The loop's own nodes are reused (declarators get final values, the first write of each other local becomes
     * its assignment), so the scope analysis knows every reference in the result: no binding changes.
     */
    #finals(loop: ForStatement | WhileStatement, local: Env): Statement[] | string {
        const finalOf = (node: Node): Expression | undefined => {
            const variable = this.#variableOf(node);
            return variable === undefined || !local.has(variable) ? undefined : valueToNode(local.get(variable), node, this.#scopes);
        };
        const declared = new Set<string>();
        const init = loop.type === "ForStatement" ? loop.init : null;
        const declaration = init?.type === "VariableDeclaration" ? init : undefined;
        for (const declarator of declaration?.declarations ?? []) if (declarator.id.type === "Identifier") declared.add(declarator.id.name);
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
