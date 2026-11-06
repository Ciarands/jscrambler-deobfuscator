import type { Expression, IdentifierReference, Node, Program, Statement } from "../../core/ast.js";
import { memberPath, propertyKey } from "../../core/ast.js";
import { sameReference } from "../../core/equal.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo } from "../../core/scope.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import type { StorageEffects } from "./effects.js";
import { storageEffects } from "./effects.js";
import type { SetupFacts } from "./getters.js";
import { SetupAnalysis } from "./getters.js";
import type { PropertyPath, RuntimeModel, Wrapper } from "./model.js";
import { RUNTIME } from "./model.js";
import { realm } from "./realm.js";
import { rootStatements, storageMatcher } from "./storage.js";

/**
 * A lone top-level IIFE (after directives; function or block-bodied arrow, direct or `.call(this)`, under unary
 * operators), or the program.
 */
const rootBody = (program: Program): { body: Statement[]; owner: Node } => {
    const statements = program.body.filter(
        (statement) => statement.type !== "EmptyStatement" && !(statement.type === "ExpressionStatement" && "directive" in statement && typeof statement.directive === "string")
    );
    const [only] = statements;
    let call: Node | undefined = statements.length === 1 && only?.type === "ExpressionStatement" ? only.expression : undefined;
    while (call?.type === "UnaryExpression") call = call.argument;
    if (call?.type !== "CallExpression") return { body: program.body, owner: program };
    let fn: Node = call.callee;
    if (fn.type === "MemberExpression" && propertyKey(fn) === "call" && call.arguments.length <= 1 && call.arguments.every((arg) => arg.type === "ThisExpression")) fn = fn.object;
    const block = (fn.type === "FunctionExpression" || fn.type === "ArrowFunctionExpression") && !fn.async && !fn.generator && fn.body?.type === "BlockStatement" ? fn.body : undefined;
    return block === undefined ? { body: program.body, owner: program } : { body: block.body, owner: fn };
};

/** Also `(X = G).k = ...`, which stores `G` somewhere first (keeping the runtime as a global): the member is still `G`'s. */
const storageAssignment = (statement: Statement): { object: IdentifierReference; key: string; right: Expression } | undefined => {
    if (statement.type !== "ExpressionStatement") return undefined;
    const e = statement.expression;
    if (e.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "MemberExpression") return undefined;
    const object = e.left.object.type === "AssignmentExpression" && e.left.object.operator === "=" ? e.left.object.right : e.left.object;
    const key = object.type === "Identifier" ? propertyKey(e.left) : undefined;
    return key === undefined || object.type !== "Identifier" ? undefined : { object, key, right: e.right };
};

const storagePath = (node: Node, storage: string): PropertyPath | undefined => {
    const path = memberPath(node);
    return path !== undefined && path.root.type === "Identifier" && path.root.name === storage ? path.keys : undefined;
};

/** `function () { return typeof T === "function" ? T.apply(O, arguments) : T; }` */
const wrapperOf = (fn: Expression, storage: string): Omit<Wrapper, "key" | "definition"> | undefined => {
    if (fn.type !== "FunctionExpression" || fn.body === null || fn.body.body.length !== 1) return undefined;
    const ret = fn.body.body[0];
    if (ret?.type !== "ReturnStatement" || ret.argument?.type !== "ConditionalExpression") return undefined;
    const { test, consequent, alternate } = ret.argument;
    if (test.type !== "BinaryExpression" || (test.operator !== "===" && test.operator !== "==")) return undefined;
    const typeofSide = [test.left, test.right].find((side) => side.type === "UnaryExpression" && side.operator === "typeof");
    const otherSide = test.left === typeofSide ? test.right : test.left;
    if (typeofSide?.type !== "UnaryExpression" || otherSide.type !== "Literal" || otherSide.value !== "function" || consequent.type !== "CallExpression") return undefined;
    const target = storagePath(alternate, storage);
    if (target === undefined || !sameReference(typeofSide.argument, alternate)) return undefined;
    const callee = consequent.callee;
    if (callee.type !== "MemberExpression" || propertyKey(callee) !== "apply" || !sameReference(callee.object, alternate)) return undefined;
    const [receiver, args] = consequent.arguments;
    if (receiver === undefined || receiver.type === "SpreadElement" || args?.type !== "Identifier" || args.name !== "arguments") return undefined;
    return { target, receiver: storagePath(receiver, storage) };
};

/**
 * The root-assigned name with most evidence: an empty root function declaration (`function G() {}`), then most wrapper
 * definitions, then most assignments. Never by source order alone: when the best two tie, there is none.
 */
const storageOf = (body: readonly Statement[]): string | { ambiguous: string[] } | undefined => {
    const evidence = new Map<string, { declared: number; wrappers: number; assignments: number }>();
    for (const statement of body) {
        const assignment = storageAssignment(statement);
        if (assignment === undefined) continue;
        const name = assignment.object.name;
        const entry = evidence.get(name) ?? { declared: 0, wrappers: 0, assignments: 0 };
        entry.assignments++;
        if (wrapperOf(assignment.right, name) !== undefined) entry.wrappers++;
        evidence.set(name, entry);
    }
    for (const statement of body) {
        const entry = statement.type === "FunctionDeclaration" && statement.id !== null ? evidence.get(statement.id.name) : undefined;
        if (entry !== undefined && statement.type === "FunctionDeclaration" && statement.params.length === 0 && statement.body?.body.length === 0 && !statement.async && !statement.generator)
            entry.declared = 1;
    }
    const ranked = [...evidence].toSorted(([, a], [, b]) => b.declared - a.declared || b.wrappers - a.wrappers || b.assignments - a.assignments);
    const [best, second] = ranked;
    if (best === undefined) return undefined;
    const same = (a: typeof best, b: typeof best): boolean => a[1].declared === b[1].declared && a[1].wrappers === b[1].wrappers && a[1].assignments === b[1].assignments;
    return second !== undefined && same(best, second) ? { ambiguous: [best[0], second[0]] } : best[0];
};

type SetupView = Pick<SetupFacts, "setupKeys" | "inheritedKeys" | "unprovenAliases">;

/**
 * Why an assignment `G.key = v`, `G` a function, may not leave `v` in a writable data property: a property the setup
 * added to what `G` inherits (an accessor or a read-only property, maybe; the program adds nothing else to builtins:
 * `getters.ts`), or an inherited accessor or read-only property of the builtins (model 7). A function's own read-only
 * properties (`length`, `name`, a sloppy one's `arguments` and `caller`) are such properties of `Function.prototype` too.
 */
const unwritable = (key: string, setup: SetupView): string | undefined => {
    if (setup.unprovenAliases.has(key) || setup.inheritedKeys.has(key)) return "the setup adds it to a builtin, maybe to one the storage object inherits from";
    for (let owner: object | null = Function.prototype; owner !== null; owner = Object.getPrototypeOf(owner) as object | null) {
        const descriptor = Object.getOwnPropertyDescriptor(owner, key);
        if (descriptor !== undefined) return descriptor.writable === true ? undefined : "a function inherits it as an accessor or a read-only property";
    }
    return undefined;
};

/**
 * The wrappers root statements define (`G.k = function () {...}`, `wrapperOf`), in root order (a later one for a key
 * replaces an earlier): each statement leaves its function at `G.k`. `G` is a root function declaration nothing
 * reassigns, an object from the start (hoisted); the key is no key a function can't hold as a writable data property
 * (`unwritable`) or the setup defines on `G` (`setupKeys`). Whatever else could make it an accessor or `G`
 * non-extensible first must reach `G` itself (model 3): `unhanded`.
 */
const wrappersOf = (body: readonly Statement[], storage: string, scopes: ScopeInfo, setup: SetupView, log: PassLog): Map<string, Wrapper> => {
    const wrappers = new Map<string, Wrapper>();
    const declaration = body.find((statement) => statement.type === "FunctionDeclaration" && statement.id?.name === storage);
    const variable = declaration?.type === "FunctionDeclaration" && declaration.id !== null ? scopes.variableOf(declaration.id) : undefined;
    const fixed = variable !== undefined && variable.defs.length === 1 && !scopes.staticReferences(variable).some((reference) => reference.isWrite());
    for (const statement of body) {
        const assignment = storageAssignment(statement);
        if (assignment?.object.name !== storage) continue;
        const found = wrapperOf(assignment.right, storage);
        if (found === undefined) continue;
        const { key } = assignment;
        const refused =
            !fixed || scopes.variableOf(assignment.object) !== variable
                ? `${storage} isn't a root function declaration nothing reassigns`
                : setup.setupKeys.has(key)
                  ? "the setup defines it"
                  : unwritable(key, setup);
        if (refused !== undefined) {
            wrappers.delete(key);
            log.debug(`${storage}.${key} isn't taken as a wrapper: ${refused}`, statement);
            continue;
        }
        wrappers.set(key, { key, ...found, definition: statement });
        log.debug(`wrapper ${key} -> ${storage}.${found.target.join(".")}`, statement);
    }
    return wrappers;
};

/**
 * The wrappers no prelude code may change before their statement but through `G`'s paths (model 3): no prelude call is
 * handed `G` (`Object.defineProperty(G, ...)`, `Object.freeze(G)`) or may use it as its `this`. Over the whole prelude:
 * the effects analysis doesn't tell which of those run first.
 */
const unhanded = (wrappers: ReadonlyMap<string, Wrapper>, effects: StorageEffects, storage: string, log: PassLog): Map<string, Wrapper> => {
    const kept = new Map<string, Wrapper>();
    const escape = effects.escapedInPrelude([]);
    for (const [key, wrapper] of wrappers) {
        const call = escape === undefined ? effects.preludeCallChanging([key], 0) : undefined;
        if (escape !== undefined) log.debug(`${storage}.${key} isn't taken as a wrapper: prelude code hands ${storage} to a call`, escape);
        else if (call !== undefined) log.debug(`${storage}.${key} isn't taken as a wrapper: a prelude call may change ${storage} through its this`, call);
        else kept.set(key, wrapper);
    }
    return kept;
};

interface StatementFacts {
    readonly local: Set<Node>;
    readonly setup: Set<Node>;
}

/** See `Facts.replaced`. The facts describe one statement's whole effect, so they carry only one-to-one. */
const carryStatementFacts = (statementFacts: StatementFacts, originals: readonly Node[], replacements: readonly Node[]): void => {
    const [original] = originals;
    const [replacement] = replacements;
    if (originals.length !== 1 || replacements.length !== 1 || original === undefined || replacement === undefined || original === replacement) return;
    for (const set of [statementFacts.local, statementFacts.setup]) {
        if (set.delete(original)) set.add(replacement);
    }
};

const QUIET: PassLog = { info: () => {}, debug: () => {}, warn: () => {}, debugging: false };

/**
 * The slots holding the global object after the prelude (models 7, 10): the statement storing it is in place before
 * later code runs (model 1), and no other prelude code changes the slot, by a write or through a `this` (model 3; what
 * may happen later is each reader's `staleAt`).
 */
const globalKeysOf = (runtime: RuntimeModel, effects: StorageEffects, slots: ReadonlyMap<string, Statement>, log: PassLog): Set<string> => {
    const keys = new Set<string>();
    const statements: readonly Node[] = rootStatements(runtime.root);
    for (const [key, statement] of slots) {
        const call = effects.preludeCallChanging([key], statements.indexOf(statement));
        if (effects.preludeWritesTo([key]) !== 1) log.debug(`${runtime.storage}.${key} may hold something else after the prelude: other prelude code may write it`, statement);
        else if (call !== undefined) log.debug(`${runtime.storage}.${key} may hold something else after the prelude: a call may change it through its this`, call);
        else keys.add(key);
    }
    return keys;
};

/**
 * Recognizes the obfuscator's runtime prelude without running it: the storage object, its wrappers, the setup's
 * aliases and the slots holding the global object. Runs right after `unflatten` and before anything rewrites the
 * runtime, so it sees the runtime as the obfuscator wrote it. Produces the RUNTIME fact; changes no code.
 */
export const runtime: Pass = {
    name: "runtime",
    description: "Recognize the obfuscator's runtime prelude: storage object, wrappers, setup aliases",
    run({ program, log, scope, facts }: PassContext): PassResult {
        const { body, owner: root } = rootBody(program);
        const candidate = storageOf(body);
        if (typeof candidate !== "string") {
            log.info(candidate === undefined ? "no runtime storage object found" : `no runtime storage object: ${candidate.ambiguous.join(" and ")} look alike`);
            return { changed: 0 };
        }
        const storage = candidate;
        log.info(`storage object: ${storage}`);

        const scopes = scope();
        const rootScopes = new Set<Node>([program]);
        if (root !== program) rootScopes.add(root);
        const { globalSlots, local: evaluated, ...setupFacts } = new SetupAnalysis({ scopes, realm: realm(), storage, rootBlocks: rootScopes, log }).run(body);
        const { aliases, callAliases } = setupFacts;
        const local = new Set<Node>(evaluated);
        const setup = new Set<Node>(setupFacts.setup);
        let model: RuntimeModel = { ...setupFacts, storage, root, globalKeys: new Set(), wrappers: wrappersOf(body, storage, scopes, setupFacts, log), local, setup };
        // A wrapper left out leaves its receiver unfollowed, which may hand `G` on: until no more are left out.
        for (;;) {
            const effects = storageEffects(model, storageMatcher(program, model, scopes), scopes, QUIET);
            const wrappers = unhanded(model.wrappers, effects, storage, log);
            if (wrappers.size === model.wrappers.size) {
                model = { ...model, globalKeys: globalKeysOf(model, effects, globalSlots, log) };
                break;
            }
            model = { ...model, wrappers };
        }
        const { wrappers, globalKeys } = model;
        log.info(`wrappers ${wrappers.size}, aliases ${aliases.length}, call aliases ${callAliases.size}, global keys [${[...globalKeys].join(", ")}]`);
        facts.set(RUNTIME, model);
        facts.onReplace((originals, replacements) => carryStatementFacts({ local, setup }, originals, replacements));
        return { changed: 0, stats: { wrappers: wrappers.size, aliases: aliases.length, callAliases: callAliases.size } };
    },
};
