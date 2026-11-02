import type { Expression, MemberExpression, Node, Statement } from "../core/ast.js";
import { memberPath, propertyKey } from "../core/ast.js";
import { at } from "../core/build.js";
import type { ScopeInfo } from "../core/scope.js";
import type { Path } from "../core/traverse.js";
import { replaceNodes, traverse } from "../core/traverse.js";
import { parentsWithin } from "./runtime/builders.js";
import type { StorageEffects } from "./runtime/effects.js";
import type { PropertyPath, RuntimeModel } from "./runtime/model.js";
import type { StorageMatcher } from "./runtime/storage.js";
import { rootStatements } from "./runtime/storage.js";
import type { KeySet } from "./key-sets.js";
import { keySets, mayName } from "./key-sets.js";

/** `path`, or the logical expression it is an operand of (transitively, through operators `through` accepts). */
const pastLogical = (path: Path, through: (operator: string) => boolean): Path => {
    let operand = path;
    while (operand.parent?.type === "LogicalExpression" && through(operand.parent.operator) && operand.parentPath !== null) operand = operand.parentPath;
    return operand;
};

/** A test position, or the operand of `!`. */
const inCondition = (operand: Path): boolean => {
    const parent = operand.parent;
    switch (parent?.type) {
        case "IfStatement":
        case "ConditionalExpression":
        case "WhileStatement":
        case "DoWhileStatement":
        case "ForStatement":
            return operand.key === "test";
        case "UnaryExpression":
            return parent.operator === "!";
        default:
            return false;
    }
};

// `onlyTested` asks that the value goes nowhere (`??`, `typeof`, `void` and equality only read it too), `onlyTruthiness`
// that nothing but its truthiness is used (`??` passes on more: whether it is nullish).

/** Whether the use of `G` at `path` is only tested; operators only read (semantic model 4). */
export const onlyTested = (path: Path): boolean => {
    const operand = pastLogical(path, () => true);
    const parent = operand.parent;
    if (parent?.type === "UnaryExpression") return parent.operator === "!" || parent.operator === "typeof" || parent.operator === "void";
    if (parent?.type === "BinaryExpression") return parent.operator === "===" || parent.operator === "!==" || parent.operator === "==" || parent.operator === "!=";
    return inCondition(operand);
};

const onlyTruthiness = (path: Path): boolean => inCondition(pastLogical(path, (operator) => operator !== "??"));

/** A no-argument call of a storage path `G.k.m` (or `G.w`). */
export interface CallSite {
    readonly call: Expression & { type: "CallExpression" };
    readonly site: Node;
    readonly statement: Statement | undefined;
    readonly discarded: boolean;
    readonly tested: boolean;
}

/** A use of `G` as a value or with a computed key: any key may be read there. */
interface DynamicUse {
    readonly node: Node;
    readonly site: Node;
    /** The runtime's root statement around it, if any. */
    readonly root: Statement | undefined;
}

export interface Survey {
    readonly calls: Map<string, { path: PropertyPath; sites: CallSite[] }>;
    readonly dynamic: readonly DynamicUse[];
}

/** `var s = G` with `s` a real alias (written once): `s` holds G under a name the matcher follows, not another one. */
export const isAliasDeclarator = (node: Node | null, matcher: StorageMatcher, scopes: ScopeInfo): boolean => {
    if (node?.type !== "VariableDeclarator" || node.id.type !== "Identifier") return false;
    const variable = scopes.variableOf(node.id);
    return variable !== undefined && matcher.aliases.has(variable);
};

/** The dynamic uses of `G`, and with `calls` its no-argument path calls by path. */
const walkUses = (program: Node, runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, calls: Survey["calls"] | undefined): DynamicUse[] => {
    const dynamic: DynamicUse[] = [];
    const roots = new Set<Node>(rootStatements(runtime.root));
    let root: Statement | undefined;
    traverse(program, {
        enter(path) {
            if (roots.has(path.node)) root = path.node as Statement;
        },
        exit(path) {
            if (path.node === root) root = undefined;
        },
        CallExpression(path) {
            const call = path.node;
            if (calls === undefined || call.arguments.length > 0 || call.callee.type !== "MemberExpression") return;
            const target = memberPath(call.callee as MemberExpression);
            if (target === undefined || target.keys.length === 0 || !matcher.isStorage(target.root)) return;
            const id = JSON.stringify(target.keys);
            const entry = calls.get(id) ?? { path: target.keys, sites: [] };
            const parent = path.parent;
            const statement = parent?.type === "ExpressionStatement" ? parent : undefined;
            const discarded = statement !== undefined || (parent?.type === "SequenceExpression" && parent.expressions.at(-1) !== call);
            entry.sites.push({ call, site: target.root, statement, discarded, tested: onlyTruthiness(path) });
            calls.set(id, entry);
        },
        MemberExpression(path) {
            const node = path.node;
            if (matcher.isStorage(node.object) && propertyKey(node) === undefined) dynamic.push({ node, site: node.object, root });
        },
        Identifier(path) {
            if (!matcher.isStorage(path.node)) return;
            const parent = path.parent;
            const asObject = parent?.type === "MemberExpression" && path.key === "object";
            const asDeclaration = parent?.type === "FunctionDeclaration" && path.key === "id";
            if (!asObject && !asDeclaration && !isAliasDeclarator(parent, matcher, scopes) && !path.isWriteTarget() && !onlyTested(path)) dynamic.push({ node: path.node, site: path.node, root });
        },
    });
    return dynamic;
};

export const survey = (program: Node, runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo): Survey => {
    const calls: Survey["calls"] = new Map();
    return { calls, dynamic: walkUses(program, runtime, matcher, scopes, calls) };
};

/** `survey`'s dynamic uses alone, for passes that find their calls otherwise. */
export const dynamicUses = (program: Node, runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo): readonly DynamicUse[] => walkUses(program, runtime, matcher, scopes, undefined);

interface KeyReference {
    readonly node: Node;
    readonly root: Node | undefined;
    readonly site: Node | undefined;
}

/** Every static member reference `x.k` with `k` in `keys`, whatever `x` is (an unfollowable alias still names the key). */
const keyReferences = (program: Node, runtime: RuntimeModel, matcher: StorageMatcher, keys: ReadonlySet<string>): Map<string, KeyReference[]> => {
    const references = new Map<string, KeyReference[]>();
    const roots = new Set<Node>(rootStatements(runtime.root));
    let root: Node | undefined;
    traverse(program, {
        enter(path) {
            if (roots.has(path.node)) root = path.node;
        },
        exit(path) {
            if (path.node === root) root = undefined;
        },
        MemberExpression(path) {
            const node = path.node;
            const key = propertyKey(node);
            if (key === undefined || !keys.has(key)) return;
            const reference = { node, root, site: matcher.isStorage(node.object) ? node.object : undefined };
            const list = references.get(key);
            if (list === undefined) references.set(key, [reference]);
            else list.push(reference);
        },
    });
    return references;
};

/**
 * What may reach a lock's holder key other than its calls (code-locks' full mode, domain-locks), for every lock of a
 * pass run: the static references to the keys `holders` and their wrappers' come from one walk, and each root
 * statement's key sets are built once.
 */
export class HolderReach {
    readonly #program: Node;
    readonly #runtime: RuntimeModel;
    readonly #matcher: StorageMatcher;
    readonly #scopes: ScopeInfo;
    readonly #effects: StorageEffects;
    readonly #dynamic: readonly DynamicUse[];
    readonly #holders: ReadonlySet<string>;
    #references: Map<string, KeyReference[]> | undefined;
    readonly #keySets = new Map<Node, (key: Expression) => KeySet | undefined>();
    readonly #keys = new Map<Node, KeySet | undefined>();

    constructor(program: Node, runtime: RuntimeModel, matcher: StorageMatcher, scopes: ScopeInfo, effects: StorageEffects, dynamic: readonly DynamicUse[], holders: ReadonlySet<string>) {
        this.#program = program;
        this.#runtime = runtime;
        this.#matcher = matcher;
        this.#scopes = scopes;
        this.#effects = effects;
        this.#dynamic = dynamic;
        this.#holders = holders;
    }

    /**
     * The first use of `G` as a value or read with a computed key that may reach the holder key `key` once `builder`
     * has run: not done before it, not a store of `G` as a global the program never names (model 2), and not a
     * computed access whose key can't name `key` (`keySets`: the decoder's name probe tries permutations of a few
     * characters).
     */
    reachingDynamicUse(key: string, builder: Statement): Node | undefined {
        const effects = this.#effects;
        return this.#dynamic.find(({ node, site, root }) => {
            if (effects.runsBefore(site, builder) || effects.keptAsGlobal(node)) return false;
            if (node.type !== "MemberExpression" || !node.computed || root === undefined) return true;
            const keys = this.#keysAt(node, root);
            return keys === undefined || mayName(keys, key);
        })?.node;
    }

    /**
     * Why a reference to the holder key `path[0]` may reach the lock `path` other than through calls whose callee
     * objects (`G.k`) are `callees`: it is none of them, isn't in the builder's own statement or the definition of a
     * wrapper of something under the holder that nothing uses, and may run once the builder has (before it, `G.k`
     * isn't the lock yet).
     */
    strayReference(path: PropertyPath, callees: ReadonlySet<Node>, builder: Statement): Node | undefined {
        const holder = path[0] as string;
        if (!this.#holders.has(holder)) throw new Error(`${holder} isn't one of the holders the references were collected for`);
        const wrappers = [...this.#runtime.wrappers.values()].filter((wrapper) => wrapper.target[0] === holder);
        const references = this.#keyReferences();
        const unused = new Set(wrappers.filter((wrapper) => (references.get(wrapper.key) ?? []).every((reference) => reference.root === wrapper.definition)).map((wrapper) => wrapper.definition));
        return references
            .get(holder)
            ?.find(({ node, root, site }) => !callees.has(node) && root !== builder && (root === undefined || !unused.has(root)) && (site === undefined || !this.#effects.runsBefore(site, builder)))
            ?.node;
    }

    #keyReferences(): ReadonlyMap<string, readonly KeyReference[]> {
        if (this.#references === undefined) {
            const keys = new Set(this.#holders);
            for (const wrapper of this.#runtime.wrappers.values()) if (this.#holders.has(wrapper.target[0] as string)) keys.add(wrapper.key);
            this.#references = keyReferences(this.#program, this.#runtime, this.#matcher, keys);
        }
        return this.#references;
    }

    #keysAt(node: MemberExpression, root: Statement): KeySet | undefined {
        if (this.#keys.has(node)) return this.#keys.get(node);
        let keysOf = this.#keySets.get(root);
        if (keysOf === undefined) {
            keysOf = keySets(this.#scopes, parentsWithin(root));
            this.#keySets.set(root, keysOf);
        }
        const keys = keysOf(node.property as Expression);
        this.#keys.set(node, keys);
        return keys;
    }
}

/** `G.key()` with `key` a global-read getter (the runtime fact) the program never replaces: a read of that global property. */
export const isGlobalRead = (call: Node, runtime: RuntimeModel, matcher: StorageMatcher, effects: StorageEffects): boolean => {
    if (call.type !== "CallExpression" || call.arguments.length > 0 || call.callee.type !== "MemberExpression") return false;
    const key = propertyKey(call.callee);
    return key !== undefined && runtime.globalReads.has(key) && matcher.isStorage(call.callee.object) && effects.staleAt(call.callee.object, [key]) === undefined;
};

/** Replaces nodes by `replacements`, and removes call statements in `removals`, leaving an empty statement where one must stay. */
export const rewriteCalls = (program: Node, replacements: ReadonlyMap<Node, Node>, removals: ReadonlySet<Node>): void => {
    replaceNodes(program, replacements);
    if (removals.size === 0) return;
    traverse(program, {
        ExpressionStatement(path) {
            if (!removals.has(path.node)) return;
            if (path.isInStatementList()) path.remove();
            else path.replace(at<Statement>({ type: "EmptyStatement" }, path.node));
        },
    });
};
