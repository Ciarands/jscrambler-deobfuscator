import type { BlockStatement, MemberExpression, Node, Program, Statement, StaticBlock, SwitchCase } from "../../core/ast.js";
import { memberKey, memberPath } from "../../core/ast.js";
import { at } from "../../core/build.js";
import { sameReference } from "../../core/equal.js";
import { placeholderDeclaration } from "../../core/hoisting.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo } from "../../core/scope.js";
import { forEachChild, traverse } from "../../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../../pipeline/pass.js";
import { storageAnalysis } from "../emulate/effects.js";
import type { RuntimeModel } from "../emulate/model.js";
import { RUNTIME } from "../emulate/model.js";
import { annexBName, caseDeclarations, perIterationCapture } from "./declarations.js";
import type { Machine, Refusal, RefusalCode, StateKey } from "./match.js";
import { matchMachine, refuse } from "./match.js";
import { reachableOrder, structure } from "./structure.js";
import { tidy } from "./tidy.js";

/**
 * State keys from the emulated runtime, for constant-key member chains on the storage object
 * (`G[123].m[18][11]`, cyclic-array states): the value the chain holds in the sandbox once the
 * prelude has run. That is only the value the program reads when nothing can change the chain in between
 * (`storageEffects`); otherwise the chain gets no key. The guest walks data properties only; a getter on the way gives
 * no key, so no runtime code runs. Objects (rows of the state table) are keyed by identity, numbers and strings by
 * value, like static constants.
 */
const runtimeStateKey = (program: Node, runtime: RuntimeModel | undefined, scopes: ScopeInfo, log: PassLog): ((node: Node) => StateKey | undefined) | undefined => {
    if (runtime === undefined || runtime.guest.broken !== undefined) return undefined;
    const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
    const cache = new Map<string, StateKey | undefined>();
    return (node) => {
        const path = memberPath(node);
        if (path === undefined || !matcher.isStorage(path.root)) return undefined;
        const stale = effects.staleAt(path.root, path.keys);
        if (stale !== undefined) {
            log.debug(`kept: ${stale.reason}`, stale.node);
            return undefined;
        }
        const id = JSON.stringify(path.keys);
        if (!cache.has(id)) cache.set(id, runtime.guest.stateKey(path.keys));
        return cache.get(id);
    };
};

/** Every identifier in the machine (loop and initializer), and those called directly (`g(...)`): one walk. */
const machineIdentifiers = (roots: readonly Node[]): { identifiers: Set<Node>; callees: Set<Node> } => {
    const identifiers = new Set<Node>();
    const callees = new Set<Node>();
    const walk = (node: Node): void => {
        if (node.type === "Identifier") identifiers.add(node);
        else if (node.type === "CallExpression" && node.callee.type === "Identifier") callees.add(node.callee);
        forEachChild(node, walk);
    };
    for (const root of roots) walk(root);
    return { identifiers, callees };
};

/**
 * A use of the state variable outside the machine (`inside`: the identifiers of the loop and its initializer), or
 * `"unknown"` when that can't be ruled out. Unflattening removes every write to the state, so any outside reader would
 * see different values: code after the loop expects the end state, a closure called from a case body expects the
 * current one.
 *
 * Slot states (`O0[5]`, a slot of the `[arguments]` array) go through the array variable's references: every outside
 * one must be a constant-key access to another slot, or a plain write to the variable.
 */
const outsideUse = (scopes: ScopeInfo, machine: Machine, inside: ReadonlySet<Node>, memberOf: () => ReadonlyMap<Node, MemberExpression>): Node | "unknown" | undefined => {
    const state = machine.state;
    const root = state.type === "MemberExpression" ? state.object : state;
    if (root.type !== "Identifier" || (state.type !== "Identifier" && state.type !== "MemberExpression")) return "unknown";
    const references = scopes.variableOf(root)?.references ?? scopes.globalReferences(root.name);
    for (const reference of references) {
        const identifier = reference.identifier as unknown as Node;
        if (inside.has(identifier)) continue;
        if (state.type === "Identifier") return identifier;
        if (reference.isWriteOnly()) continue;
        const member = memberOf().get(identifier);
        if (member === undefined || memberKey(member) === undefined || sameReference(member, state)) return identifier;
    }
    return undefined;
};

/** `object` → its member expression, for every `x.k` / `x[k]` whose object is an identifier. One walk, on demand. */
const membersByObject = (program: Node): Map<Node, MemberExpression> => {
    const members = new Map<Node, MemberExpression>();
    const walk = (node: Node): void => {
        if (node.type === "MemberExpression" && node.object.type === "Identifier") members.set(node.object, node);
        forEachChild(node, walk);
    };
    walk(program);
    return members;
};

/** The statement list of a node `Path.isInStatementList()` accepted. */
const statementsOf = (parent: Node): readonly Statement[] => (parent.type === "SwitchCase" ? (parent as SwitchCase).consequent : (parent as Program | BlockStatement | StaticBlock).body);

/**
 * Control-flow unflattening.
 *
 * Runs right after `normalize`: jscrambler flattens nearly every function, including its own runtime helpers, into
 * `for (; S !== end;) switch (S)` machines. Machines whose states are plain constants need nothing else to be undone,
 * and every later pass (global proxy, aliases, decoders, slot inlining) is far simpler to write and to check on
 * structured code. Machines whose states are computed (cyclic-array ids) are left for a later run, after those ids
 * have been resolved to constants or keyed by the emulated runtime (`runtimeStateKey`).
 */
export const unflatten: Pass = {
    name: "unflatten",
    description: "Rebuild loops and ifs from control-flow-flattened switch machines",
    run({ program, log, scope, facts }: PassContext): PassResult {
        // Scope analysis (and the runtime state keys built on it) only once a loop looks like a machine: most rounds
        // find none. It always happens before the first rewrite (every rewrite first checks the state's uses), so it
        // sees the program as it was; lookups are by node identity, and the nodes checked here are moved, not copied.
        let analysis: { scopes: ScopeInfo; stateKey: ((node: Node) => StateKey | undefined) | undefined } | undefined;
        const analysed = () => {
            if (analysis === undefined) {
                const scopes = scope();
                analysis = { scopes, stateKey: runtimeStateKey(program, facts.get(RUNTIME), scopes, log) };
            }
            return analysis;
        };
        const resolve = (identifier: Node) => analysed().scopes.variableOf(identifier);
        const stateKey = (node: Node) => analysed().stateKey?.(node);
        let members: Map<Node, MemberExpression> | undefined;
        const memberOf = () => (members ??= membersByObject(program));

        // Labels of the walk so far: every label enclosing a machine, or inside it, is seen before the machine is
        // rebuilt (on exit), and those are the only ones a generated label could clash with.
        const taken = new Set<string>();
        let counter = 0;
        const labels = {
            next(prefix: string): string {
                let name: string;
                do name = `${prefix}${++counter}`;
                while (taken.has(name));
                taken.add(name);
                return name;
            },
        };

        let unflattened = 0;
        let skipped = 0;
        const refusals = new Map<RefusalCode, number>();
        const skip = (refusal: Refusal, fallback: Node) => {
            skipped++;
            refusals.set(refusal.code, (refusals.get(refusal.code) ?? 0) + 1);
            log.debug(`skipped (${refusal.code}): ${refusal.reason}`, refusal.node ?? fallback);
        };

        traverse(program, {
            LabeledStatement: (path) => void taken.add(path.node.label.name),
            ForStatement: {
                // On exit, so machines nested inside case bodies are already unflattened when their parent is matched.
                exit(path) {
                    const loop = path.node;
                    const siblings = path.isInStatementList() && path.parent !== null ? statementsOf(path.parent) : null;
                    const site = { loop, siblings, index: path.index, labeled: path.parent?.type === "LabeledStatement" };
                    const matched = matchMachine(site, resolve, stateKey);
                    if (!matched.ok) {
                        if (matched.code !== "not-a-machine") skip(matched, loop);
                        return;
                    }
                    const machine = matched.machine;
                    const { scopes } = analysed();

                    const lexicalInit = loop.init?.type === "VariableDeclaration" && loop.init.kind !== "var";
                    const captured = perIterationCapture(scopes, loop);
                    if (captured !== undefined) return skip(captured, loop);

                    const { identifiers, callees } = machineIdentifiers(machine.initializer === null ? [loop] : [machine.initializer, loop]);
                    const outside = outsideUse(scopes, machine, identifiers, memberOf);
                    if (outside === "unknown") return skip(refuse("state-escapes", "can't rule out uses of the state outside the machine", machine.state), loop);
                    if (outside !== undefined) return skip(refuse("state-escapes", "state is used outside the machine", outside), loop);

                    const order = reachableOrder(machine);
                    const built = structure(machine, order, loop, labels);
                    if (!built.ok) return skip(refuse("unstructured", built.reason, loop), loop);
                    const declared = caseDeclarations(scopes, machine, new Set(order), callees, log);
                    if (!declared.ok) return skip(declared, loop);
                    const tidied = tidy(built.statements, log);

                    const { hoisted, vars } = declared.declarations;
                    for (const name of tidied.dropped.vars) vars.add(name);
                    for (const declaration of tidied.dropped.functions) {
                        const name = annexBName(scopes, declaration);
                        if (name !== undefined) vars.add(name);
                    }
                    const block = (body: Statement[]): Statement => at<BlockStatement>({ type: "BlockStatement", body }, loop);
                    // Hoisted functions get a block of their own: the code around them (the loop's init) never saw them.
                    const code = hoisted.length > 0 ? [block([...hoisted, ...tidied.statements])] : tidied.statements;
                    // A `let` init keeps its own block, as the loop gave it.
                    const body = lexicalInit ? [block([...machine.preamble, ...code])] : [...machine.preamble, ...code];
                    const statements: Statement[] = [...placeholderDeclaration("var", vars, loop), ...body];
                    if (vars.size > 0) log.debug(`kept declarations of dropped code: var ${[...vars].join(", ")}`, loop);

                    if (siblings !== null) {
                        facts.replaced(machine.initializer === null ? [loop] : [machine.initializer, loop], statements);
                        if (machine.initializer !== null) path.removeSibling(machine.initializer);
                        path.insertBefore(statements);
                        path.remove();
                    } else {
                        const replacement = statements.length === 1 && statements[0]?.type === "BlockStatement" ? statements[0] : block(statements);
                        facts.replaced([loop], [replacement]);
                        path.replace(replacement);
                    }
                    unflattened++;
                    log.debug(`unflattened ${machine.blocks.size} states`, loop);
                },
            },
        });

        for (const [code, count] of refusals) log.info(`skipped ${count} machine(s): ${code}`);
        return { changed: unflattened, stats: { unflattened, skipped } };
    },
};
