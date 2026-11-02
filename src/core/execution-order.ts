import type { Node } from "./ast.js";
import type { ScopeInfo, Variable } from "./scope.js";
import { forEachChild } from "./traverse.js";

/** The kinds `reachesAfter` orders by position (reads, declarators, statements); it refuses any other node. */
const ORDERED: Record<string, true> = { Identifier: true, MemberExpression: true, VariableDeclarator: true, ExpressionStatement: true };

const functionBody = (block: Node): readonly Node[] | undefined =>
    block.type === "Program"
        ? block.body
        : (block.type === "FunctionDeclaration" || block.type === "FunctionExpression" || block.type === "ArrowFunctionExpression") && block.body !== null && block.body.type === "BlockStatement"
          ? block.body.body
          : undefined;

/** A node's parent; none for the name of `o.name`, which is no reference. */
export const referenceParent = (scopes: ScopeInfo, node: Node): Node | undefined => {
    const above = scopes.parentOf(node);
    return above?.type === "MemberExpression" && !above.computed && above.property === node ? undefined : above;
};

/** A node and its ancestors, innermost first, with each one's place in that chain. */
interface Ancestry {
    readonly chain: readonly Node[];
    readonly index: ReadonlyMap<Node, number>;
}

/**
 * Whether a use runs after a definition, from document order and the calls of the function declarations it sits in.
 * Its caches hold for one constant environment: parents change only when the scope analysis' generation does, which
 * makes `constantEnv` build a new one.
 */
export class ExecutionOrder {
    readonly #scopes: ScopeInfo;
    /** `GlobalEscape.safe`: a script global's function may also be called through the global object. */
    readonly #globalSafe: (variable: Variable) => boolean | undefined;
    readonly #childPositions = new Map<Node, Map<Node, number>>();
    readonly #topLevels = new Map<Node, ReadonlySet<Node>>();
    readonly #ancestries = new Map<Node, Ancestry>();
    /**
     * For a constant declared inside a nested statement list rather than directly in its body: that list. Control
     * enters a statement list only at its start (no jump lands inside one), so a use after the declaration and still
     * inside the list runs after it in the same pass through the list.
     */
    readonly #limits = new Map<Node, Node>();
    /**
     * Verdicts of `runsAfter`, per definition: proven ones only (see there). A `false` is always final: assumptions
     * only ever make a check succeed.
     */
    readonly #verdicts = new Map<Node, Map<Node, boolean>>();
    readonly #checking = new Map<Node, Set<Node>>();
    #depth = 0;
    #reached: { readonly known: Map<Node, boolean>; readonly declaration: Node }[] = [];

    constructor(scopes: ScopeInfo, globalSafe: (variable: Variable) => boolean | undefined) {
        this.#scopes = scopes;
        this.#globalSafe = globalSafe;
    }

    /** Whether a `runsAfter` check is assuming a declaration runs after its definition. */
    get assuming(): boolean {
        return this.#depth > 0;
    }

    isTopLevel(block: Node, statement: Node | undefined): boolean {
        if (statement === undefined) return false;
        let set = this.#topLevels.get(block);
        if (set === undefined) {
            set = new Set(functionBody(block) ?? []);
            this.#topLevels.set(block, set);
        }
        return set.has(statement);
    }

    isWithin(ancestor: Node, node: Node): boolean {
        for (let above = this.#scopes.parentOf(node); above !== undefined; above = this.#scopes.parentOf(above)) if (above === ancestor) return true;
        return false;
    }

    /**
     * Whether `a` comes before `b` in document order (a depth-first walk in source order, the tree as it now is:
     * after unflattening, that is execution order). An ancestor comes before what it contains.
     */
    precedes(a: Node, b: Node): boolean {
        if (a === b) return false;
        const { chain, index } = this.#ancestryOf(a);
        let child = b;
        for (let parent = this.#scopes.parentOf(b); parent !== undefined; child = parent, parent = this.#scopes.parentOf(parent)) {
            if (parent === a) return true;
            const at = index.get(parent);
            if (at !== undefined) return at > 0 && this.#positionOf(parent, chain[at - 1] as Node) < this.#positionOf(parent, child);
        }
        return false;
    }

    /**
     * Whether a definition's statement runs once per pass through its list: directly in the body, or in a nested
     * statement list, where reads count only inside that list, after the definition (`limits`).
     */
    placed(block: Node, statement: Node, definition: Node): boolean {
        if (this.isTopLevel(block, statement)) return true;
        const list = referenceParent(this.#scopes, statement);
        const listed = list?.type === "SwitchCase" ? list.consequent : list?.type === "BlockStatement" || list?.type === "StaticBlock" ? list.body : [];
        if (list === undefined || !this.isWithin(block, list) || !(listed as readonly Node[]).includes(statement)) return false;
        this.#limits.set(definition, list);
        return true;
    }

    /**
     * `use` runs after `definition`: it comes later in `block`'s document order (within the definition's statement
     * list, see `limits`) and, when it sits in a function declaration (hoisted), that function only runs after
     * `definition` too (`runsAfter`). A use in a function declaration runs when the function is called, wherever it
     * is declared: then only the calls count (a helper declared before the slot it reads is set). A definition inside
     * a declaration is in a nested list, whose `limits` its calls from outside don't meet.
     */
    reachesAfter(block: Node, definition: Node, use: Node): boolean {
        if (ORDERED[definition.type] !== true || ORDERED[use.type] !== true || !this.isWithin(block, definition) || !this.isWithin(block, use)) return false;
        const declaration = this.#declarationAround(block, use);
        if (declaration !== undefined) return this.#runsAfter(block, definition, declaration);
        const limit = this.#limits.get(definition);
        return this.precedes(definition, use) && (limit === undefined || this.isWithin(limit, use));
    }

    /**
     * The body of the function `declaration` (in `block`) only runs after `definition`: every reference to it does
     * (`reachesAfter`). Checked coinductively: a declaration already being checked (recursion, mutual recursion) is
     * assumed to run after. Proof: let C be the declarations a successful outermost check went through. Each of their
     * references either comes after `definition` outside any declaration, or sits in a member of C. A function's
     * object is only reached by evaluating its name (it is created when its scope is entered and only escapes through
     * a reference; `arguments.callee` and `f.caller` need it running already; a block function whose value Annex B
     * also puts in a function-wide binding is refused: `annexBEscapes`), so if a member of C ran before
     * `definition`, take the earliest evaluation of a reference to a member of C before `definition`: it can't be
     * outside the declarations (it would come after), so it is inside a member of C, which was then running before
     * `definition`, so a reference to that member was evaluated even earlier: a contradiction. Verdicts reached under
     * an assumption are only kept once the outermost check succeeds (they are then all proven); a failure is kept
     * right away.
     */
    #runsAfter(block: Node, definition: Node, declaration: Node): boolean {
        let known = this.#verdicts.get(definition);
        let stack = this.#checking.get(definition);
        if (known === undefined || stack === undefined) {
            known = new Map();
            stack = new Set();
            this.#verdicts.set(definition, known);
            this.#checking.set(definition, stack);
        }
        const verdict = known.get(declaration);
        if (verdict !== undefined) return verdict;
        if (stack.has(declaration)) return true;
        const fn = declaration.type === "FunctionDeclaration" && declaration.id !== null ? this.#scopes.variableOf(declaration.id) : undefined;
        if (fn === undefined || this.#globalSafe(fn) !== true || this.#scopes.annexBEscapes(fn)) {
            known.set(declaration, false);
            return false;
        }
        const outermost = stack.size === 0;
        const mark = this.#reached.length;
        stack.add(declaration);
        this.#depth++;
        this.#reached.push({ known, declaration });
        const safe = this.#scopes.staticReferences(fn).every((reference) => this.reachesAfter(block, definition, reference.identifier as unknown as Node));
        stack.delete(declaration);
        this.#depth--;
        if (!safe) known.set(declaration, false);
        // A failed outermost check for this definition proves none of what it assumed.
        if (outermost && !safe) this.#reached.length = mark;
        if (this.#depth === 0) {
            for (const proven of this.#reached) proven.known.set(proven.declaration, true);
            this.#reached = [];
        }
        return safe;
    }

    /** The nearest function declaration around `use` inside `block`: hoisted, so callable before what precedes it. */
    #declarationAround(block: Node, use: Node): Node | undefined {
        for (let above = this.#scopes.parentOf(use); above !== undefined && above !== block; above = this.#scopes.parentOf(above)) if (above.type === "FunctionDeclaration") return above;
        return undefined;
    }

    #positionOf(parent: Node, child: Node): number {
        let positions = this.#childPositions.get(parent);
        if (positions === undefined) {
            const found = new Map<Node, number>();
            forEachChild(parent, (node) => void found.set(node, found.size));
            positions = found;
            this.#childPositions.set(parent, positions);
        }
        return positions.get(child) ?? -1;
    }

    #ancestryOf(node: Node): Ancestry {
        let ancestry = this.#ancestries.get(node);
        if (ancestry === undefined) {
            const chain: Node[] = [node];
            for (let above = this.#scopes.parentOf(node); above !== undefined; above = this.#scopes.parentOf(above)) chain.push(above);
            ancestry = { chain, index: new Map(chain.map((link, i) => [link, i])) };
            this.#ancestries.set(node, ancestry);
        }
        return ancestry;
    }
}
