import type { Expression, FunctionLike, Node } from "./ast.js";
import type { Analysis } from "./constants.js";
import type { Value } from "./evaluate.js";
import { binary, evaluate, FAIL } from "./evaluate.js";
import { referenceParent } from "./execution-order.js";
import type { Reference, Variable } from "./scope.js";

export type Constant = { readonly value: Value; readonly after: Node };

/** `value` at `definition`, then `steps` (`x = w;`/`x += w;`) in the same statement list; holds after `after`. */
export interface Definition {
    readonly value: Node;
    readonly definition: Node;
    readonly statement: Node;
    readonly steps: readonly { readonly operator: "=" | "+="; readonly value: Expression }[];
    readonly after: Node;
}

/** `after` undefined: a declaration, held from scope entry. */
interface FunctionBinding {
    readonly fn: FunctionLike;
    readonly after: Node | undefined;
    readonly block: Node;
}

/** The values bindings hold for good: constants and functions (see `constantEnv`). */
export class BindingConstants {
    readonly #analysis: Pick<Analysis, "scopes" | "order" | "globals" | "env" | "log" | "memo">;
    readonly #definitions = new Map<Variable, Definition | undefined>();
    readonly #constants = new Map<Variable, Constant | undefined>();
    readonly #functions = new Map<Variable, FunctionBinding | undefined>();

    constructor(analysis: Pick<Analysis, "scopes" | "order" | "globals" | "env" | "log" | "memo">) {
        this.#analysis = analysis;
    }

    /** A binding's definition when it is written once (`findDefinition` without steps). */
    singleDefinition(variable: Variable): Definition | undefined {
        const built = this.#definitionOf(variable);
        return built?.steps.length === 0 ? built : undefined;
    }

    constantOf(variable: Variable): Constant | undefined {
        return this.#analysis.memo(this.#constants, variable, () => {
            const { order, env, globals, log } = this.#analysis;
            // A read of the binding that evaluating its value needs makes the value fail to evaluate.
            const built = this.#definitionOf(variable);
            if (built === undefined || !order.placed(variable.scope.block as unknown as Node, built.statement, built.after)) return undefined;
            // `x = w` gives `w`, whatever `x` held; `x += w` reads `x`, then evaluates `w`, then adds: on primitives,
            // what `binary` computes.
            let result = evaluate(built.value, env);
            for (const step of built.steps) {
                if (step.operator === "=") {
                    result = evaluate(step.value, env);
                    continue;
                }
                if (!result.ok) continue;
                const appended = evaluate(step.value, env);
                result = appended.ok ? binary("+", result.value, appended.value) : FAIL;
            }
            if (!result.ok || globals.safe(variable) !== true) return undefined;
            if (built.steps.length > 0) log?.debug(`${variable.name} is written ${built.steps.length + 1} times in one statement list: constant after the last`, built.after);
            return { value: result.value, after: built.after };
        });
    }

    /** `ConstantEnv.functionAt`. */
    functionAt(identifier: Node): FunctionLike | undefined {
        const variable = identifier.type === "Identifier" ? this.#analysis.scopes.variableOf(identifier) : undefined;
        const binding = variable === undefined ? undefined : this.#functionBindingOf(variable);
        if (binding === undefined) return undefined;
        return binding.after === undefined || this.#analysis.order.reachesAfter(binding.block, binding.after, identifier) ? binding.fn : undefined;
    }

    /**
     * The function a binding holds for good, and from where on: a function declaration, never written (from its
     * scope's entry: a block's for one in a block, which only references inside the block resolve to), or a function
     * or arrow expression it gets once, as constants do (after the definition).
     */
    #functionBindingOf(variable: Variable): FunctionBinding | undefined {
        return this.#analysis.memo(this.#functions, variable, () => {
            const { scopes, order, globals } = this.#analysis;
            const block = variable.scope.block as unknown as Node;
            const [def] = variable.defs;
            if (variable.defs.length === 1 && def?.type === "FunctionName") {
                const declaration = def.node as unknown as Node;
                if (declaration.type !== "FunctionDeclaration") return undefined;
                if (scopes.staticReferences(variable).some((reference) => reference.isWrite()) || globals.safe(variable) !== true) return undefined;
                return { fn: declaration, after: undefined, block };
            }
            const single = this.singleDefinition(variable);
            const fn = single?.value;
            if (single === undefined || (fn?.type !== "FunctionExpression" && fn?.type !== "ArrowFunctionExpression")) return undefined;
            if (!order.placed(block, single.statement, single.definition) || globals.safe(variable) !== true) return undefined;
            return { fn, after: single.definition, block };
        });
    }

    #definitionOf(variable: Variable): Definition | undefined {
        if (this.#definitions.has(variable)) return this.#definitions.get(variable);
        const found = this.#findDefinition(variable);
        this.#definitions.set(variable, found);
        return found;
    }

    /**
     * A binding's value and where it gets it: `var x = v;` (the declarator), or `var x;` written once, by a statement
     * `x = v;` (that statement). Or a binding written several times, all by its declarators (`var x = ""; var x =
     * "ab";` declares one binding) and statements `x = w;` and `x += w;` in one statement list (a string built in
     * pieces: `var s = "ab"; s += "cd";`), the first of them in document order an initializer or an `=`: reads after the
     * last write (`after`) see what they compute in order; reads before it aren't answered. The list runs its
     * statements in order and is only entered at its start, so a pass through it that reaches `after` ran each write
     * once, in order, from the first.
     */
    #findDefinition(variable: Variable): Definition | undefined {
        const { scopes, order } = this.#analysis;
        const parentOf = (node: Node): Node | undefined => referenceParent(scopes, node);
        const [def] = variable.defs;
        if (def === undefined || (variable.defs.length > 1 && !variable.defs.every((other) => other.type === "Variable" && (other.parent as { kind?: string } | null)?.kind === "var")))
            return undefined;
        if (def.type !== "Variable") return undefined;
        const declarator = def.node as unknown as Node;
        const declaration = def.parent as unknown as Node | null;
        if (declarator.type !== "VariableDeclarator" || declarator.id.type !== "Identifier" || declaration?.type !== "VariableDeclaration") return undefined;
        const writes: { operator: "=" | "+="; value: Expression; definition: Node; statement: Node }[] = [];
        for (const write of scopes.staticReferences(variable)) {
            if (!write.isWrite()) continue;
            const initialized = write.init === true ? parentOf(write.identifier as unknown as Node) : undefined;
            if (initialized?.type === "VariableDeclarator" && initialized.init !== null) {
                writes.push({ operator: "=", value: initialized.init, definition: initialized, statement: parentOf(initialized) as Node });
                continue;
            }
            const operator = this.#assigningStatement(write, "=") !== undefined ? "=" : this.#assigningStatement(write, "+=") !== undefined ? "+=" : undefined;
            const statement = operator === undefined ? undefined : parentOf(parentOf(write.identifier as unknown as Node) as Node);
            if (operator === undefined || statement?.type !== "ExpressionStatement" || statement.expression.type !== "AssignmentExpression") return undefined;
            writes.push({ operator, value: statement.expression.right, definition: statement, statement });
        }
        const [only] = writes;
        if (writes.length === 1 && only?.operator === "=") {
            // `var x; x = v;`: a `let` would be in its dead zone before the declaration, a `const` can't be assigned.
            if (only.definition !== declarator && declaration.kind !== "var") return undefined;
            return { value: only.value, definition: only.definition, statement: only.statement, steps: [], after: only.definition };
        }
        // (A `const` throws at its second write: nothing after that write runs.)
        if (writes.length < 2) return undefined;
        const list = parentOf(only?.statement as Node);
        if (writes.some((write) => parentOf(write.statement) !== list)) return undefined;
        writes.sort((a, b) => (order.precedes(a.definition, b.definition) ? -1 : 1));
        const [first, ...steps] = writes;
        const last = steps.at(-1);
        if (first === undefined || first.operator !== "=" || last === undefined) return undefined;
        return { value: first.value, definition: first.definition, statement: first.statement, steps, after: last.definition };
    }

    #assigningStatement(write: Reference, operator: string): Node | undefined {
        const { scopes } = this.#analysis;
        const id = write.identifier as unknown as Node;
        const assignment = referenceParent(scopes, id);
        const statement = assignment === undefined ? undefined : referenceParent(scopes, assignment);
        return assignment?.type === "AssignmentExpression" && assignment.operator === operator && assignment.left === id && statement?.type === "ExpressionStatement" ? statement : undefined;
    }
}
