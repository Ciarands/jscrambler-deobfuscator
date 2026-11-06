import type { MemberExpression, Node } from "./ast.js";
import type { Analysis } from "./constants.js";
import { evaluate } from "./evaluate.js";
import type { GlobalReach, Scope, Variable } from "./scope.js";

export type Refusal = { readonly reason: string; readonly node: Node };

/** The function a definition gives its binding: a declaration, or a declarator's function or arrow. */
const functionOf = (definition: Node): Node | undefined =>
    definition.type === "FunctionDeclaration"
        ? definition
        : definition.type === "VariableDeclarator" && (definition.init?.type === "FunctionExpression" || definition.init?.type === "ArrowFunctionExpression")
          ? definition.init
          : undefined;

/** Whether code could reach a script global as a property of the global object (see `constantEnv`). */
export class GlobalEscape {
    readonly #analysis: Pick<Analysis, "scopes" | "order" | "arrays" | "env" | "log" | "memo">;
    readonly #dynamic: Scope | undefined;
    #reach: GlobalReach | undefined;
    /**
     * Each global member's key, where it evaluates: kept once known (a failure may be a lookup still in progress, and
     * an answer under a table being validated holds only for that check).
     */
    readonly #memberKeys = new Map<Node, string>();
    readonly #checks = new Map<Variable, boolean | undefined>();

    constructor(analysis: Pick<Analysis, "scopes" | "order" | "arrays" | "env" | "log" | "memo">) {
        this.#analysis = analysis;
        this.#dynamic = analysis.scopes.manager.scopes.find((scope) => scope.type === "with" || scope.directCallToEvalScope);
    }

    /** Whether no refusal applies to `variable` (`ConstantEnv.onlyByName`); `undefined` while that is being found. */
    safe(variable: Variable): boolean | undefined {
        return this.#analysis.memo(this.#checks, variable, () => {
            const [refusal] = this.refusals(variable, false);
            if (refusal !== undefined) this.#analysis.log?.debug(`${variable.name} is not constant: ${refusal.reason}`, refusal.node);
            return refusal === undefined;
        });
    }

    /**
     * Why code could reach the script global `variable` as a property of the global object (see `constantEnv`); none
     * for any other binding. Keys are evaluated as the current check sees them. Only the first reason unless `all`.
     */
    refusals(variable: Variable, all: boolean): Refusal[] {
        if (variable.scope.type !== "global") return [];
        const { scopes, order, arrays } = this.#analysis;
        const node = variable.identifiers[0] as unknown as Node;
        if (this.#dynamic !== undefined) return [{ reason: "the program uses with or direct eval", node: this.#dynamic.block as unknown as Node }];
        const names = (this.#reach ??= scopes.globalReach());
        if (names.spelled.has(variable.name)) return [{ reason: `the program spells ${variable.name} as a property or a string`, node }];
        // The code of a function nothing reads runs only once something reaches it: for its own binding's check, the
        // global object it would reach doesn't count.
        const unrun = scopes.staticReferences(variable).some((reference) => reference.isRead())
            ? []
            : variable.defs.map((def) => functionOf(def.node as unknown as Node)).filter((fn) => fn !== undefined);
        const counts = (place: Node): boolean => !unrun.some((fn) => order.isWithin(fn, place));
        const escape = names.escapes.find(counts);
        if (escape !== undefined) return [{ reason: "the global object's value goes somewhere, where any key may be read", node: escape }];
        const refusals: Refusal[] = [];
        for (const member of names.members) {
            if (!counts(member)) continue;
            const key = this.#memberKey(member);
            if (key !== undefined) {
                if (key === variable.name) refusals.push({ reason: `the global object is used with the key ${variable.name}`, node: member });
            } else if (!arrays.keyOfTable(member.property, variable.name)) {
                refusals.push({ reason: "the global object is used with an unknown key", node: member });
            }
            if (refusals.length > 0 && !all) break;
        }
        return refusals;
    }

    #memberKey(member: MemberExpression): string | undefined {
        const validating = this.#analysis.arrays.validating;
        const known = validating ? undefined : this.#memberKeys.get(member);
        if (known !== undefined) return known;
        const key = evaluate(member.property, this.#analysis.env);
        if (!key.ok) return undefined;
        const name = String(key.value);
        if (!validating) this.#memberKeys.set(member, name);
        return name;
    }
}
