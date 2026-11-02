import type { Node } from "../../core/ast.js";
import type { EvaluateEnv } from "../../core/evaluate.js";
import { evaluate } from "../../core/evaluate.js";
import type { ScopeInfo, Variable } from "../../core/scope.js";
import { slotArray, slotOf } from "../emulate/builders.js";

const GETTER = "a property read (possible getter)";
const GLOBAL_READ = "a global read (possible getter)";

/** What reading a local or a slot of a local array does: whether it may run code or throw, and what it may read. */
export class LocalReads {
    readonly #slotArrays = new Map<Variable, boolean>();

    constructor(
        readonly scopes: ScopeInfo,
        readonly env: EvaluateEnv,
        /** The program's parent links, as of before the rewrite. */
        readonly parents: () => ReadonlyMap<Node, Node>
    ) {}

    /** A binding whose read can't throw or run code: a `var`, parameter, function or catch name, or `arguments`. */
    safeBinding(identifier: Node): boolean {
        const variable = this.scopes.variableOf(identifier);
        if (variable === undefined) return false;
        if (variable.defs.length === 0) return variable.name === "arguments" && variable.scope.type === "function";
        return variable.defs.every((def) => def.type === "Parameter" || def.type === "FunctionName" || def.type === "CatchClause" || (def.type === "Variable" && def.parent.kind === "var"));
    }

    /**
     * `S[i]` with `S` a slot array: every read of it finds that array (not the `undefined` its hoisted `var` holds
     * before, which a slot read throws on), whose index properties are plain data: reading one runs nothing (an index
     * past its end looks up the prototypes: relies on model 7: builtins intact).
     */
    slotRead(node: Node): boolean {
        const slot = slotOf(node, this.scopes);
        if (slot === undefined) return false;
        const { variable } = slot;
        let known = this.#slotArrays.get(variable);
        if (known === undefined) {
            // `inert`, `first`: the declaration is its function's first code and its elements call nothing, so the array
            // is stored before code that could read it runs. Sufficient, not necessary (any declaration every read
            // follows would do, and so would `let`): a conservative restriction.
            known = slotArray(variable, this.scopes.references(variable), this.parents(), { init: "inert", placement: "first", uses: "index" });
            this.#slotArrays.set(variable, known);
        }
        return known;
    }

    localStore(target: Node): boolean {
        return target.type === "Identifier" ? this.safeBinding(target) : this.slotRead(target);
    }

    /** Why an argument can't be put into the case's expression (or dropped): `undefined` for constants, safe locals and slot reads. */
    substitutable(node: Node): string | undefined {
        if (evaluate(node, this.env).ok) return undefined;
        if (node.type === "Identifier") return this.safeBinding(node) ? undefined : GLOBAL_READ;
        if (node.type === "ThisExpression" || this.slotRead(node)) return undefined;
        return node.type === "MemberExpression" ? GETTER : `a ${node.type}`;
    }

    /**
     * Whether reading `node`, an argument, after code it doesn't know has run still gives what reading it first did:
     * a slot read `S[i]`, or a `var` or parameter whose binding no other function refers to (code that runs while an
     * operator converts a value is another function's: only a function that names the binding can change it; a
     * recursive call of this one gets bindings of its own), in a function no `eval` or `with` can reach into. A
     * parameter also counts only in a strict function or an arrow: a sloppy function's `arguments` object maps its
     * parameters, and code it is handed to (or `f.arguments`) could write them through it; a strict one's doesn't map,
     * and an arrow has none.
     */
    stableAcrossCalls(node: Node): boolean {
        const binding = node.type === "Identifier" ? node : this.slotRead(node) && node.type === "MemberExpression" ? node.object : undefined;
        const variable = binding === undefined ? undefined : this.scopes.variableOf(binding);
        if (variable === undefined || variable.scope.dynamic || variable.defs.length !== 1) return false;
        const [def] = variable.defs;
        const unmapped = def?.type === "Parameter" && (variable.scope.isStrict || (variable.scope.block as unknown as Node).type === "ArrowFunctionExpression");
        if (!unmapped && (def?.type !== "Variable" || def.parent.kind !== "var")) return false;
        const own = variable.scope.variableScope;
        const references = this.scopes.references(variable);
        return references !== undefined && references.every((reference) => reference.from.variableScope === own);
    }

    /**
     * Whether `node` only ever has a primitive value: literals and operator results, and a function's `var`s whose
     * every write stores one (a `var` read before its first write is `undefined`; a script's are globals other code
     * may write). `seen` guards against cycles.
     */
    primitive(node: Node, seen: Set<Variable> = new Set()): boolean {
        switch (node.type) {
            case "Literal":
                return !("regex" in node && node.regex !== undefined && node.regex !== null);
            case "TemplateLiteral":
            case "UnaryExpression":
            case "BinaryExpression":
            case "UpdateExpression":
                return true;
            case "LogicalExpression":
                return this.primitive(node.left, seen) && this.primitive(node.right, seen);
            case "ConditionalExpression":
                return this.primitive(node.consequent, seen) && this.primitive(node.alternate, seen);
            case "Identifier": {
                if (evaluate(node, this.env).ok) return true;
                const variable = this.scopes.variableOf(node);
                if (variable === undefined || variable.scope.dynamic || variable.scope.type === "global" || !variable.defs.every((def) => def.type === "Variable" && def.parent.kind === "var"))
                    return false;
                if (seen.has(variable)) return true;
                seen.add(variable);
                const references = this.scopes.references(variable);
                return (
                    references !== undefined &&
                    references.every(
                        (reference) => !reference.isWrite() || (reference.writeExpr !== null && reference.writeExpr !== undefined && this.primitive(reference.writeExpr as unknown as Node, seen))
                    )
                );
            }
            default:
                return false;
        }
    }
}
