import type { CallExpression, Expression, Node, Statement } from "../../core/ast.js";
import { isFunctionNode } from "../../core/ast.js";
import type { Value } from "../../core/evaluate.js";
import type { Variable } from "../../core/scope.js";
import type { Path } from "../../core/traverse.js";
import type { PropertyPath } from "../runtime/model.js";

export interface Case {
    readonly label: Value;
    readonly formula: Expression;
    readonly problem: string | undefined;
}

/** `G.k`: a selector method storing its argument in the builder's state, and a calculation switching on that state. */
export interface Calculator {
    readonly path: PropertyPath;
    readonly name: string;
    readonly selector: string;
    readonly calculation: string;
    readonly cases: readonly Case[];
    /** The calculation's `var a = arguments` local: `a[i]` in a formula is the call's argument `i`. */
    readonly args: Variable;
    readonly definition: Statement;
}

export interface Place {
    readonly parent: Node;
    readonly key: string;
    readonly index: number | null;
}

export interface Site {
    readonly call: CallExpression;
    readonly calculator: Calculator;
    readonly role: "selector" | "calculation";
    readonly reference: Node;
    readonly wrapper: string | undefined;
    /** Where the call sits in each ancestor, nearest first, up to its function (or the program). */
    readonly places: readonly Place[];
}

/** Every call of a calculator's methods (directly or through a wrapper) whose target is proven. */
export type Sites = ReadonlyMap<CallExpression, Site>;

export interface Resolution {
    readonly site: Site;
    readonly selected: Case | undefined;
    readonly args: readonly Expression[];
    /** Why the arguments are bound to parameters before the case's expression runs (`orderProblem`), if they are. */
    readonly bound: string | undefined;
}

export type Refusal = { readonly ok: false; readonly reason: string; readonly node: Node };

export const refusal = (reason: string, node: Node): Refusal => ({ ok: false, reason, node });

export const isOwnSelector = (sites: Sites, node: Node, calculator: Calculator): boolean => {
    const site = node.type === "CallExpression" ? sites.get(node) : undefined;
    return site !== undefined && site.calculator === calculator && site.role === "selector";
};

export const placesOf = (path: Path): Place[] => {
    const places: Place[] = [];
    for (let p: Path | null = path; p !== null && p.parent !== null && p.key !== null; p = p.parentPath) {
        places.push({ parent: p.parent, key: p.key, index: p.index });
        if (isFunctionNode(p.parent)) break;
    }
    return places;
};
