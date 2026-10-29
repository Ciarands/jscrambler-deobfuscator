import type { Node } from "../../core/ast.js";
import type { PassLog } from "../../core/log.js";
import type { ScopeInfo } from "../../core/scope.js";

/** The rewrites of the unminify pass, as counted in its stats. */
export const TRANSFORMS = [
    "blockStatements",
    "splitDeclarations",
    "computedKeys",
    "shorthand",
    "splitForLoopVars",
    "forToWhile",
    "invertBooleanLogic",
    "logicalToIf",
    "mergeElseIf",
    "removeDoubleNot",
    "templateStrings",
    "ternaryToIf",
    "truncateNumbers",
    "typeofUndefined",
    "unaryStatements",
    "returnVoid",
    "sequences",
    "objectLiterals",
    "regexEscapes",
    "labeledBlocks",
    "yoda",
] as const;

export type Transform = (typeof TRANSFORMS)[number];

export class UnminifyContext {
    readonly scopes: ScopeInfo;
    readonly log: PassLog;
    readonly counts: Record<Transform, number>;
    readonly #hasWith: boolean;

    constructor(scopes: ScopeInfo, log: PassLog) {
        this.scopes = scopes;
        this.log = log;
        this.counts = Object.fromEntries(TRANSFORMS.map((name) => [name, 0])) as Record<Transform, number>;
        this.#hasWith = scopes.manager.scopes.some((scope) => scope.type === "with");
    }

    /** Count a rewrite of `node` and log it. */
    did(transform: Transform, node: Node): void {
        this.counts[transform]++;
        if (this.log.debugging) this.log.debug(transform, node);
    }

    /** Log why a node that has a rewrite's shape keeps its form. */
    refused(reason: string, node: Node): void {
        if (this.log.debugging) this.log.debug(reason, node);
    }

    /**
     * Whether the identifier reads the global of its name: no declaration of the name around it and no `with` that
     * could answer it. Identifiers created after the scope analysis (unknown to it) qualify when no scope in the
     * program declares the name and the program has no `with`.
     */
    isGlobal(identifier: Node): boolean {
        if (identifier.type !== "Identifier") return false;
        const bound = this.scopes.nameBoundAt(identifier, identifier.name);
        if (bound === undefined) return !this.#hasWith && !this.scopes.declaresName(identifier.name);
        if (bound || !this.#hasWith) return !bound;
        for (let scope = this.scopes.referenceOf(identifier)?.from ?? null; scope !== null; scope = scope.upper) if (scope.type === "with") return false;
        return true;
    }
}
