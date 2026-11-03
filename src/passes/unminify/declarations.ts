import type { Expression, Node, Program, Statement, VariableDeclaration, VariableDeclarator } from "../../core/ast.js";
import { isBindingName, isFunctionNode, isLoopNode } from "../../core/ast.js";
import { at } from "../../core/build.js";
import type { Reference, ScopeInfo, Variable } from "../../core/scope.js";
import { traverse } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";
import { removeDeclarators } from "./statements.js";

/**
 * jscrambler hoists every local into one `var a, b, c;` at the top of its function. A `var x;` moves to the first
 * assignment of `x` (`var x = e;`) when every reference is in the statement list holding it, and becomes a `let` or
 * `const` where that binds the same. The names left at the top are joined back into one `var a, b;`.
 *
 * Moving is exact: a `var` binds function-wide wherever it stands, `var x;` does nothing when it runs, and `var x = e;`
 * assigns `x` as `x = e;` does, provided the new place binds `x` to the same variable. It does: every reference
 * resolves statically to the variable, so no scope enclosing one binds `x` below the function, and every scope
 * enclosing the list that holds them encloses them too. So no `catch (x)` encloses the new `var` (Annex B would let its
 * initializer write the parameter) and no lexical `x` does (an early error). A `with` that could take a reference
 * leaves the references unknown, and direct `eval` could see the name: both are refused.
 */

type Identifier = Node & { type: "Identifier"; name: string };

/** Code that runs later than where it stands: function bodies, class field initializers, static blocks. */
const DEFERRED: Readonly<Record<string, true>> = {
    FunctionDeclaration: true,
    FunctionExpression: true,
    ArrowFunctionExpression: true,
    PropertyDefinition: true,
    AccessorProperty: true,
    StaticBlock: true,
};

/** Statements holding other statements: a first use inside one means the uses span blocks. */
const COMPOUND: Readonly<Record<string, true>> = {
    BlockStatement: true,
    IfStatement: true,
    TryStatement: true,
    SwitchStatement: true,
    LabeledStatement: true,
    WithStatement: true,
    ForStatement: true,
    ForInStatement: true,
    ForOfStatement: true,
    WhileStatement: true,
    DoWhileStatement: true,
};

const statementsOf = (node: Node): Statement[] | undefined => {
    switch (node.type) {
        case "Program":
            return node.body as Statement[];
        case "BlockStatement":
            return node.body;
        case "SwitchCase":
            return node.consequent;
        default:
            return undefined;
    }
};

const declarationOf = (kind: "var" | "let" | "const", declarators: VariableDeclarator[], origin: Node): VariableDeclaration =>
    at<VariableDeclaration>({ type: "VariableDeclaration", kind, declarations: declarators, declare: false }, origin);

const declaratorOf = (id: Identifier, init: Expression | null): VariableDeclarator => at<VariableDeclarator>({ type: "VariableDeclarator", id, init, definite: false }, id);

/** The statement that first uses the name, as a declaration site: its write and what runs before the binding holds a value. */
interface Site {
    readonly write: Identifier;
    readonly initializer: Node;
    /** A loop head: a lexical declaration there is the loop's, with a copy per iteration. */
    readonly head: boolean;
}

/** `x = e;`, `for (x = e; ...)`, `for (x in/of e)` (also labelled), when `x` is one of `uses`. */
const siteOf = (statement: Statement, uses: ReadonlySet<Node>): Site | undefined => {
    if (statement.type === "ExpressionStatement") {
        const expression = statement.expression;
        if (expression.type !== "AssignmentExpression" || expression.operator !== "=" || !uses.has(expression.left)) return undefined;
        return { write: expression.left as Identifier, initializer: expression.right, head: false };
    }
    let loop: Statement = statement;
    while (loop.type === "LabeledStatement") loop = loop.body;
    if (loop.type === "ForStatement") {
        const init = loop.init;
        if (init?.type !== "AssignmentExpression" || init.operator !== "=" || !uses.has(init.left)) return undefined;
        return { write: init.left as Identifier, initializer: init.right, head: true };
    }
    if ((loop.type === "ForInStatement" || loop.type === "ForOfStatement") && uses.has(loop.left)) return { write: loop.left as Identifier, initializer: loop.right, head: true };
    return undefined;
};

interface Plan {
    readonly declarator: VariableDeclarator;
    readonly list: Statement[];
    readonly statement: Statement;
    readonly site: Site;
    readonly kind: "var" | "let" | "const";
}

/** The bare `var x;` declarator of `variable` standing in a statement list; `undefined` when it has none. */
const bareDeclarator = (variable: Variable, scopes: ScopeInfo): VariableDeclarator | undefined => {
    for (const def of variable.defs) {
        if (def.type !== "Variable" || def.parent.kind !== "var") continue;
        const declarator = def.node as unknown as VariableDeclarator;
        if (declarator.init !== null || declarator.id.type !== "Identifier") continue;
        const declaration = def.parent as unknown as Statement;
        const holder = scopes.parentOf(declaration);
        if (holder !== undefined && statementsOf(holder)?.includes(declaration) === true) return declarator;
    }
    return undefined;
};

class Planner {
    readonly #scopes: ScopeInfo;
    readonly #context: UnminifyContext;
    readonly #indexes = new WeakMap<Statement[], Map<Node, number>>();

    constructor(scopes: ScopeInfo, context: UnminifyContext) {
        this.#scopes = scopes;
        this.#context = context;
    }

    #indexOf(list: Statement[], statement: Node): number | undefined {
        let indexes = this.#indexes.get(list);
        if (indexes === undefined) {
            indexes = new Map(list.map((item, index) => [item as Node, index]));
            this.#indexes.set(list, indexes);
        }
        return indexes.get(statement);
    }

    /** `node`'s ancestors from `root` down, `node` included; `undefined` when `root` isn't one. */
    #chain(node: Node, root: Node): Node[] | undefined {
        const chain = [node];
        for (let current = node; current !== root;) {
            const parent = this.#scopes.parentOf(current);
            if (parent === undefined) return undefined;
            chain.push(parent);
            current = parent;
        }
        return chain.toReversed();
    }

    #refuse(reason: string, node: Node): undefined {
        this.#context.refused(`keeps the hoisted var: ${reason}`, node);
        return undefined;
    }

    plan(variable: Variable, evalSees: boolean): Plan | undefined {
        const scopes = this.#scopes;
        const declarator = bareDeclarator(variable, scopes);
        if (declarator === undefined) return undefined;
        if (variable.defs.length !== 1) return this.#refuse("the name has another declaration in its function", declarator);
        if (evalSees) return this.#refuse("a direct eval can see it", declarator);
        const references = scopes.references(variable);
        if (references === undefined) return this.#refuse("a with statement can intercept it", declarator);
        if (references.length === 0) return this.#refuse("it is never used", declarator);
        const root = variable.scope.block as unknown as Node;
        const chains: Node[][] = [];
        for (const reference of references) {
            const identifier = reference.identifier as unknown as Node;
            if (scopes.parentOf(identifier)?.type === "FunctionDeclaration") return this.#refuse("a block function of the name writes it (Annex B)", declarator);
            const chain = this.#chain(identifier, root);
            if (chain === undefined) return this.#refuse("one of its references is outside the tree", declarator);
            chains.push(chain);
        }

        // The smallest statement list of the function's own code holding every reference.
        let common = Math.min(...chains.map((chain) => chain.length));
        const first = chains[0] as Node[];
        for (const chain of chains) while (common > 0 && chain[common - 1] !== first[common - 1]) common--;
        let depth = -1;
        let list: Statement[] | undefined;
        for (let k = 0; k < common; k++) {
            const node = first[k] as Node;
            if (k > 0 && DEFERRED[node.type] === true) break;
            const statements = statementsOf(node);
            if (statements !== undefined && chains.every((chain) => this.#indexOf(statements, chain[k + 1] as Node) !== undefined)) {
                depth = k;
                list = statements;
            }
        }
        if (list === undefined) return this.#refuse("no statement list of its function holds every use", declarator);
        const indexes = chains.map((chain) => this.#indexOf(list, chain[depth + 1] as Node) as number);
        const index = Math.min(...indexes);
        const statement = list[index] as Statement;
        const site = siteOf(statement, new Set(references.map((reference) => reference.identifier as unknown as Node)));
        if (site === undefined) {
            const reason = COMPOUND[statement.type] === true ? "its first use is inside a compound statement, not `x = e;`" : "its first use is not an assignment `x = e;`";
            return this.#refuse(reason, declarator);
        }

        let inLoop = site.head;
        for (let k = depth; k > 0 && !inLoop; k--) inLoop = isLoopNode(first[k]);

        const kind = this.#lexicalKind(variable, references, chains, indexes, index, depth, site, inLoop);
        return { declarator, list, statement, site, kind: kind ?? "var" };
    }

    #keepVar(reason: string, node: Node): undefined {
        this.#context.refused(`keeps the moved declaration a var: ${reason}`, node);
        return undefined;
    }

    /**
     * `let` (`const` with one write) declares the same binding as the moved `var` when nothing can tell them apart: no
     * use before the declaration runs (so none in its dead zone) and none after the loop it heads; none in a function
     * declaration (hoisted, it may run first); in a loop, no closure that could keep one iteration's binding. No other
     * declaration of the name can be in its block: every reference resolves to the variable. A script's top-level `var`
     * is also a global object property: those stay.
     */
    #lexicalKind(
        variable: Variable,
        references: readonly Reference[],
        chains: readonly Node[][],
        indexes: readonly number[],
        index: number,
        depth: number,
        site: Site,
        inLoop: boolean
    ): "let" | "const" | undefined {
        const node = site.write;
        if (variable.scope.type !== "function") return this.#keepVar("only a function's var becomes lexical (a script's is a global object property)", node);
        if (!isBindingName(variable.name)) return this.#keepVar("its name can't be declared lexically", node);
        for (let i = 0; i < chains.length; i++) {
            const chain = chains[i] as Node[];
            const identifier = chain[chain.length - 1] as Node;
            if (identifier === site.write) continue;
            if (chain.includes(site.initializer)) return this.#keepVar("its initializer uses it", identifier);
            if (indexes[i] !== index && site.head) return this.#keepVar("it is used after the loop its head declares it in", identifier);
            for (let k = depth + 1; k < chain.length; k++) {
                const ancestor = chain[k] as Node;
                if (ancestor.type === "FunctionDeclaration") return this.#keepVar("a function declaration (hoisted) uses it", identifier);
                if (inLoop && DEFERRED[ancestor.type] === true) return this.#keepVar("a closure in a loop captures it", identifier);
            }
        }
        return references.filter((reference) => reference.isWrite()).length === 1 ? "const" : "let";
    }
}

const isBareVar = (statement: Statement | undefined): statement is VariableDeclaration =>
    statement?.type === "VariableDeclaration" && statement.kind === "var" && statement.declarations.every((declarator) => declarator.init === null && declarator.id.type === "Identifier");

/** `var a; var b;` -> `var a, b;`: declarations without initializers do nothing when they run. */
const joinBareVars = (list: Statement[], context: UnminifyContext): void => {
    for (let i = 0; i < list.length; i++) {
        let end = i;
        while (isBareVar(list[end])) end++;
        if (end - i < 2) continue;
        const run = list.slice(i, end) as VariableDeclaration[];
        context.did("joinDeclarations", run[0] as Node);
        list.splice(
            i,
            end - i,
            declarationOf(
                "var",
                run.flatMap((statement) => statement.declarations),
                run[0] as Node
            )
        );
    }
};

/**
 * Moves hoisted `var x;` declarations to the first assignment, promoting them to `let`/`const` where exact, then joins
 * the ones left at the top of each function. Needs `scopes` analysed on the program as it stands.
 */
export const placeDeclarations = (program: Program, scopes: ScopeInfo, context: UnminifyContext): void => {
    const planner = new Planner(scopes, context);
    const evalAnywhere = scopes.manager.scopes.some((scope) => scope.directCallToEvalScope);
    const plans: Plan[] = [];
    for (const scope of scopes.manager.scopes) {
        if (scope.type !== "function" && scope.type !== "global" && scope.type !== "module") continue;
        const evalSees = scope.type === "global" ? evalAnywhere : scope.dynamic;
        for (const variable of scope.variables) {
            const plan = planner.plan(variable, evalSees);
            if (plan !== undefined) plans.push(plan);
        }
    }

    const moved = new Set<Node>();
    for (const { declarator, list, statement, site, kind } of plans) {
        context.did("moveDeclarations", declarator);
        if (kind !== "var") context.did(kind === "const" ? "constDeclarations" : "letDeclarations", site.write);
        moved.add(declarator);
        if (statement.type === "ExpressionStatement") {
            list[list.indexOf(statement)] = declarationOf(kind, [declaratorOf(site.write, site.initializer as Expression)], statement);
            continue;
        }
        let loop: Statement = statement;
        while (loop.type === "LabeledStatement") loop = loop.body;
        if (loop.type === "ForStatement") loop.init = declarationOf(kind, [declaratorOf(site.write, site.initializer as Expression)], site.write);
        else if (loop.type === "ForInStatement" || loop.type === "ForOfStatement") loop.left = declarationOf(kind, [declaratorOf(site.write, null)], site.write);
    }
    if (moved.size > 0) removeDeclarators(program, moved);

    joinBareVars(program.body as Statement[], context);
    traverse(program, {
        BlockStatement(path) {
            if (isFunctionNode(path.parent) && path.key === "body") joinBareVars(path.node.body, context);
        },
    });
};
