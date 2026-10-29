import type { Expression, MemberExpression, Node, Statement, VariableDeclaration, VariableDeclarator } from "../core/ast.js";
import { isIdentifierName } from "../core/ast.js";
import { at } from "../core/build.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

const statementOf = (expression: Expression): Statement => at<Statement>({ type: "ExpressionStatement", expression }, expression);

/** Split a statement whose leading expressions are a comma sequence into the sequence's statements plus the rest. */
const split = (statement: Statement): Statement[] | undefined => {
    switch (statement.type) {
        case "ExpressionStatement":
            if (statement.expression.type !== "SequenceExpression") return undefined;
            return statement.expression.expressions.map(statementOf);
        case "ReturnStatement":
        case "ThrowStatement": {
            const argument = statement.argument;
            if (argument?.type !== "SequenceExpression") return undefined;
            const last = argument.expressions.at(-1) as Expression;
            return [...argument.expressions.slice(0, -1).map(statementOf), { ...statement, argument: last }];
        }
        case "IfStatement": {
            const test = statement.test;
            if (test.type !== "SequenceExpression") return undefined;
            const last = test.expressions.at(-1) as Expression;
            return [...test.expressions.slice(0, -1).map(statementOf), { ...statement, test: last }];
        }
        case "VariableDeclaration": {
            // `var a = x, b = (s, y), c;` -> `var a = x; s; var b = y, c;`: the same order, and each name is declared
            // (or, for let/const, initialized) just as late as before when `s` runs.
            if (statement.kind === "using" || statement.kind === "await using") return undefined;
            const k = statement.declarations.findIndex((declarator) => declarator.init?.type === "SequenceExpression");
            if (k === -1) return undefined;
            const declarator = statement.declarations[k] as VariableDeclarator;
            const sequence = declarator.init as Expression & { expressions: Expression[] };
            const before = statement.declarations.slice(0, k);
            const rest = [at<VariableDeclarator>({ ...declarator, init: sequence.expressions.at(-1) as Expression }, declarator), ...statement.declarations.slice(k + 1)];
            return [
                ...(before.length === 0 ? [] : [at<Statement>({ ...statement, declarations: before }, statement)]),
                ...sequence.expressions.slice(0, -1).map(statementOf),
                at<Statement>({ ...statement, declarations: rest }, declarator),
            ];
        }
        default:
            return undefined;
    }
};

/** Positions holding exactly one statement (`if (c) <here>`, loop and label bodies): a split needs a block there. */
const SINGLE_STATEMENT_SLOTS: Record<string, readonly string[]> = {
    IfStatement: ["consequent", "alternate"],
    ForStatement: ["body"],
    ForInStatement: ["body"],
    ForOfStatement: ["body"],
    WhileStatement: ["body"],
    DoWhileStatement: ["body"],
    LabeledStatement: ["body"],
    WithStatement: ["body"],
};

/** Split `statement` until nothing in the result splits further (`return (a, b), c`). */
const splitFully = (statement: Statement): Statement[] | undefined => {
    let current = split(statement);
    if (current === undefined) return undefined;
    for (let changed = true; changed;) {
        changed = false;
        current = current.flatMap((s) => {
            const more = split(s);
            if (more === undefined) return [s];
            changed = true;
            return more;
        });
    }
    return current;
};

/**
 * `var x = <literal>` followed by a declarator or assignment of `x` with another literal: the first literal is never
 * seen. Only a literal: any other value may run code (a call, a getter) that reads `x` and would see the first one.
 * A declarator without an initializer (`var x = 1, x;`) leaves the value as it is.
 */
const overwritten = (declarator: VariableDeclarator | undefined, name: string | undefined, value: Node | null): boolean =>
    value?.type === "Literal" && declarator?.id.type === "Identifier" && declarator.id.name === name && (declarator.init === null || declarator.init.type === "Literal");

const declarationOf = (node: VariableDeclaration, declarations: VariableDeclarator[]): VariableDeclaration =>
    at<VariableDeclaration>({ type: "VariableDeclaration", kind: node.kind, declarations }, node);

/**
 * Declarations whose literal value is replaced right away (`var a = "", a = "keyCode";`, `var b = "";
 * b = "href";`): `var x = <literal>` followed by another declarator of `x`, in the same `var` or the next one, or
 * by the statement `x = e`. The literal is never seen, so only the second value matters, as long as it doesn't read
 * `x` (it would see the literal). Both are in one statement list, so they name one binding, and dropping a repeated
 * declarator leaves the variable declared. What `first` (and `second`, when `consumed` is 2) become, or `undefined`.
 */
const mergeDeclaration = (first: Statement, second: Statement | undefined): { replacement: Statement[]; consumed: 1 | 2 } | undefined => {
    if (first.type !== "VariableDeclaration" || first.kind !== "var") return undefined;
    const kept = first.declarations.filter((declarator, i) => {
        const next = first.declarations[i + 1];
        return next === undefined || !overwritten(declarator, next.id.type === "Identifier" ? next.id.name : undefined, next.init);
    });
    if (kept.length < first.declarations.length) return { replacement: [declarationOf(first, kept)], consumed: 1 };
    const last = first.declarations.at(-1);
    if (second?.type === "VariableDeclaration" && second.kind === "var") {
        const [next] = second.declarations;
        if (next === undefined || !overwritten(last, next.id.type === "Identifier" ? next.id.name : undefined, next.init)) return undefined;
        const rest = first.declarations.slice(0, -1);
        return { replacement: rest.length === 0 ? [] : [declarationOf(first, rest)], consumed: 1 };
    }
    if (second?.type !== "ExpressionStatement" || second.expression.type !== "AssignmentExpression" || last === undefined) return undefined;
    const assignment = second.expression;
    if (assignment.operator !== "=" || assignment.left.type !== "Identifier" || !overwritten(last, assignment.left.name, assignment.right)) return undefined;
    const merged = at<VariableDeclarator>({ ...last, init: assignment.right }, last);
    return { replacement: [declarationOf(first, [...first.declarations.slice(0, -1), merged])], consumed: 2 };
};

/**
 * Normalize syntax so later passes only have to recognise one shape. Every rewrite is exactly equivalent:
 *
 * - `a, b, c;` -> `a; b; c;` (statement position; as the lone body of an if/loop/label it becomes `{ a; b; c; }`)
 * - `return a, b;` -> `a; return b;` and `throw a, b;` -> `a; throw b;`
 * - `if ((a, b)) ...` -> `a; if (b) ...`
 * - `x["name"]` -> `x.name` when the key is a valid identifier name
 * - `!0` -> `true`, `!1` -> `false`
 *
 * Runs first: minified outputs keep the runtime prelude in comma sequences, which hides its
 * statements from the unflattener and the emulator.
 */
export const normalize: Pass = {
    name: "normalize",
    description: "Split comma sequences into statements, use dot access, fold !0/!1",
    run({ program, log, facts }: PassContext): PassResult {
        let sequences = 0;
        let members = 0;
        let booleans = 0;
        let declarations = 0;

        /** Split the statements of a list in place, then merge declarations whose initial value is overwritten at once. */
        const splitList = (list: Statement[]): void => {
            for (let i = 0; i < list.length; i++) {
                const original = list[i] as Statement;
                const statements = splitFully(original);
                if (statements === undefined) continue;
                if (log.debugging) log.debug(`split into ${statements.length} statements`, original);
                facts.replaced([original], statements);
                list.splice(i, 1, ...statements);
                i += statements.length - 1;
                sequences++;
            }
            for (let i = 0; i < list.length; i++) {
                const merged = mergeDeclaration(list[i] as Statement, list[i + 1]);
                if (merged === undefined) continue;
                const originals = list.slice(i, i + merged.consumed);
                if (log.debugging) log.debug("merged a declaration whose value is overwritten at once", list[i] as Statement);
                facts.replaced(originals, merged.replacement);
                list.splice(i, merged.consumed, ...merged.replacement);
                i = Math.max(-1, i - 2);
                declarations++;
            }
        };

        // Statements are split where they are listed (or held alone) before the walk goes into them, so whatever the
        // splits produce is walked too: one walk does it all.
        traverse(program, {
            enter(path) {
                const node = path.node;
                if (node.type === "Program" || node.type === "BlockStatement" || node.type === "StaticBlock") splitList(node.body as Statement[]);
                else if (node.type === "SwitchCase") splitList(node.consequent);
                const slots = SINGLE_STATEMENT_SLOTS[node.type];
                if (slots === undefined) return;
                const fields = node as unknown as Record<string, Statement | null | undefined>;
                for (const slot of slots) {
                    const statement = fields[slot];
                    const statements = statement === null || statement === undefined ? undefined : splitFully(statement);
                    if (statement === null || statement === undefined || statements === undefined) continue;
                    if (log.debugging) log.debug(`split into a block of ${statements.length} statements`, statement);
                    const block = at<Statement>({ type: "BlockStatement", body: statements }, statement);
                    facts.replaced([statement], [block]);
                    fields[slot] = block;
                    sequences++;
                }
            },
            MemberExpression(path) {
                const node = path.node as MemberExpression;
                if (!node.computed || !("property" in node)) return;
                const property = node.property;
                if (property.type !== "Literal" || typeof property.value !== "string" || !isIdentifierName(property.value)) return;
                if (log.debugging) log.debug("member access to dot form", node);
                path.replace({ ...node, computed: false, property: at({ type: "Identifier", name: property.value }, property) } as MemberExpression);
                members++;
            },
            UnaryExpression(path) {
                const node = path.node;
                if (node.operator !== "!" || node.argument.type !== "Literal" || (node.argument.value !== 0 && node.argument.value !== 1)) return;
                if (log.debugging) log.debug(`!${String(node.argument.value)} to ${String(node.argument.value === 0)}`, node);
                path.replace(at<Expression>({ type: "Literal", value: node.argument.value === 0, raw: null }, node));
                booleans++;
            },
        });

        log.info(`split ${sequences} sequence statement(s), ${members} member access(es) to dot form, ${booleans} !0/!1, merged ${declarations} declaration(s)`);
        // Splits keep every expression (and so every reference); merges drop a declaration of a name declared again.
        return { changed: sequences + members + booleans + declarations, bindingsChanged: declarations > 0, stats: { sequences, members, booleans, declarations } };
    },
};
