import type { Expression, MemberExpression, Statement, VariableDeclarator } from "../core/ast.js";
import { isIdentifierName } from "../core/ast.js";
import { at } from "../core/build.js";
import { pushAll, spliceList } from "../core/list.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";

const statementOf = (expression: Expression): Statement => at<Statement>({ type: "ExpressionStatement", expression }, expression);

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
 * Normalize syntax so later passes only recognise one shape (comma statements split, `x["name"]` -> `x.name`,
 * `!0` -> `true`). Every rewrite is exact. Runs first: minified outputs hide the prelude in comma sequences.
 */
export const normalize: Pass = {
    name: "normalize",
    description: "Split comma sequences into statements, use dot access, fold !0/!1",
    run({ program, log, facts }: PassContext): PassResult {
        let sequences = 0;
        let members = 0;
        let booleans = 0;

        /** Split the statements of a list in place. */
        const splitList = (list: Statement[]): void => {
            let out: Statement[] | undefined;
            for (let i = 0; i < list.length; i++) {
                const original = list[i] as Statement;
                const statements = splitFully(original);
                if (statements === undefined) {
                    out?.push(original);
                    continue;
                }
                if (log.debugging) log.debug(`split into ${statements.length} statements`, original);
                facts.replaced([original], statements);
                out ??= list.slice(0, i);
                pushAll(out, statements);
                sequences++;
            }
            if (out !== undefined) spliceList(list, 0, list.length, out);
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

        log.info(`split ${sequences} sequence statement(s), ${members} member access(es) to dot form, ${booleans} !0/!1`);
        // Splits keep every expression (and so every reference).
        return { changed: sequences + members + booleans, bindingsChanged: false, stats: { sequences, members, booleans } };
    },
};
