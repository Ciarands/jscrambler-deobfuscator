import type { Expression, Function as FunctionNode, Node, Program, Statement, TemplateElement } from "./ast.js";

/*
 * ESTree printer. Output reads like hand-written code: numbers as written by people (`0.5`, `1000000`), strings in
 * the quote that needs fewer escapes with invisible characters escaped, short lists (arguments, arrays, objects,
 * parameters) on one line and long ones one item per line. It prints exactly the AST it is given: re-parsing the output
 * gives the same tree (parentheses are added only where the grammar needs them). Comments are not printed.
 */

/** Lines longer than this break their lists, one item per line. */
const WIDTH = 100;
/** A list this short stays on its line however long the line is: breaking it wouldn't shorten the line much. */
const SHORT_LIST = 40;
const INDENT = "  ";

// Precedence, loosest first. An expression of precedence p printed where at least `min` is needed gets parentheses.
const SEQUENCE = 1;
const ASSIGN = 2; // assignment, arrow function, yield
const CONDITIONAL = 3;
const NULLISH = 4;
const UNARY = 16; // prefix unary operators, await, prefix ++/--
const POSTFIX = 17; // postfix ++/--
const CALL = 18; // calls, `new` with arguments, tagged templates, chains
const MEMBER = 19;
const PRIMARY = 20;

const BINARY: Readonly<Record<string, number>> = {
    "??": NULLISH,
    "||": 5,
    "&&": 6,
    "|": 7,
    "^": 8,
    "&": 9,
    "==": 10,
    "!=": 10,
    "===": 10,
    "!==": 10,
    "<": 11,
    ">": 11,
    "<=": 11,
    ">=": 11,
    instanceof: 11,
    in: 11,
    "<<": 12,
    ">>": 12,
    ">>>": 12,
    "+": 13,
    "-": 13,
    "*": 14,
    "/": 14,
    "%": 14,
    "**": 15,
};

// Context flags. The START_* ones hold only for the expression that begins the printed context (its leftmost leaf).
const START_STATEMENT = 1; // no `{`, `function`, `async function`, `class`, `let [` first
const START_ARROW_BODY = 2; // no `{` first
const START_EXPORT_DEFAULT = 4; // no `function`, `async function`, `class` first
const START_FOR_HEAD = 8; // no `let` first (for-init, for-in/of left)
const START_FOR_OF = 16; // no `async` first (`for (async of x)` reads as an arrow)
const NO_IN = 32; // inside a for-init: a bare `in` would end it
const NO_CALL = 64; // inside a `new` callee: a call would take the `new`'s arguments
const CHAIN_HOST = 128; // object, callee or tag: an optional chain here would extend into the parent
const MEMBER_OBJECT = 256; // object of `.name`: `1.name` would read as a decimal point
const START = START_STATEMENT | START_ARROW_BODY | START_EXPORT_DEFAULT | START_FOR_HEAD | START_FOR_OF;

/** Thrown when a one-line attempt doesn't fit; caught by the list that started it. */
const ABORT: unique symbol = Symbol("abort");

interface Mark {
    readonly parts: number;
    readonly buffer: number;
    readonly length: number;
    readonly line: number;
    readonly lineStart: number;
    readonly indent: number;
    readonly flat: boolean;
    readonly abortAt: number;
}

/** What a list holds, which decides how its items print. */
type ListKind = "arguments" | "array" | "object" | "objectPattern" | "arrayPattern" | "parameters" | "specifiers" | "attributes";

const SIMPLE_STRING = /^[\x20-\x7e]*$/;
const INVISIBLE = /[\p{Cc}\p{Cf}\p{Co}\p{Cn}\p{Zl}\p{Zp}\p{Zs}]/u;

const hex = (code: number, digits: number): string => code.toString(16).toUpperCase().padStart(digits, "0");

/** Escape for one character code (or code point) that can't appear as itself; `undefined` when it can. */
const escapeCode = (code: number, next: number): string | undefined => {
    switch (code) {
        case 0x5c:
            return "\\\\";
        case 0x0a:
            return "\\n";
        case 0x0d:
            return "\\r";
        case 0x09:
            return "\\t";
        case 0x08:
            return "\\b";
        case 0x0c:
            return "\\f";
        case 0x0b:
            return "\\v";
        case 0x00:
            return next >= 0x30 && next <= 0x39 ? "\\x00" : "\\0";
        default:
            break;
    }
    if (code < 0x20 || (code >= 0x7f && code <= 0xa0)) return `\\x${hex(code, 2)}`;
    if (code < 0x7f) return undefined;
    if (code >= 0xd800 && code <= 0xdfff) return `\\u${hex(code, 4)}`; // lone surrogate (pairs come as code points)
    if (!INVISIBLE.test(String.fromCodePoint(code))) return undefined;
    return code > 0xffff ? `\\u{${hex(code, 0)}}` : `\\u${hex(code, 4)}`;
};

/**
 * A string's characters with `extra` (the quote, or what a template must escape) escaped. `special` (global) matches
 * every character `extra` or `escapeCode` may escape: printable ASCII other than those can't need it, so runs of it
 * are copied as they are.
 */
const escapeText = (text: string, special: RegExp, escapeExtra: (code: number, index: number) => string | undefined): string => {
    let out = "";
    let from = 0;
    special.lastIndex = 0;
    for (let match = special.exec(text); match !== null; match = special.exec(text)) {
        const i = match.index;
        let code = text.charCodeAt(i);
        let width = 1;
        if (code >= 0xd800 && code <= 0xdbff) {
            const low = text.charCodeAt(i + 1);
            if (low >= 0xdc00 && low <= 0xdfff) {
                code = (code - 0xd800) * 0x400 + (low - 0xdc00) + 0x10000;
                width = 2;
            }
        }
        const escaped = escapeExtra(code, i) ?? escapeCode(code, text.charCodeAt(i + width));
        if (escaped !== undefined) {
            out += text.slice(from, i) + escaped;
            from = i + width;
        }
        special.lastIndex = i + width;
    }
    return out + text.slice(from);
};

/** What may need escaping in a string literal in double or single quotes, and in a template. */
const DOUBLE_SPECIAL = /[^\x20-\x7e]|["\\]/g;
const SINGLE_SPECIAL = /[^\x20-\x7e]|['\\]/g;
const TEMPLATE_SPECIAL = /[^\x20-\x7e]|[`$\\]/g;

/** A string literal, in the quotes that need fewer escapes (double when even). */
export const quoteString = (value: string): string => {
    const doubles = value.split('"').length - 1;
    const quote = doubles > 0 && doubles > value.split("'").length - 1 ? "'" : '"';
    if (SIMPLE_STRING.test(value) && !value.includes(quote) && !value.includes("\\")) return quote + value + quote;
    const quoteCode = quote.charCodeAt(0);
    return quote + escapeText(value, quote === '"' ? DOUBLE_SPECIAL : SINGLE_SPECIAL, (code) => (code === quoteCode ? `\\${quote}` : undefined)) + quote;
};

/** Raw template text whose cooked value is `cooked`: escapes backslashes, backticks, `${`, and invisible characters. */
export const templateRaw = (cooked: string): string =>
    escapeText(cooked, TEMPLATE_SPECIAL, (code, index) => {
        if (code === 0x60) return "\\`";
        if (code === 0x24 && cooked.charCodeAt(index + 1) === 0x7b) return "\\$";
        if (code === 0x0a) return "\n"; // a line break reads better as itself, and cooks back to `\n`
        return undefined;
    });

/** A number as people write it: `0.5`, `1000000`, `1e21`, `5e-324`. Non-negative finite numbers only. */
const formatNumber = (value: number): string => {
    if (value === Infinity) return "1e999";
    const text = String(value);
    const plus = text.indexOf("e+");
    return plus === -1 ? text : text.slice(0, plus + 1) + text.slice(plus + 2);
};

const isNegativeNumber = (node: Node): boolean => node.type === "Literal" && typeof node.value === "number" && (node.value < 0 || Object.is(node.value, -0));

/**
 * Whether `node`, printed where an expression of precedence `min` is needed in the context `flags`, needs parentheses.
 * One switch on the node type for both questions: the type read is the costly part (it's megamorphic).
 */
const needsParentheses = (node: Node, min: number, flags: number): boolean => {
    switch (node.type) {
        case "Identifier":
            if (flags === 0) return false;
            return (node.name === "let" && (flags & (START_STATEMENT | START_FOR_HEAD)) !== 0) || (node.name === "async" && (flags & START_FOR_OF) !== 0);
        case "MemberExpression":
            return MEMBER < min;
        case "CallExpression":
            return CALL < min || (flags & NO_CALL) !== 0;
        case "Literal":
            if (typeof node.value !== "number") return false;
            if (node.value < 0 || Object.is(node.value, -0)) return UNARY < min;
            // `(1).x`: a digit-only number before `.name` would take the dot as its decimal point.
            return (flags & MEMBER_OBJECT) !== 0 && /^\d+$/.test(formatNumber(node.value));
        case "SequenceExpression":
            return SEQUENCE < min;
        case "AssignmentExpression":
            return ASSIGN < min || (node.left.type === "ObjectPattern" && (flags & (START_STATEMENT | START_ARROW_BODY)) !== 0);
        case "ArrowFunctionExpression":
        case "YieldExpression":
            return ASSIGN < min;
        case "ConditionalExpression":
            return CONDITIONAL < min;
        case "LogicalExpression":
            return (BINARY[node.operator] ?? 0) < min;
        case "BinaryExpression":
            return (BINARY[node.operator] ?? 0) < min || (node.operator === "in" && (flags & NO_IN) !== 0);
        case "UnaryExpression":
        case "AwaitExpression":
            return UNARY < min;
        case "UpdateExpression":
            return (node.prefix ? UNARY : POSTFIX) < min;
        case "NewExpression":
        case "TaggedTemplateExpression":
        case "ImportExpression":
            return CALL < min;
        case "ChainExpression":
            return CALL < min || (flags & (CHAIN_HOST | NO_CALL)) !== 0;
        case "ObjectExpression":
            return (flags & (START_STATEMENT | START_ARROW_BODY)) !== 0;
        case "FunctionExpression":
        case "ClassExpression":
            return (flags & (START_STATEMENT | START_EXPORT_DEFAULT)) !== 0;
        default:
            return false;
    }
};

/** First character of what `node` prints as, for operators that would merge with it (`- -a`, `+ ++a`). */
const startsWithSign = (node: Node): string | undefined => {
    if (node.type === "UnaryExpression" && (node.operator === "-" || node.operator === "+")) return node.operator;
    if (node.type === "UpdateExpression" && node.prefix) return node.operator[0];
    if (isNegativeNumber(node)) return "-";
    return undefined;
};

/** Whether `statement` ends with an `if` that has no `else` (an `else` printed after it would attach to that `if`). */
const endsWithOpenIf = (statement: Statement): boolean => {
    switch (statement.type) {
        case "IfStatement":
            return statement.alternate === null || endsWithOpenIf(statement.alternate);
        case "ForStatement":
        case "ForInStatement":
        case "ForOfStatement":
        case "WhileStatement":
        case "WithStatement":
        case "LabeledStatement":
            return endsWithOpenIf(statement.body);
        default:
            return false;
    }
};

class Printer {
    readonly #layout: boolean;
    /** Output so far is `#parts.join("") + #buffer`; the buffer is flushed into `#parts` in chunks (joining many tiny strings is slow). */
    #parts: string[] = [];
    #buffer = "";
    #length = 0;
    #line = 0;
    #lineStart = 0;
    #indent = 0;
    /** Inside a one-line attempt: a line break aborts it. */
    #flat = false;
    /** Output length past which the current one-line attempt aborts (only while on the line it started on). */
    #abortAt = Infinity;
    readonly #indents: string[] = ["\n"];

    constructor(layout: boolean) {
        this.#layout = layout;
    }

    get output(): string {
        return this.#parts.join("") + this.#buffer;
    }

    write(text: string): void {
        this.#buffer += text;
        this.#length += text.length;
        if (this.#length > this.#abortAt) throw ABORT;
    }

    /** Text that may contain line breaks (template quasis). */
    writeMultiline(text: string): void {
        const last = text.lastIndexOf("\n");
        if (last === -1) return this.write(text);
        if (this.#flat) throw ABORT;
        this.#buffer += text;
        for (let i = text.indexOf("\n"); i !== -1; i = text.indexOf("\n", i + 1)) this.#line++;
        this.#lineStart = this.#length + last + 1;
        this.#length += text.length;
        this.#abortAt = Infinity;
    }

    newline(): void {
        if (this.#flat) throw ABORT;
        if (this.#buffer.length > 8192) {
            this.#parts.push(this.#buffer);
            this.#buffer = "";
        }
        const text = (this.#indents[this.#indent] ??= `\n${INDENT.repeat(this.#indent)}`);
        this.#buffer += text;
        this.#length += text.length;
        this.#line++;
        this.#lineStart = this.#length - text.length + 1;
        this.#abortAt = Infinity;
    }

    /**
     * Where an attempt starts. A long buffer is flushed first, so undoing the attempt only slices a short one: a flush
     * during the attempt pushed the buffer as it was at the mark (plus more) as the chunk at `mark.parts`.
     */
    #mark(): Mark {
        if (this.#buffer.length > 256) {
            this.#parts.push(this.#buffer);
            this.#buffer = "";
        }
        return {
            parts: this.#parts.length,
            buffer: this.#buffer.length,
            length: this.#length,
            line: this.#line,
            lineStart: this.#lineStart,
            indent: this.#indent,
            flat: this.#flat,
            abortAt: this.#abortAt,
        };
    }

    /** Undo the output since `mark` (an aborted attempt). */
    #reset(mark: Mark): void {
        const buffer = this.#parts.length > mark.parts ? (this.#parts[mark.parts] as string) : this.#buffer;
        this.#buffer = buffer.slice(0, mark.buffer);
        this.#parts.length = mark.parts;
        this.#length = mark.length;
        this.#line = mark.line;
        this.#lineStart = mark.lineStart;
        this.#indent = mark.indent;
        this.#flat = mark.flat;
        this.#abortAt = mark.abortAt;
    }

    // ---- lists

    /**
     * `open item, item close` on one line when it fits, else (arguments only) items hugging the brackets when the
     * first line fits (`f(function () {` ... `})`), else one item per line. A lone argument always hugs: on a line of
     * its own it would be as long.
     */
    list(open: string, close: string, items: readonly (Node | null)[], kind: ListKind): void {
        if (items.length === 0) {
            this.write(open + close);
            return;
        }
        if (!this.#layout || this.#flat || (kind === "arguments" && items.length === 1)) return this.#inline(open, close, items, kind);
        if (this.#attempt(true, open, close, items, kind)) return;
        if (kind === "arguments" && this.#attempt(false, open, close, items, kind)) return;
        // A trailing hole needs its own comma: `[a, ,]` has two elements.
        const trailingComma = items.at(-1) === null;
        this.write(open);
        this.#indent++;
        for (let i = 0; i < items.length; i++) {
            this.newline();
            const item = items[i];
            if (item !== null && item !== undefined) this.#item(item, kind);
            if (i < items.length - 1 || trailingComma) this.write(",");
        }
        this.#indent--;
        this.newline();
        this.write(close);
    }

    /**
     * Print the list on one line (`flat`) or hugging its brackets; if what it writes passes the line width before its
     * first line break (or breaks at all when `flat`), undo it and return false.
     */
    #attempt(flat: boolean, open: string, close: string, items: readonly (Node | null)[], kind: ListKind): boolean {
        const mark = this.#mark();
        this.#flat = flat;
        this.#abortAt = Math.min(this.#abortAt, Math.max(this.#lineStart + WIDTH, this.#length + SHORT_LIST));
        try {
            this.#inline(open, close, items, kind);
        } catch (error) {
            if (error !== ABORT) throw error;
            this.#reset(mark);
            return false;
        }
        // The outer limit holds again if still on the line it was set for.
        this.#flat = mark.flat;
        this.#abortAt = this.#line === mark.line ? mark.abortAt : Infinity;
        return true;
    }

    #inline(open: string, close: string, items: readonly (Node | null)[], kind: ListKind): void {
        const spaced = kind === "object" || kind === "objectPattern" || kind === "specifiers" || kind === "attributes";
        this.write(spaced ? `${open} ` : open);
        for (let i = 0; i < items.length; i++) {
            if (i > 0) this.write(", ");
            const item = items[i];
            if (item !== null && item !== undefined) this.#item(item, kind);
        }
        if (items.at(-1) === null) this.write(",");
        this.write(spaced ? ` ${close}` : close);
    }

    #item(item: Node, kind: ListKind): void {
        switch (kind) {
            case "arguments":
            case "array":
                return this.expression(item, ASSIGN, 0);
            case "object":
                return this.property(item, false);
            case "objectPattern":
                return this.property(item, true);
            case "arrayPattern":
            case "parameters":
                return this.pattern(item, 0);
            case "specifiers":
                return this.specifier(item);
            case "attributes":
                if (item.type !== "ImportAttribute") throw new Error(`print: unsupported import attribute ${item.type}`);
                this.moduleName(item.key);
                this.write(": ");
                return this.expression(item.value, PRIMARY, 0);
        }
    }

    // ---- statements

    program(program: Program): void {
        if (program.hashbang !== null) this.write(`#!${program.hashbang.value}`);
        const body = program.body as Statement[];
        if (body.length === 0) return;
        this.statements(body, true);
        this.write("\n");
    }

    /**
     * Statements, each on its own line (the program's first on the current one). Where directives may be (`prologue`:
     * the start of a program or function body), a string statement that isn't a directive gets parentheses, so that it
     * doesn't become one.
     */
    statements(body: readonly Statement[], prologue: boolean): void {
        let inPrologue = prologue;
        for (let i = 0; i < body.length; i++) {
            const statement = body[i] as Statement;
            if (i > 0 || this.#length > 0) this.newline();
            if (statement.type !== "ExpressionStatement") {
                inPrologue = false;
                this.statement(statement);
                continue;
            }
            const expression = statement.expression;
            if (typeof statement.directive === "string" && expression.type === "Literal") {
                const directive = statement.directive;
                this.write(`${expression.raw ?? (directive.includes('"') ? `'${directive}'` : `"${directive}"`)};`);
                continue;
            }
            if (inPrologue && expression.type === "Literal" && typeof expression.value === "string") {
                this.write("(");
                this.literal(expression);
                this.write(");");
            } else this.statement(statement);
            inPrologue = false;
        }
    }

    /** `{ ... }`; `prologue` for function bodies (see `statements`). */
    block(body: readonly Statement[], prologue = false): void {
        if (body.length === 0) {
            this.write("{}");
            return;
        }
        this.write("{");
        this.#indent++;
        this.statements(body, prologue);
        this.#indent--;
        this.newline();
        this.write("}");
    }

    /** The statement of an `if`/loop/label: a block on the same line, or a lone statement after a space. */
    body(statement: Statement): void {
        this.write(" ");
        if (statement.type === "BlockStatement") this.block(statement.body);
        else this.statement(statement);
    }

    statement(node: Statement): void {
        switch (node.type) {
            case "BlockStatement":
                return this.block(node.body);
            case "EmptyStatement":
                return this.write(";");
            case "ExpressionStatement":
                this.expression(node.expression, SEQUENCE, START_STATEMENT);
                return this.write(";");
            case "VariableDeclaration":
                this.variableDeclaration(node, 0);
                return this.write(";");
            case "FunctionDeclaration":
                return this.function(node);
            case "ClassDeclaration":
                return this.class(node);
            case "IfStatement": {
                this.write("if (");
                this.expression(node.test, SEQUENCE, 0);
                this.write(")");
                const alternate = node.alternate;
                if (alternate !== null && node.consequent.type !== "BlockStatement" && endsWithOpenIf(node.consequent)) {
                    this.write(" ");
                    this.block([node.consequent]);
                } else {
                    this.body(node.consequent);
                }
                if (alternate === null) return;
                if (node.consequent.type === "BlockStatement") this.write(" ");
                else this.newline();
                this.write("else");
                if (alternate.type === "IfStatement") {
                    this.write(" ");
                    return this.statement(alternate);
                }
                return this.body(alternate);
            }
            case "ForStatement":
                this.write("for (");
                if (node.init !== null) {
                    if (node.init.type === "VariableDeclaration") this.variableDeclaration(node.init, NO_IN);
                    else this.expression(node.init, SEQUENCE, NO_IN | START_FOR_HEAD);
                }
                this.write(";");
                if (node.test !== null) {
                    this.write(" ");
                    this.expression(node.test, SEQUENCE, 0);
                }
                this.write(";");
                if (node.update !== null) {
                    this.write(" ");
                    this.expression(node.update, SEQUENCE, 0);
                }
                this.write(")");
                return this.body(node.body);
            case "ForInStatement":
            case "ForOfStatement": {
                const of = node.type === "ForOfStatement";
                this.write(of && node.await ? "for await (" : "for (");
                if (node.left.type === "VariableDeclaration") this.variableDeclaration(node.left, NO_IN);
                else this.pattern(node.left, START_FOR_HEAD | (of ? START_FOR_OF : 0));
                this.write(of ? " of " : " in ");
                this.expression(node.right, of ? ASSIGN : SEQUENCE, 0);
                this.write(")");
                return this.body(node.body);
            }
            case "WhileStatement":
                this.write("while (");
                this.expression(node.test, SEQUENCE, 0);
                this.write(")");
                return this.body(node.body);
            case "DoWhileStatement":
                this.write("do");
                this.body(node.body);
                this.write(" while (");
                this.expression(node.test, SEQUENCE, 0);
                return this.write(");");
            case "ReturnStatement":
            case "ThrowStatement":
                this.write(node.type === "ReturnStatement" ? "return" : "throw");
                if (node.argument !== null) {
                    this.write(" ");
                    this.expression(node.argument, SEQUENCE, 0);
                }
                return this.write(";");
            case "BreakStatement":
            case "ContinueStatement":
                this.write(node.type === "BreakStatement" ? "break" : "continue");
                if (node.label !== null) this.write(` ${node.label.name}`);
                return this.write(";");
            case "LabeledStatement":
                // A label `let` (written escaped in the source) would read as the start of a `let` declaration.
                this.write(`${node.label.name === "let" ? "l\\u0065t" : node.label.name}:`);
                return this.body(node.body);
            case "SwitchStatement":
                this.write("switch (");
                this.expression(node.discriminant, SEQUENCE, 0);
                this.write(") {");
                this.#indent++;
                for (const switchCase of node.cases) {
                    this.newline();
                    if (switchCase.test === null) this.write("default:");
                    else {
                        this.write("case ");
                        this.expression(switchCase.test, SEQUENCE, 0);
                        this.write(":");
                    }
                    const only = switchCase.consequent.length === 1 ? switchCase.consequent[0] : undefined;
                    if (only?.type === "BlockStatement") {
                        this.write(" ");
                        this.block(only.body);
                        continue;
                    }
                    this.#indent++;
                    for (let i = 0; i < switchCase.consequent.length; i++) {
                        this.newline();
                        this.statement(switchCase.consequent[i] as Statement);
                    }
                    this.#indent--;
                }
                this.#indent--;
                this.newline();
                return this.write("}");
            case "TryStatement":
                this.write("try ");
                this.block(node.block.body);
                if (node.handler !== null) {
                    this.write(" catch ");
                    if (node.handler.param !== null) {
                        this.write("(");
                        this.pattern(node.handler.param, 0);
                        this.write(") ");
                    }
                    this.block(node.handler.body.body);
                }
                if (node.finalizer !== null) {
                    this.write(" finally ");
                    this.block(node.finalizer.body);
                }
                return;
            case "WithStatement":
                this.write("with (");
                this.expression(node.object, SEQUENCE, 0);
                this.write(")");
                return this.body(node.body);
            case "DebuggerStatement":
                return this.write("debugger;");
            case "ImportDeclaration":
                return this.importDeclaration(node);
            case "ExportNamedDeclaration":
                this.write("export ");
                if (node.declaration !== null) return this.statement(node.declaration as Statement);
                this.list("{", "}", node.specifiers, "specifiers");
                if (node.source !== null) {
                    this.write(" from ");
                    this.expression(node.source, PRIMARY, 0);
                    this.attributes(node.attributes);
                }
                return this.write(";");
            case "ExportDefaultDeclaration": {
                this.write("export default ");
                const declaration = node.declaration;
                if (declaration.type === "FunctionDeclaration") return this.function(declaration);
                if (declaration.type === "ClassDeclaration") return this.class(declaration);
                this.expression(declaration as Expression, ASSIGN, START_EXPORT_DEFAULT);
                return this.write(";");
            }
            case "ExportAllDeclaration":
                this.write("export *");
                if (node.exported !== null) {
                    this.write(" as ");
                    this.moduleName(node.exported);
                }
                this.write(" from ");
                this.expression(node.source, PRIMARY, 0);
                this.attributes(node.attributes);
                return this.write(";");
            default:
                throw new Error(`print: unsupported statement ${node.type}`);
        }
    }

    variableDeclaration(node: Extract<Statement, { type: "VariableDeclaration" }>, flags: number): void {
        this.write(`${node.kind} `);
        for (let i = 0; i < node.declarations.length; i++) {
            if (i > 0) this.write(", ");
            const declarator = node.declarations[i];
            if (declarator === undefined) continue;
            this.pattern(declarator.id, 0);
            if (declarator.init !== null) {
                this.write(" = ");
                this.expression(declarator.init, ASSIGN, flags & NO_IN);
            }
        }
    }

    importDeclaration(node: Extract<Statement, { type: "ImportDeclaration" }>): void {
        this.write(node.phase === null ? "import " : `import ${node.phase} `);
        const specifiers = node.specifiers;
        let named = 0;
        for (const specifier of specifiers) {
            if (specifier.type === "ImportDefaultSpecifier") this.write(specifier.local.name);
            else if (specifier.type === "ImportNamespaceSpecifier") this.write(`${named > 0 ? ", " : ""}* as ${specifier.local.name}`);
            else continue;
            named++;
        }
        const braces = specifiers.filter((specifier) => specifier.type === "ImportSpecifier");
        if (braces.length > 0) {
            if (named > 0) this.write(", ");
            this.list("{", "}", braces, "specifiers");
        }
        if (specifiers.length > 0) this.write(" from ");
        this.expression(node.source, PRIMARY, 0);
        this.attributes(node.attributes);
        this.write(";");
    }

    moduleName(node: Node): void {
        if (node.type === "Identifier") this.write(node.name);
        else this.expression(node, PRIMARY, 0);
    }

    /** `a`, `a as b`, `"a b" as c` in an import or export list. */
    specifier(node: Node): void {
        let from: Node;
        let to: Node;
        if (node.type === "ImportSpecifier") [from, to] = [node.imported, node.local];
        else if (node.type === "ExportSpecifier") [from, to] = [node.local, node.exported];
        else throw new Error(`print: unsupported specifier ${node.type}`);
        this.moduleName(from);
        if (from.type === "Identifier" && to.type === "Identifier" && from.name === to.name) return;
        this.write(" as ");
        this.moduleName(to);
    }

    attributes(attributes: readonly Node[]): void {
        if (attributes.length === 0) return;
        this.write(" with ");
        this.list("{", "}", attributes, "attributes");
    }

    // ---- functions and classes

    function(node: FunctionNode): void {
        if (node.async) this.write("async ");
        this.write(node.generator ? "function*" : "function");
        this.write(node.id === null ? " " : ` ${node.id.name}`);
        this.parameters(node.params);
        this.write(" ");
        this.block((node.body?.body ?? []) as Statement[], true);
    }

    parameters(params: readonly Node[]): void {
        this.list("(", ")", params, "parameters");
    }

    arrow(node: Extract<Node, { type: "ArrowFunctionExpression" }>, flags: number): void {
        if (node.async) this.write("async ");
        const only = node.params.length === 1 ? node.params[0] : undefined;
        if (only?.type === "Identifier") this.write(only.name);
        else this.parameters(node.params);
        this.write(" => ");
        if (node.body.type === "BlockStatement") this.block(node.body.body as Statement[], true);
        else this.expression(node.body, ASSIGN, START_ARROW_BODY | (flags & NO_IN));
    }

    class(node: Extract<Node, { type: "ClassDeclaration" | "ClassExpression" }>): void {
        this.decorators(node.decorators);
        this.write("class");
        if (node.id !== null) this.write(` ${node.id.name}`);
        if (node.superClass !== null) {
            this.write(" extends ");
            this.expression(node.superClass, CALL, 0);
        }
        this.write(" ");
        const members = node.body.body;
        if (members.length === 0) {
            this.write("{}");
            return;
        }
        this.write("{");
        this.#indent++;
        for (const member of members) {
            this.newline();
            this.classMember(member);
        }
        this.#indent--;
        this.newline();
        this.write("}");
    }

    decorators(decorators: readonly Extract<Node, { type: "Decorator" }>[] | undefined): void {
        for (const decorator of decorators ?? []) {
            this.write("@");
            let callee: Node = decorator.expression;
            if (callee.type === "CallExpression") callee = callee.callee;
            while (callee.type === "MemberExpression" && !callee.computed) callee = callee.object;
            if (callee.type === "Identifier") this.expression(decorator.expression, CALL, 0);
            else {
                this.write("(");
                this.expression(decorator.expression, SEQUENCE, 0);
                this.write(")");
            }
            this.write(" ");
        }
    }

    classMember(member: Node): void {
        switch (member.type) {
            case "StaticBlock":
                this.write("static ");
                return this.block(member.body);
            case "MethodDefinition": {
                this.decorators(member.decorators);
                if (member.static) this.write("static ");
                return this.method(member.kind === "get" || member.kind === "set" ? member.kind : "method", member.key, member.computed, member.value);
            }
            case "PropertyDefinition":
            case "AccessorProperty":
                this.decorators(member.decorators);
                if (member.static) this.write("static ");
                if (member.type === "AccessorProperty") this.write("accessor ");
                this.key(member.key, member.computed);
                if (member.value !== null) {
                    this.write(" = ");
                    this.expression(member.value, ASSIGN, 0);
                }
                return this.write(";");
            default:
                throw new Error(`print: unsupported class member ${member.type}`);
        }
    }

    /** `get key() {}`, `async *key() {}`, ... */
    method(kind: "get" | "set" | "method", key: Node, computed: boolean, fn: Node): void {
        if (fn.type !== "FunctionExpression") throw new Error(`print: method value ${fn.type}`);
        if (kind !== "method") this.write(`${kind} `);
        if (fn.async) this.write("async ");
        if (fn.generator) this.write("*");
        this.key(key, computed);
        this.parameters(fn.params);
        this.write(" ");
        this.block((fn.body?.body ?? []) as Statement[], true);
    }

    key(key: Node, computed: boolean): void {
        if (computed) {
            this.write("[");
            this.expression(key, ASSIGN, 0);
            this.write("]");
        } else if (key.type === "Identifier") this.write(key.name);
        else if (key.type === "PrivateIdentifier") this.write(`#${key.name}`);
        else this.expression(key, PRIMARY, 0);
    }

    // ---- patterns

    pattern(node: Node, flags: number): void {
        switch (node.type) {
            case "ObjectPattern":
                return this.list("{", "}", node.properties as readonly Node[], "objectPattern");
            case "ArrayPattern":
                return this.list("[", "]", node.elements as readonly (Node | null)[], "arrayPattern");
            case "AssignmentPattern":
                this.pattern(node.left, flags);
                this.write(" = ");
                return this.expression(node.right, ASSIGN, flags & NO_IN);
            case "RestElement":
                this.write("...");
                return this.pattern(node.argument, 0);
            default:
                return this.expression(node, CALL, flags);
        }
    }

    property(node: Node, inPattern: boolean): void {
        if (node.type === "SpreadElement" || node.type === "RestElement") {
            this.write("...");
            if (node.type === "RestElement") return this.pattern(node.argument, 0);
            return this.expression(node.argument, ASSIGN, 0);
        }
        if (node.type !== "Property") throw new Error(`print: unsupported property ${node.type}`);
        const value = node.value as Node;
        if (node.kind === "get" || node.kind === "set") return this.method(node.kind, node.key, node.computed, value);
        if (node.method) return this.method("method", node.key, node.computed, value);
        if (node.shorthand && !node.computed && node.key.type === "Identifier") {
            const name = node.key.name;
            if (value.type === "Identifier" && value.name === name) return this.write(name);
            if (value.type === "AssignmentPattern" && value.left.type === "Identifier" && value.left.name === name) return this.pattern(value, 0);
        }
        this.key(node.key, node.computed);
        this.write(": ");
        if (inPattern) this.pattern(value, 0);
        else this.expression(value, ASSIGN, 0);
    }

    // ---- expressions

    /** Print `node` where an expression of precedence `min` is needed, in the context `flags`. */
    expression(node: Node, min: number, flags: number): void {
        if (needsParentheses(node, min, flags)) {
            this.write("(");
            this.expressionInner(node, 0);
            this.write(")");
            return;
        }
        this.expressionInner(node, flags);
    }

    expressionInner(node: Node, flags: number): void {
        const start = flags & START;
        const noIn = flags & NO_IN;
        switch (node.type) {
            case "Identifier":
                return this.write(node.name);
            case "PrivateIdentifier":
                return this.write(`#${node.name}`);
            case "ThisExpression":
                return this.write("this");
            case "Super":
                return this.write("super");
            case "Literal":
                return this.literal(node);
            case "TemplateLiteral":
                return this.template(node);
            case "TaggedTemplateExpression":
                this.expression(node.tag, CALL, start | CHAIN_HOST | (flags & NO_CALL));
                return this.template(node.quasi);
            case "ArrayExpression":
                return this.list("[", "]", node.elements as readonly (Node | null)[], "array");
            case "ObjectExpression":
                return this.list("{", "}", node.properties, "object");
            case "FunctionExpression":
                return this.function(node);
            case "ArrowFunctionExpression":
                return this.arrow(node, flags);
            case "ClassExpression":
                return this.class(node);
            case "SequenceExpression":
                for (let i = 0; i < node.expressions.length; i++) {
                    if (i > 0) this.write(", ");
                    this.expression(node.expressions[i] as Node, ASSIGN, (i === 0 ? start : 0) | noIn);
                }
                return;
            case "AssignmentExpression":
                this.pattern(node.left, start);
                this.write(` ${node.operator} `);
                return this.expression(node.right, ASSIGN, noIn);
            case "ConditionalExpression":
                this.expression(node.test, NULLISH + 1, start | noIn);
                this.write(" ? ");
                this.expression(node.consequent, ASSIGN, 0);
                this.write(" : ");
                return this.expression(node.alternate, ASSIGN, noIn);
            case "LogicalExpression":
            case "BinaryExpression": {
                const precedence = BINARY[node.operator] ?? 0;
                const left = node.left as Node;
                const right = node.right as Node;
                const exponent = node.operator === "**";
                // `??` doesn't mix with `||`/`&&` without parentheses.
                const mixes = (child: Node): boolean => child.type === "LogicalExpression" && (node.operator === "??") !== (child.operator === "??");
                if (left.type === "PrivateIdentifier") this.write(`#${left.name}`);
                else if (mixes(left)) {
                    this.write("(");
                    this.expressionInner(left, 0);
                    this.write(")");
                } else this.expression(left, exponent ? POSTFIX : precedence, start | noIn);
                this.write(` ${node.operator} `);
                if (mixes(right)) {
                    this.write("(");
                    this.expressionInner(right, 0);
                    return this.write(")");
                }
                return this.expression(right, exponent ? precedence : precedence + 1, noIn);
            }
            case "UnaryExpression": {
                const operator = node.operator;
                this.write(operator);
                if (operator.length > 1 || startsWithSign(node.argument) === operator) this.write(" ");
                return this.expression(node.argument, UNARY, noIn);
            }
            case "AwaitExpression":
                this.write("await ");
                return this.expression(node.argument, UNARY, noIn);
            case "UpdateExpression":
                if (node.prefix) {
                    this.write(node.operator);
                    if (startsWithSign(node.argument) === node.operator[0]) this.write(" ");
                    return this.expression(node.argument, CALL, 0);
                }
                this.expression(node.argument, CALL, start);
                return this.write(node.operator);
            case "YieldExpression":
                this.write(node.delegate ? "yield*" : "yield");
                if (node.argument === null) return;
                this.write(" ");
                return this.expression(node.argument, ASSIGN, noIn);
            case "SpreadElement":
                this.write("...");
                return this.expression(node.argument, ASSIGN, 0);
            case "MemberExpression":
                this.expression(node.object, CALL, start | CHAIN_HOST | (flags & NO_CALL) | (node.computed ? 0 : MEMBER_OBJECT));
                if (node.computed) {
                    this.write(node.optional ? "?.[" : "[");
                    this.expression(node.property, SEQUENCE, 0);
                    return this.write("]");
                }
                this.write(node.optional ? "?." : ".");
                return this.write(node.property.type === "PrivateIdentifier" ? `#${node.property.name}` : node.property.name);
            case "CallExpression":
                this.expression(node.callee, CALL, start | CHAIN_HOST);
                if (node.optional) this.write("?.");
                return this.arguments(node.arguments);
            case "NewExpression":
                this.write("new ");
                this.expression(node.callee, MEMBER, NO_CALL | CHAIN_HOST);
                return this.arguments(node.arguments);
            case "ChainExpression":
                return this.expressionInner(node.expression, flags & ~(CHAIN_HOST | MEMBER_OBJECT));
            case "ImportExpression":
                this.write(node.phase === null ? "import" : `import.${node.phase}`);
                return this.arguments(node.options === null ? [node.source] : [node.source, node.options]);
            case "MetaProperty":
                return this.write(`${node.meta.name}.${node.property.name}`);
            case "ParenthesizedExpression":
                this.write("(");
                this.expressionInner(node.expression, 0);
                return this.write(")");
            case "ObjectPattern":
            case "ArrayPattern":
            case "AssignmentPattern":
            case "RestElement":
                return this.pattern(node, flags);
            default:
                throw new Error(`print: unsupported expression ${node.type}`);
        }
    }

    arguments(args: readonly Node[]): void {
        this.list("(", ")", args, "arguments");
    }

    literal(node: Extract<Node, { type: "Literal" }>): void {
        if ("regex" in node && node.regex !== undefined) return this.write(`/${node.regex.pattern}/${node.regex.flags}`);
        if ("bigint" in node && typeof node.bigint === "string") return this.write(`${node.bigint}n`);
        const value = node.value;
        if (typeof value === "string") return this.write(quoteString(value));
        if (typeof value === "number") {
            if (Number.isNaN(value)) return this.write("(0 / 0)");
            if (value < 0 || Object.is(value, -0)) return this.write(`-${formatNumber(-value)}`);
            return this.write(formatNumber(value));
        }
        return this.write(String(value));
    }

    template(node: Extract<Node, { type: "TemplateLiteral" }>): void {
        this.write("`");
        for (let i = 0; i < node.quasis.length; i++) {
            const quasi = node.quasis[i] as TemplateElement;
            this.writeMultiline(quasi.value.raw ?? templateRaw(quasi.value.cooked ?? ""));
            const expression = node.expressions[i];
            if (expression === undefined) continue;
            this.write("${");
            this.expression(expression, SEQUENCE, 0);
            this.write("}");
        }
        this.write("`");
    }
}

/** Print an ESTree program, laid out for reading. Comments are not printed. */
export const print = (program: Program): string => {
    const printer = new Printer(true);
    printer.program(program);
    return printer.output;
};

/** Print one statement as a program of its own (to run it in the sandbox): exact, without layout work. */
export const printStatement = (statement: Statement): string => {
    const printer = new Printer(false);
    printer.statements([statement], true);
    return printer.output;
};
