import type {
    AccessorProperty,
    BinaryExpression,
    Expression,
    MethodDefinition,
    Node,
    ObjectExpression,
    PropertyDefinition,
    Statement,
    TemplateElement,
    TemplateLiteral,
    UnaryExpression,
} from "../../core/ast.js";
import { isFunctionNode, isIdentifierName, keyName } from "../../core/ast.js";
import { at, valueToNode } from "../../core/build.js";
import type { ScopeInfo } from "../../core/scope.js";
import { forEachChild } from "../../core/traverse.js";
import { templateRaw } from "../../core/print.js";
import type { Path } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";

/** `!argument`; a boolean literal negates to the other one (the operands an inversion distributes over may be one). */
export const not = (argument: Expression, origin: Node): Expression =>
    argument.type === "Literal" && typeof argument.value === "boolean"
        ? valueToNode(!argument.value, origin)
        : at<UnaryExpression>({ type: "UnaryExpression", operator: "!", prefix: true, argument }, origin);

type Binary = Extract<Node, { type: "BinaryExpression" }>;

/** `!(a == b)` -> `a != b`. Only equality: `!(a < b)` isn't `a >= b` when either is NaN. */
const NEGATED_EQUALITY: Readonly<Record<string, BinaryExpression["operator"]>> = { "==": "!=", "!=": "==", "===": "!==", "!==": "===" };

/** `1 < x` -> `x > 1`: the operator with its operands swapped. Commutative ones stay. */
const SWAPPED: Readonly<Record<string, BinaryExpression["operator"]>> = {
    "==": "==",
    "===": "===",
    "!=": "!=",
    "!==": "!==",
    "<": ">",
    ">": "<",
    "<=": ">=",
    ">=": "<=",
    "*": "*",
    "&": "&",
    "|": "|",
    "^": "^",
};

const SHIFTS: ReadonlySet<string> = new Set(["<<", ">>", ">>>"]);
const BITWISE: ReadonlySet<string> = new Set(["&", "|", "^", "<<", ">>", ">>>"]);

/** Names whose global is a constant value: reading them can't run code or throw. */
const CONSTANT_GLOBALS: ReadonlySet<string> = new Set(["undefined", "NaN", "Infinity"]);

/** Evaluating it can't run code, throw, or depend on when it happens. */
const isConstantValue = (node: Node, context: UnminifyContext): boolean => {
    switch (node.type) {
        case "Literal":
            return !("regex" in node && node.regex !== undefined && node.regex !== null) && typeof node.value !== "bigint";
        case "Identifier":
            return CONSTANT_GLOBALS.has(node.name) && context.isGlobal(node);
        case "UnaryExpression":
            return (
                node.operator === "-" &&
                ((node.argument.type === "Literal" && typeof node.argument.value === "number") ||
                    (node.argument.type === "Identifier" && node.argument.name === "Infinity" && context.isGlobal(node.argument)))
            );
        default:
            return false;
    }
};

/** Whether the expression at `path` is only used for its truthiness (`if (HERE)`, `!HERE`, `HERE ? a : b`, `if (HERE && x)`). */
const isTestedForTruth = (path: Path): boolean => {
    for (let current: Path | null = path; current !== null; current = current.parentPath) {
        const parent = current.parent;
        if (parent === null) return false;
        switch (parent.type) {
            case "IfStatement":
            case "WhileStatement":
            case "DoWhileStatement":
            case "ForStatement":
            case "ConditionalExpression":
                return current.key === "test";
            case "UnaryExpression":
                return parent.operator === "!";
            case "LogicalExpression":
                // Both operands of `&&`/`||` only decide its truthiness when the whole is tested for truth.
                if (parent.operator === "??") return false;
                continue;
            default:
                return false;
        }
    }
    return false;
};

const isU = (side: Node): boolean => side.type === "Literal" && side.value === "u";
const isTypeof = (side: Node): boolean => side.type === "UnaryExpression" && side.operator === "typeof";

/** `typeof x > "u"` -> `typeof x === "undefined"`: only `"undefined"` sorts after `"u"` among typeof results. */
const typeofUndefined = (node: Binary): Expression | undefined => {
    let isUndefined: boolean;
    let operand: Node;
    if (isTypeof(node.left) && isU(node.right) && (node.operator === ">" || node.operator === "<")) {
        isUndefined = node.operator === ">";
        operand = node.left;
    } else if (isU(node.left) && isTypeof(node.right) && (node.operator === "<" || node.operator === ">")) {
        isUndefined = node.operator === "<";
        operand = node.right;
    } else return undefined;
    return at<BinaryExpression>({ type: "BinaryExpression", operator: isUndefined ? "===" : "!==", left: operand, right: valueToNode("undefined", node.right) }, node);
};

const numberOf = (operand: Node): number | undefined => {
    if (operand.type === "Literal" && typeof operand.value === "number") return operand.value;
    if (operand.type === "UnaryExpression" && operand.operator === "-" && operand.argument.type === "Literal" && typeof operand.argument.value === "number") return -operand.argument.value;
    return undefined;
};

/** A number operand of a bitwise operator as the operator sees it (ToInt32, ToUint32 for `>>>`, or a shift count). */
const truncatedOperand = (operator: string, operand: Node, side: "left" | "right"): Expression | undefined => {
    const value = numberOf(operand);
    if (value === undefined) return undefined;
    const truncated = side === "right" && SHIFTS.has(operator) ? value & 31 : operator === ">>>" ? value >>> 0 : value | 0;
    return truncated === value ? undefined : valueToNode(truncated, operand);
};

/** `x & 4294967297` -> `x & 1`: number operands of bitwise operators as the operator truncates them. */
const truncateNumbers = (node: Binary): Expression | undefined => {
    if (!BITWISE.has(node.operator)) return undefined;
    const left = truncatedOperand(node.operator, node.left, "left");
    const right = truncatedOperand(node.operator, node.right, "right");
    if (left === undefined && right === undefined) return undefined;
    return at<BinaryExpression>({ ...node, left: left ?? node.left, right: right ?? node.right }, node);
};

/**
 * Raw template text `a` then `b`, escaping what the seam would misread: a bare `$` ending `a` and a `{` starting `b`
 * would open a substitution; a `\0` ending `a` and a digit starting `b` would read as an octal escape (an error).
 */
const joinRaw = (a: string, b: string): string => {
    let backslashes = 0;
    while (a[a.length - 2 - backslashes] === "\\") backslashes++;
    const escaped = backslashes % 2 === 1;
    if (a.endsWith("$") && !escaped && b.startsWith("{")) return `${a}\\${b}`;
    if (a.endsWith("0") && escaped && /^\d/.test(b)) return `${a.slice(0, -2)}\\x00${b}`;
    return a + b;
};

/** `` `a${"b"}c` `` -> `` `abc` ``. Not in tagged templates: the tag sees the strings and values apart. */
const inlineTemplateStrings = (node: TemplateLiteral): TemplateLiteral | undefined => {
    if (!node.expressions.some((expression) => expression.type === "Literal" && typeof expression.value === "string")) return undefined;
    const quasis: TemplateElement[] = [];
    const expressions: Expression[] = [];
    let raw = node.quasis[0]?.value.raw ?? "";
    let cooked = node.quasis[0]?.value.cooked ?? "";
    for (let i = 0; i < node.expressions.length; i++) {
        const expression = node.expressions[i] as Expression;
        const next = node.quasis[i + 1] as TemplateElement;
        if (expression.type === "Literal" && typeof expression.value === "string") {
            raw = joinRaw(joinRaw(raw, templateRaw(expression.value)), next.value.raw);
            cooked += expression.value + (next.value.cooked ?? "");
            continue;
        }
        quasis.push(at<TemplateElement>({ type: "TemplateElement", value: { raw, cooked }, tail: false }, node));
        expressions.push(expression);
        raw = next.value.raw;
        cooked = next.value.cooked ?? "";
    }
    quasis.push(at<TemplateElement>({ type: "TemplateElement", value: { raw, cooked }, tail: true }, node));
    return at<TemplateLiteral>({ type: "TemplateLiteral", quasis, expressions }, node);
};

/** Characters an escape in a pattern can stand for as themselves: letters, digits, `_` and space mean the same unescaped (see `mergesBefore`). */
const isPlainPatternChar = (code: number): boolean => (code >= 65 && code <= 90) || (code >= 97 && code <= 122) || (code >= 48 && code <= 57) || code === 95 || code === 32;

/**
 * Punctuation that means itself anywhere in a pattern without the `v` flag (where `&&`, `!!`, ... inside classes are
 * reserved). `,` too where it can't complete a quantifier (`{1\x2c2}` is literal text, `{1,2}` a quantifier).
 */
const PLAIN_PUNCTUATION: ReadonlySet<number> = new Set([..."!\"#%&',:;<=>@`~"].map((char) => char.charCodeAt(0)));

/** Syntax characters (and `/`, which ends the literal): an identity escape `\.` means the character, with any flag. */
const SYNTAX_CHARACTERS: ReadonlySet<number> = new Set([..."^$\\.*+?()[]{}|/"].map((char) => char.charCodeAt(0)));

/**
 * Whether `char`, written after `out` unescaped, would join what comes before into something else: a digit after a
 * backreference or octal escape (`\1` + `1` is `\11`), a hex digit after an unfinished `\x`/`\u` (non-unicode `\x4`
 * is the text `x4`, `\x4` + `1` the character `A`), a digit or `,` after an open `{` (`a{1` + `,2}` is a
 * quantifier).
 */
const mergesBefore = (out: string, char: string, inClass: boolean): boolean =>
    (/\d/.test(char) && /(?:^|[^\\])(?:\\\\)*\\\d+$/.test(out)) ||
    (/[\dA-Fa-f]/.test(char) && /(?:^|[^\\])(?:\\\\)*\\(?:x[\dA-Fa-f]?|u\{?[\dA-Fa-f]{0,3})$/.test(out)) ||
    (!inClass && /[\d,]/.test(char) && /(?:^|[^\\])(?:\\\\)*\{[\d,]*$/.test(out));

/** How many capturing groups a pattern has: each `(` not followed by `?`, and each named group `(?<name>`. */
const capturingGroups = (pattern: string): number => {
    let count = 0;
    let inClass = false;
    for (let i = 0; i < pattern.length; i++) {
        const char = pattern[i];
        if (char === "\\") {
            i++;
        } else if (inClass) {
            if (char === "]") inClass = false;
        } else if (char === "[") {
            inClass = true;
        } else if (char === "(" && (pattern[i + 1] !== "?" || (pattern[i + 2] === "<" && pattern[i + 3] !== "=" && pattern[i + 3] !== "!"))) {
            count++;
        }
    }
    return count;
};

/**
 * `/\x70\x72\u006fgress/` -> `/progress/`, `/\163\137\164h\072/` -> `/s_th:/`, `/\u002e(srt|vtt)/` ->
 * `/\.(srt|vtt)/`: escapes of printable characters written as the characters, unless that joins what comes before
 * into something else (`mergesBefore`). Letters, digits, `_` and space as themselves; without the `v` flag, plain
 * punctuation too, syntax characters as identity escapes (`\.`, `\/`), and `-` as itself outside classes and `\-` in
 * them. `\xHH` and `\uHHHH` mean the same in and out of classes with any flag. A three-digit legacy octal escape
 * (`\163`, only without `u`/`v`) is a character in a class and, outside one, when it starts with 0 or its number is
 * past the pattern's capturing groups (else it would be a backreference); one followed by another digit stays
 * (`\1634`: the digits read as one number). Nothing is unescaped after `\c` (`\c\x41` is `\c` and `A` apart, `\cA` a
 * control character).
 */
const readablePattern = (pattern: string, flags: string): string | undefined => {
    const unicode = flags.includes("u") || flags.includes("v");
    const setMode = flags.includes("v");
    const spelling = (code: number, inClass: boolean): string | undefined => {
        const char = String.fromCharCode(code);
        if (isPlainPatternChar(code)) return char;
        if (setMode) return undefined;
        if (PLAIN_PUNCTUATION.has(code)) return char;
        if (SYNTAX_CHARACTERS.has(code)) return `\\${char}`;
        if (char === "-") return inClass ? "\\-" : "-";
        return undefined;
    };
    let groups: number | undefined;
    let out = "";
    let changed = false;
    let afterControl = false;
    let inClass = false;
    for (let i = 0; i < pattern.length;) {
        if (pattern[i] !== "\\") {
            if (pattern[i] === "[" && !inClass) inClass = true;
            else if (pattern[i] === "]" && inClass) inClass = false;
            out += pattern[i];
            afterControl = false;
            i++;
            continue;
        }
        const kind = pattern[i + 1] ?? "";
        const digits = kind === "x" ? 2 : kind === "u" ? 4 : 0;
        const hex = pattern.slice(i + 2, i + 2 + digits);
        let code = digits > 0 && hex.length === digits && /^[\dA-Fa-f]+$/.test(hex) ? Number.parseInt(hex, 16) : undefined;
        let length = 2 + digits;
        const octal = /^[0-3][0-7]{2}(?!\d)/.exec(pattern.slice(i + 1))?.[0];
        if (code === undefined && octal !== undefined && !unicode) {
            groups ??= capturingGroups(pattern);
            if (inClass || octal.startsWith("0") || Number(octal) > groups) {
                code = Number.parseInt(octal, 8);
                length = 4;
            }
        }
        const spelled = code === undefined || afterControl ? undefined : spelling(code, inClass);
        if (spelled !== undefined && !mergesBefore(out, spelled.at(-1) as string, inClass)) {
            out += spelled;
            changed = true;
            afterControl = false;
            i += length;
            continue;
        }
        out += pattern.slice(i, i + 2);
        afterControl = kind === "c";
        i += 2;
    }
    return changed ? out : undefined;
};

const isAlphanumeric = (char: string | undefined): boolean => char !== undefined && /^[\dA-Za-z]$/.test(char);

/**
 * A class's letters, digits and ranges between them as one sorted list of ranges (`L-MKN-ZA-DF-JE-E` -> `A-Z`), or
 * undefined when it holds anything else (escapes, punctuation): which characters it has is all a class means, the
 * `i` flag folding each the same either way. Runs end at letters or digits: they are what the class has.
 */
const canonicalClass = (body: string): string | undefined => {
    const codes = new Set<number>();
    for (let i = 0; i < body.length;) {
        const start = body[i] as string;
        if (!isAlphanumeric(start)) return undefined;
        if (body[i + 1] === "-" && i + 2 < body.length) {
            const end = body[i + 2] as string;
            if (!isAlphanumeric(end) || end < start) return undefined;
            for (let code = start.charCodeAt(0); code <= end.charCodeAt(0); code++) codes.add(code);
            i += 3;
        } else {
            codes.add(start.charCodeAt(0));
            i++;
        }
    }
    const sorted = [...codes].toSorted((a, b) => a - b);
    let out = "";
    for (let i = 0; i < sorted.length;) {
        let j = i;
        while (j + 1 < sorted.length && sorted[j + 1] === (sorted[j] as number) + 1) j++;
        const first = String.fromCharCode(sorted[i] as number);
        const last = String.fromCharCode(sorted[j] as number);
        out += j - i >= 2 ? `${first}-${last}` : j === i ? first : `${first}${last}`;
        i = j + 1;
    }
    return out;
};

/**
 * `[L-MKN-ZA-DF-JE-E]` -> `[A-Z]` (see `canonicalClass`), and the long quantifier spellings `{0,}`, `{1,}`,
 * `{0,1}` -> `*`, `+`, `?` outside classes (an unescaped `{0,}` there is always a quantifier: anything else is a
 * syntax error). Not with the `v` flag (its classes nest and have set operations).
 */
const canonicalPattern = (pattern: string, flags: string): string | undefined => {
    if (flags.includes("v")) return undefined;
    let out = "";
    for (let i = 0; i < pattern.length;) {
        const char = pattern[i] as string;
        if (char === "\\") {
            out += pattern.slice(i, i + 2);
            i += 2;
            continue;
        }
        if (char === "[") {
            let end = i + 1;
            while (end < pattern.length && pattern[end] !== "]") end += pattern[end] === "\\" ? 2 : 1;
            const negated = pattern[i + 1] === "^";
            const body = pattern.slice(i + (negated ? 2 : 1), end);
            const canonical = body.length === 0 ? undefined : canonicalClass(body);
            out += canonical === undefined ? pattern.slice(i, end + 1) : `[${negated ? "^" : ""}${canonical}]`;
            i = end + 1;
            continue;
        }
        const quantifier = /^\{(0,|1,|0,1)\}/.exec(pattern.slice(i))?.[1];
        if (quantifier !== undefined) {
            out += quantifier === "0," ? "*" : quantifier === "1," ? "+" : "?";
            i += quantifier.length + 2;
            continue;
        }
        out += char;
        i++;
    }
    return out === pattern ? undefined : out;
};

/**
 * Bindings of a function that code moved out of it would lose: `"all"` its `this`, `arguments`, `new.target` and
 * `super`; `"except-this"` all but `this` (passed on by `.apply(this)`/`.call(this)`); `"none"` (an arrow's are the
 * caller's).
 */
export type OwnBindings = "all" | "except-this" | "none";

/**
 * A builder's local: its name, and which identifiers of that name the analysis resolves to another binding (one
 * declared inside the code that names it, in a nested function or block: it stays that binding wherever the code goes).
 */
export interface Holder {
    readonly name: string;
    readonly isOther: (identifier: Node) => boolean;
}

export const builderHolder = (id: Node & { name: string }, scopes: ScopeInfo): Holder => {
    const variable = scopes.variableOf(id);
    return {
        name: id.name,
        isOther: (identifier) => {
            const other = variable === undefined ? undefined : scopes.variableOf(identifier);
            return other !== undefined && other !== variable;
        },
    };
};

/** Whether `node` mentions the holder, or uses bindings of the function it leaves (`own`) outside functions that bind their own. */
export const uses = (node: Node | null | undefined, holder: Holder, own: OwnBindings): boolean => {
    if (node === null || node === undefined) return false;
    if (node.type === "Identifier") return (node.name === holder.name && !holder.isOther(node)) || (own !== "none" && node.name === "arguments");
    if (node.type === "ThisExpression") return own === "all";
    if (node.type === "MetaProperty" || node.type === "Super") return own !== "none";
    const inner = isFunctionNode(node) && node.type !== "ArrowFunctionExpression" ? "none" : own;
    let found = false;
    forEachChild(node, (child) => {
        found ||= uses(child, holder, inner);
    });
    return found;
};

/** A property's key as the property name it defines (`a`, `"a"` and `a` alike; `1` and `"1"` alike), when static. */
const definedName = (property: Node): string | undefined => (property.type !== "Property" || property.computed ? undefined : keyName(property.key));

/**
 * An object literal whose properties assignments may add to as the literal would have them: plain properties only (no
 * spread, getter or setter, which an assignment would run or copy), none named `__proto__` (a prototype, whose setters
 * an assignment could meet).
 */
export const isPlainLiteral = (node: Node): node is ObjectExpression =>
    node.type === "ObjectExpression" && node.properties.every((property) => property.type === "Property" && property.kind === "init" && definedName(property) !== "__proto__");

export interface PlannedStore {
    readonly into: ObjectExpression;
    readonly property: Node;
}

/**
 * `name.k = v;`, `name["k"] = v;` or `name[1] = v;` as a statement, where `v` doesn't name the holder (nor uses the
 * bindings of the function it leaves, `own`): the property `k: v` for `literal`, which the holder holds. Also
 * `name.j.k = v;` when `j` is the last property of `literal` (with the properties `planned` before it) and holds a
 * plain object literal: `k: v` goes in that one, where `v` still runs after every other value (it ran last). Not
 * `__proto__`, which a literal reads as the prototype; not computed keys other than literals (an assignment converts
 * its key after the value). An anonymous function or class `v` gets the key as its name, which the store didn't give
 * it (model 12).
 */
export const plannedStore = (statement: Statement, holder: Holder, own: OwnBindings, literal: ObjectExpression, planned: readonly PlannedStore[]): PlannedStore | undefined => {
    const { name } = holder;
    const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
    if (e?.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "MemberExpression" || uses(e.right, holder, own)) return undefined;
    const { object, property, computed } = e.left;
    const key = computed
        ? property.type === "Literal" && (typeof property.value === "string" || typeof property.value === "number")
            ? property.value
            : undefined
        : property.type === "Identifier"
          ? property.name
          : undefined;
    if (key === undefined || key === "__proto__") return undefined;
    const keyNode = typeof key === "string" && isIdentifierName(key) ? at<Expression>({ type: "Identifier", name: key }, property) : valueToNode(key, property);
    const stored = at<Node>({ type: "Property", kind: "init", key: keyNode, value: e.right, computed: false, method: false, shorthand: false }, statement) as Node;
    if (object.type === "Identifier") return object.name === name ? { into: literal, property: stored } : undefined;
    if (object.type !== "MemberExpression" || object.object.type !== "Identifier" || object.object.name !== name) return undefined;
    const outer = object.computed ? (object.property.type === "Literal" ? String(object.property.value) : undefined) : object.property.type === "Identifier" ? object.property.name : undefined;
    const last = [...literal.properties, ...planned.filter((store) => store.into === literal).map((store) => store.property)].at(-1);
    const into = last !== undefined && outer !== undefined && definedName(last) === outer && last.type === "Property" ? last.value : undefined;
    return into !== undefined && isPlainLiteral(into) ? { into, property: stored } : undefined;
};

/**
 * `(() => { var t = {}; t.a = x; t.b.c = y; return t; })()` -> `{ a: x, b: { c: y } }` when `t.b` holds a literal
 * (jscrambler builds object literals this way, also as `function () {...}.apply(this, arguments)`, `.apply(this)` and
 * `.call(this)`; the literal may start with properties, and may be assigned after a bare `var t;`). The values run in
 * order either way; setting a property of a fresh plain object creates it (no setter on Object.prototype but
 * `__proto__`'s, which stays: model 7), as the literal does; nothing else sees the object until it's returned, and a
 * value can't reach it without naming it. A plain function's own `arguments`, `new.target` and `super` aren't the
 * caller's, so values using them only move out of an arrow; its `this` is when the call passes it (a sloppy function
 * would replace an undefined or primitive `this`, but the caller then is sloppy too and has replaced its own).
 */
const objectFromBuilder = (node: Node, context: UnminifyContext): ObjectExpression | undefined => {
    if (node.type !== "CallExpression" || node.optional) return undefined;
    let fn: Node = node.callee;
    let passesThis = false;
    if (fn.type === "MemberExpression" && !fn.computed && fn.property.type === "Identifier" && (fn.property.name === "apply" || fn.property.name === "call")) {
        const [self, args] = node.arguments;
        if (self?.type !== "ThisExpression" || node.arguments.length > (fn.property.name === "apply" ? 2 : 1)) return undefined;
        // Reading `arguments` outside a function that has one throws: it must be the caller's own.
        if (args !== undefined && (args.type !== "Identifier" || args.name !== "arguments" || context.scopes.variableOf(args)?.scope.type !== "function")) return undefined;
        fn = fn.object;
        if (fn.type !== "FunctionExpression") return undefined;
        passesThis = true;
    } else if (node.arguments.length > 0) return undefined;
    if ((fn.type !== "FunctionExpression" && fn.type !== "ArrowFunctionExpression") || fn.params.length > 0 || fn.async || fn.generator || fn.body?.type !== "BlockStatement") return undefined;
    if (fn.type === "FunctionExpression" && fn.id !== null) return undefined;
    const own: OwnBindings = fn.type === "ArrowFunctionExpression" ? "none" : passesThis ? "except-this" : "all";
    const body = fn.body.body as Statement[];
    const [first] = body;
    if (first?.type !== "VariableDeclaration" || first.kind === "using" || first.kind === "await using" || first.declarations.length !== 1) return undefined;
    const [declarator] = first.declarations;
    if (declarator?.id.type !== "Identifier") return undefined;
    const name = declarator.id.name;
    const holder = builderHolder(declarator.id, context.scopes);
    let rest = body.slice(1);
    let literal = declarator.init;
    if (literal === null) {
        const [assign] = rest;
        const e = assign?.type === "ExpressionStatement" ? assign.expression : undefined;
        if (e?.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "Identifier" || e.left.name !== name) return undefined;
        literal = e.right;
        rest = rest.slice(1);
    }
    if (!isPlainLiteral(literal) || uses(literal, holder, own)) return undefined;
    const last = rest.at(-1);
    if (last?.type !== "ReturnStatement" || last.argument?.type !== "Identifier" || last.argument.name !== name) return undefined;
    const planned: PlannedStore[] = [];
    for (const statement of rest.slice(0, -1)) {
        const store = plannedStore(statement, holder, own, literal, planned);
        if (store === undefined) return undefined;
        planned.push(store);
    }
    for (const { into, property } of planned) into.properties.push(property as ObjectExpression["properties"][number]);
    return literal;
};

type NodeOf<T extends Node["type"]> = Extract<Node, { type: T }>;

const readableRegex = (node: NodeOf<"Literal">, context: UnminifyContext): Node | undefined => {
    if (!("regex" in node) || node.regex === undefined || node.regex === null) return undefined;
    const { flags } = node.regex;
    const unescaped = readablePattern(node.regex.pattern, flags);
    const canonical = canonicalPattern(unescaped ?? node.regex.pattern, flags);
    const pattern = canonical ?? unescaped;
    if (pattern === undefined) return undefined;
    if (unescaped !== undefined) context.did("regexEscapes", node);
    if (canonical !== undefined) context.did("regexClasses", node);
    return { ...node, regex: { pattern, flags }, raw: `/${pattern}/${flags}` } as Node;
};

/**
 * `(1, f)(x)` -> `f(x)`: both call `f` with no `this`, unless a `with` could answer `f` (then `f()` passes its
 * object) or `f` is `eval` (the direct call reads the caller's scope, the indirect one not).
 */
const directCall = (node: NodeOf<"CallExpression">, context: UnminifyContext): Expression | undefined => {
    const callee = node.callee;
    if (callee.type !== "SequenceExpression" || !callee.expressions.slice(0, -1).every((e) => e.type === "Literal")) return undefined;
    const target = callee.expressions.at(-1);
    if (target?.type !== "Identifier" || target.name === "eval" || context.hasWith) return undefined;
    context.did("directCalls", node);
    return at<Expression>({ ...node, callee: target }, node);
};

const booleanTail = (path: Path, node: NodeOf<"LogicalExpression">, context: UnminifyContext): Node | undefined => {
    if (node.operator === "??") return undefined;
    const neutral = node.operator !== "||";
    const isNeutral = (side: Node): boolean => side.type === "Literal" && side.value === neutral;
    if (isNeutral(node.left)) {
        context.did("booleanTails", node);
        return node.right;
    }
    // `a || false`, `a && true`: only truthiness can tell them from `a`.
    if (isNeutral(node.right) && isTestedForTruth(path)) {
        context.did("booleanTails", node);
        return node.left;
    }
    return undefined;
};

const invertNegation = (path: Path, node: NodeOf<"UnaryExpression">, context: UnminifyContext): Node | undefined => {
    if (node.operator !== "!") return undefined;
    const argument = node.argument;
    if (argument.type === "UnaryExpression" && argument.operator === "!") {
        if (isTestedForTruth(path)) {
            context.did("removeDoubleNot", node);
            return argument.argument;
        }
        context.refused("keeps !!: its boolean value is used", node);
    }
    if (argument.type === "BinaryExpression") {
        const negated = NEGATED_EQUALITY[argument.operator];
        if (negated === undefined) {
            context.refused("keeps the negation: only equality inverts exactly (NaN)", node);
            return undefined;
        }
        context.did("invertBooleanLogic", node);
        return at<BinaryExpression>({ ...argument, operator: negated }, node);
    }
    if (argument.type === "LogicalExpression" && argument.operator !== "??") {
        context.did("invertBooleanLogic", node);
        return at<Expression>(
            { type: "LogicalExpression", operator: argument.operator === "&&" ? "||" : "&&", left: not(argument.left, argument.left), right: not(argument.right, argument.right) },
            node
        );
    }
    if (argument.type === "LogicalExpression") context.refused("keeps !(a ?? b): no `??` form of its negation", node);
    return undefined;
};

const rewriteBinary = (node: Binary, context: UnminifyContext): Expression | undefined => {
    const typeofCheck = typeofUndefined(node);
    if (typeofCheck !== undefined) {
        context.did("typeofUndefined", node);
        return typeofCheck;
    }
    const swapped = SWAPPED[node.operator];
    if (swapped !== undefined && node.left.type !== "PrivateIdentifier" && isConstantValue(node.left, context) && !isConstantValue(node.right, context)) {
        context.did("yoda", node);
        return at<BinaryExpression>({ ...node, operator: swapped, left: node.right, right: node.left }, node);
    }
    if (swapped !== undefined && node.left.type === "Identifier" && CONSTANT_GLOBALS.has(node.left.name) && !context.isGlobal(node.left)) {
        context.refused(`keeps the order: \`${node.left.name}\` here may not be the global`, node);
    }
    const truncated = truncateNumbers(node);
    if (truncated !== undefined) context.did("truncateNumbers", node);
    return truncated;
};

const templateStrings = (path: Path, node: TemplateLiteral, context: UnminifyContext): TemplateLiteral | undefined => {
    if (path.parent?.type === "TaggedTemplateExpression") {
        if (node.expressions.some((expression) => expression.type === "Literal")) context.refused("keeps a tagged template's values: the tag sees them apart", node);
        return undefined;
    }
    const inlined = inlineTemplateStrings(node);
    if (inlined !== undefined) context.did("templateStrings", node);
    return inlined;
};

const dotAccess = (node: NodeOf<"MemberExpression">, context: UnminifyContext): Expression | undefined => {
    const property = node.property;
    if (!node.computed || property.type !== "Literal" || typeof property.value !== "string" || !isIdentifierName(property.value)) return undefined;
    context.did("computedKeys", node);
    return at<Expression>({ ...node, computed: false, property: at<Expression>({ type: "Identifier", name: property.value }, property) }, node);
};

type Keyed = NodeOf<"Property"> | MethodDefinition | PropertyDefinition | AccessorProperty;

/** `"a": x` -> `a: x`, in place. */
const identifierKey = (node: Keyed, context: UnminifyContext): void => {
    const key = node.key;
    if (key.type !== "Literal" || typeof key.value !== "string" || !isIdentifierName(key.value)) return;
    // `__proto__: x` sets the prototype where `"__proto__": x` does too but `["__proto__"]: x` doesn't; a class
    // `constructor` key decides what the constructor is; `static prototype` is an early error.
    if (key.value === "__proto__" || (node.type !== "Property" && (key.value === "constructor" || (node.static && key.value === "prototype")))) {
        context.refused(`keeps the key "${key.value}" as written`, node);
        return;
    }
    context.did("computedKeys", node);
    node.key = at<Expression>({ type: "Identifier", name: key.value }, key);
    node.computed = false;
};

/** `{ a: a }` -> `{ a }`, in place. Not `__proto__`: `{ __proto__: __proto__ }` sets the prototype, `{ __proto__ }` doesn't. */
const shorthand = (node: Keyed, context: UnminifyContext): void => {
    if (node.type !== "Property" || node.computed || node.method || node.kind !== "init" || node.shorthand) return;
    const value = node.value as Node;
    if (node.key.type !== "Identifier" || value.type !== "Identifier" || value.name !== node.key.name) return;
    if (value.name === "__proto__") {
        context.refused("keeps `__proto__: __proto__`: the shorthand doesn't set the prototype", node);
        return;
    }
    context.did("shorthand", node);
    node.shorthand = true;
};

/** One step; the caller repeats on the result. `undefined` also when object and class keys were changed in place. */
export const rewriteExpression = (path: Path, context: UnminifyContext): Node | undefined => {
    const node = path.node;
    switch (node.type) {
        case "Literal":
            return readableRegex(node, context);
        case "CallExpression": {
            const call = directCall(node, context);
            if (call !== undefined) return call;
            const object = objectFromBuilder(node, context);
            if (object !== undefined) context.did("objectLiterals", node);
            return object;
        }
        case "LogicalExpression":
            return booleanTail(path, node, context);
        case "UnaryExpression":
            return invertNegation(path, node, context);
        case "BinaryExpression":
            return rewriteBinary(node, context);
        case "TemplateLiteral":
            return templateStrings(path, node, context);
        case "MemberExpression":
            return dotAccess(node, context);
        case "Property":
        case "MethodDefinition":
        case "PropertyDefinition":
        case "AccessorProperty":
            // A refused key stays a string literal, which no shorthand has.
            identifierKey(node, context);
            shorthand(node, context);
            return undefined;
        default:
            return undefined;
    }
};
