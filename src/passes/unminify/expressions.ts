import type { BinaryExpression, Expression, Node, ObjectExpression, Statement, TemplateElement, TemplateLiteral, UnaryExpression } from "../../core/ast.js";
import { isFunctionNode, isIdentifierName } from "../../core/ast.js";
import { at, valueToNode } from "../../core/build.js";
import { forEachChild } from "../../core/traverse.js";
import { templateRaw } from "../../core/print.js";
import type { Path } from "../../core/traverse.js";
import type { UnminifyContext } from "./context.js";

/** `!argument`. */
export const not = (argument: Expression, origin: Node): Expression => at<UnaryExpression>({ type: "UnaryExpression", operator: "!", prefix: true, argument }, origin);

/** A binary expression node, `#x in o` included. */
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

/**
 * A value whose evaluation can't run code, throw, or depend on when it happens: a string, number, boolean or null
 * literal, `-number`, or the global `undefined`/`NaN`/`Infinity` (`-Infinity`).
 */
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

/** The number an operand is, as written: `5`, `-5`. */
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

/** Characters an escape in a pattern can stand for as themselves: letters, `_` and space mean the same unescaped. */
const isPlainPatternChar = (code: number): boolean => (code >= 65 && code <= 90) || (code >= 97 && code <= 122) || code === 95 || code === 32;

/**
 * `/\x70\x72\u006fgress/` -> `/progress/`: `\xHH` and `\uHHHH` escapes of letters, `_` and space written as the
 * characters. Those mean the same in and out of classes and with any flag, and can't join what's around them into
 * something else, except after `\c` (`\c\x41` is `\c` and `A` apart, `\cA` a control character), which stays. Digits
 * stay escaped (`\1\x31` would become the reference `\11`), as do other escapes.
 */
const readablePattern = (pattern: string): string | undefined => {
    let out = "";
    let changed = false;
    let afterControl = false;
    for (let i = 0; i < pattern.length;) {
        if (pattern[i] !== "\\") {
            out += pattern[i];
            afterControl = false;
            i++;
            continue;
        }
        const kind = pattern[i + 1];
        const digits = kind === "x" ? 2 : kind === "u" ? 4 : 0;
        const hex = pattern.slice(i + 2, i + 2 + digits);
        const code = digits > 0 && hex.length === digits && /^[\dA-Fa-f]+$/.test(hex) ? Number.parseInt(hex, 16) : undefined;
        if (code !== undefined && isPlainPatternChar(code) && !afterControl) {
            out += String.fromCharCode(code);
            changed = true;
            afterControl = false;
            i += 2 + digits;
            continue;
        }
        out += pattern.slice(i, i + 2);
        afterControl = kind === "c";
        i += 2;
    }
    return changed ? out : undefined;
};

/** Whether `node` mentions the name `name`, or (`ownThis`) uses `this`/`arguments` outside functions that bind their own. */
const uses = (node: Node | null | undefined, name: string, ownThis: boolean): boolean => {
    if (node === null || node === undefined) return false;
    if (node.type === "Identifier") return node.name === name || (ownThis && node.name === "arguments");
    if (node.type === "ThisExpression" || node.type === "MetaProperty" || node.type === "Super") return ownThis;
    const inner = ownThis && isFunctionNode(node) && node.type !== "ArrowFunctionExpression" ? false : ownThis;
    let found = false;
    forEachChild(node, (child) => {
        found ||= uses(child, name, inner);
    });
    return found;
};

/**
 * `(() => { var t; t = {}; t.a = x; t["b"] = y; return t; })()` -> `{ a: x, b: y }` (jscrambler builds object
 * literals this way, also as `function () {...}.apply(this, arguments)`). The values run in order either way;
 * setting a property of a fresh plain object creates it (no setter on Object.prototype but `__proto__`'s, which
 * stays: model 7), as the literal does; nothing else sees the object until it's returned, and a value can't reach it
 * without naming it. A plain function's own `this` and `arguments` aren't the caller's (even through `.apply(this,
 * arguments)`: a sloppy function gets the global object for an undefined `this`, and a fresh `arguments`), so values
 * using them only move out of an arrow.
 */
const objectFromBuilder = (node: Node, context: UnminifyContext): ObjectExpression | undefined => {
    if (node.type !== "CallExpression" || node.optional) return undefined;
    let fn: Node = node.callee;
    if (fn.type === "MemberExpression" && !fn.computed && fn.property.type === "Identifier" && fn.property.name === "apply") {
        const [self, args] = node.arguments;
        if (node.arguments.length !== 2 || self?.type !== "ThisExpression" || args?.type !== "Identifier" || args.name !== "arguments") return undefined;
        // Reading `arguments` outside a function that has one throws: it must be the caller's own.
        if (context.scopes.variableOf(args)?.scope.type !== "function") return undefined;
        fn = fn.object;
        if (fn.type !== "FunctionExpression") return undefined;
    } else if (node.arguments.length > 0) return undefined;
    const ownThis = fn.type === "FunctionExpression";
    if ((fn.type !== "FunctionExpression" && fn.type !== "ArrowFunctionExpression") || fn.params.length > 0 || fn.async || fn.generator || fn.body?.type !== "BlockStatement") return undefined;
    if (fn.type === "FunctionExpression" && fn.id !== null) return undefined;
    const body = fn.body.body as Statement[];
    const [first] = body;
    if (first?.type !== "VariableDeclaration" || first.kind === "using" || first.kind === "await using" || first.declarations.length !== 1) return undefined;
    const [declarator] = first.declarations;
    if (declarator?.id.type !== "Identifier") return undefined;
    const name = declarator.id.name;
    let rest = body.slice(1);
    if (declarator.init === null) {
        const [assign] = rest;
        const e = assign?.type === "ExpressionStatement" ? assign.expression : undefined;
        if (e?.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "Identifier" || e.left.name !== name || e.right.type !== "ObjectExpression" || e.right.properties.length > 0)
            return undefined;
        rest = rest.slice(1);
    } else if (declarator.init.type !== "ObjectExpression" || declarator.init.properties.length > 0) return undefined;
    const last = rest.at(-1);
    if (last?.type !== "ReturnStatement" || last.argument?.type !== "Identifier" || last.argument.name !== name) return undefined;
    const properties: Node[] = [];
    for (const statement of rest.slice(0, -1)) {
        const e = statement.type === "ExpressionStatement" ? statement.expression : undefined;
        if (e?.type !== "AssignmentExpression" || e.operator !== "=" || e.left.type !== "MemberExpression") return undefined;
        const { object, property, computed } = e.left;
        if (object.type !== "Identifier" || object.name !== name || uses(e.right, name, ownThis)) return undefined;
        const key = computed
            ? property.type === "Literal" && (typeof property.value === "string" || typeof property.value === "number")
                ? property.value
                : undefined
            : property.type === "Identifier"
              ? property.name
              : undefined;
        if (key === undefined || key === "__proto__") return undefined;
        const keyNode = typeof key === "string" && isIdentifierName(key) ? at<Expression>({ type: "Identifier", name: key }, property) : valueToNode(key, property);
        properties.push(at<Node>({ type: "Property", kind: "init", key: keyNode, value: e.right, computed: false, method: false, shorthand: false }, statement) as Node);
    }
    return at<ObjectExpression>({ type: "ObjectExpression", properties }, node);
};

/**
 * Rewrite the expression at `path` (one step; the caller repeats on the result). Returns the replacement, or
 * `undefined` when there is none: nothing applies, or object and class keys were changed in place.
 */
export const rewriteExpression = (path: Path, context: UnminifyContext): Node | undefined => {
    const node = path.node;
    switch (node.type) {
        case "Literal": {
            if (!("regex" in node) || node.regex === undefined || node.regex === null) return undefined;
            const pattern = readablePattern(node.regex.pattern);
            if (pattern === undefined) return undefined;
            context.did("regexEscapes", node);
            return { ...node, regex: { pattern, flags: node.regex.flags }, raw: `/${pattern}/${node.regex.flags}` } as Node;
        }
        case "CallExpression": {
            const object = objectFromBuilder(node, context);
            if (object !== undefined) context.did("objectLiterals", node);
            return object;
        }
        case "UnaryExpression": {
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
        }
        case "BinaryExpression": {
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
        }
        case "TemplateLiteral": {
            if (path.parent?.type === "TaggedTemplateExpression") {
                if (node.expressions.some((expression) => expression.type === "Literal")) context.refused("keeps a tagged template's values: the tag sees them apart", node);
                return undefined;
            }
            const inlined = inlineTemplateStrings(node);
            if (inlined !== undefined) context.did("templateStrings", node);
            return inlined;
        }
        case "MemberExpression": {
            const property = node.property;
            if (!node.computed || property.type !== "Literal" || typeof property.value !== "string" || !isIdentifierName(property.value)) return undefined;
            context.did("computedKeys", node);
            return at<Expression>({ ...node, computed: false, property: at<Expression>({ type: "Identifier", name: property.value }, property) }, node);
        }
        case "Property":
        case "MethodDefinition":
        case "PropertyDefinition":
        case "AccessorProperty": {
            const key = node.key;
            if (key.type === "Literal" && typeof key.value === "string" && isIdentifierName(key.value)) {
                // `__proto__: x` sets the prototype where `"__proto__": x` does too but `["__proto__"]: x` doesn't;
                // a class `constructor` key decides what the constructor is; `static prototype` is an early error.
                if (key.value === "__proto__" || (node.type !== "Property" && (key.value === "constructor" || (node.static && key.value === "prototype")))) {
                    context.refused(`keeps the key "${key.value}" as written`, node);
                    return undefined;
                }
                context.did("computedKeys", node);
                node.key = at<Expression>({ type: "Identifier", name: key.value }, key);
                node.computed = false;
            }
            // `{ a: a }` -> `{ a }`. Not `__proto__`: `{ __proto__: __proto__ }` sets the prototype, `{ __proto__ }` doesn't.
            if (node.type !== "Property" || node.computed || node.method || node.kind !== "init" || node.shorthand) return undefined;
            const value = node.value as Node;
            if (node.key.type === "Identifier" && value.type === "Identifier" && value.name === node.key.name) {
                if (value.name === "__proto__") {
                    context.refused("keeps `__proto__: __proto__`: the shorthand doesn't set the prototype", node);
                    return undefined;
                }
                context.did("shorthand", node);
                node.shorthand = true;
            }
            return undefined;
        }
        default:
            return undefined;
    }
};
