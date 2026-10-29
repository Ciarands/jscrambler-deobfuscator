import { describe, expect, it } from "vitest";
import type { Node } from "../src/core/ast.js";
import { evaluate } from "../src/core/evaluate.js";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";

const templateOf = (code: string): Node => {
    let found: Node | undefined;
    traverse(parse(code), {
        TemplateLiteral: (path) => {
            found ??= path.node;
        },
    });
    if (found === undefined) throw new Error("no template literal");
    return found;
};

/** The expression of the one statement `code` holds. */
const expression = (code: string): Node => (parse(code).body[0] as unknown as { expression: Node }).expression;

describe("evaluate", () => {
    it("has no value for a template part with an invalid escape", () => {
        // Only a tagged template may contain one; its cooked value is null, not an empty string.
        expect(evaluate(templateOf("tag`\\unicode`")).ok).toBe(false);
        expect(evaluate(templateOf("tag`ok${1}\\xZ`")).ok).toBe(false);
        expect(evaluate(templateOf("`a${1}b`"))).toEqual({ ok: true, value: "a1b" });
    });

    it("negates fresh objects to false, but not literals that run code to build", () => {
        for (const code of ["![]", "![1, 'a']", "!{}", "!function () {}", "!(() => 1)"]) expect(evaluate(expression(code))).toEqual({ ok: true, value: false });
        for (const code of ["![f()]", "!{ a: f() }", "!{ get a() { return 1; } }"]) expect(evaluate(expression(code)).ok).toBe(false);
    });
});
