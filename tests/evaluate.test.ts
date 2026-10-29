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

describe("evaluate", () => {
    it("has no value for a template part with an invalid escape", () => {
        // Only a tagged template may contain one; its cooked value is null, not an empty string.
        expect(evaluate(templateOf("tag`\\unicode`")).ok).toBe(false);
        expect(evaluate(templateOf("tag`ok${1}\\xZ`")).ok).toBe(false);
        expect(evaluate(templateOf("`a${1}b`"))).toEqual({ ok: true, value: "a1b" });
    });
});
