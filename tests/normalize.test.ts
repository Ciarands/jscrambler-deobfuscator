import { describe, expect, it } from "vitest";
import { parse } from "../src/core/parse.js";
import { traverse } from "../src/core/traverse.js";
import { deobfuscate } from "../src/index.js";
import { observe } from "./helpers.js";

const normalize = async (code: string) => (await deobfuscate(code, { passes: ["normalize"] })).code;

const leftoverSequences = (code: string): number => {
    let count = 0;
    traverse(parse(code), {
        ExpressionStatement: (path) => void (path.node.expression.type === "SequenceExpression" && count++),
        ReturnStatement: (path) => void (path.node.argument?.type === "SequenceExpression" && count++),
        IfStatement: (path) => void (path.node.test.type === "SequenceExpression" && count++),
        VariableDeclarator: (path) => void (path.node.init?.type === "SequenceExpression" && count++),
    });
    return count;
};

describe("normalize", () => {
    it("splits sequences everywhere, including inside functions that a split moved, and keeps evaluation order", async () => {
        const input = `
            var f = function () { return t(1), t(2), t(3); }, g;
            g = function () { t(4), t(5); if ((t(6), t(7))) t(8), t(9); }, f(), g(), t(10);
            (function () { var u = t(13), w = (t(14), t(15)), z = (t(16), t(17)); t([u, w, z]); })();
            (function () { throw t(11), t(12); })
        `;
        const output = await normalize(input);
        expect(leftoverSequences(output)).toBe(0);
        expect(observe(output, { trace: true })).toBe(observe(input, { trace: true }));
    });

    it("uses dot access only for identifier keys and folds !0/!1", async () => {
        const output = await normalize(`o["ok"] = o["not-ok"] + o["1x"] + o["$_"]; x = [!0, !1, !2];`);
        expect(output).toBe(`o.ok = o["not-ok"] + o["1x"] + o.$_;\nx = [true, false, !2];\n`);
    });
});
