import { describe, expect, it, vi } from "vitest";
import { deobfuscate, ParseError, UnknownPassError } from "../src/index.js";

describe("deobfuscate", () => {
    it("round-trips code with no passes and the output is stable", async () => {
        const input = "var a=[arguments];if(a[0]){a[1]=function(x){return x+1}(2)}else{for(;;)break}";
        const first = await deobfuscate(input);
        const second = await deobfuscate(first.code);
        expect(second.code).toBe(first.code);
        expect(first.code).toContain("a[1] = function (x) {");
    });

    it("parses scripts that are not valid modules", async () => {
        const { code } = await deobfuscate("with (o) { x = 1; }");
        expect(code).toBe("with (o) {\n  x = 1;\n}\n");
    });

    it("throws ParseError with a line and column", async () => {
        const error = await deobfuscate("var ok = 1;\nvar x = ;", { filename: "broken.js" }).catch((e: unknown) => e);
        expect(error).toBeInstanceOf(ParseError);
        expect((error as ParseError).message).toMatch(/broken\.js: .+ \(2:9\)/);
    });

    it("rejects unknown pass names before doing any work", async () => {
        await expect(deobfuscate("not even valid (", { passes: ["nope"] })).rejects.toBeInstanceOf(UnknownPassError);
        await expect(deobfuscate("x", { skip: ["nope"] })).rejects.toBeInstanceOf(UnknownPassError);
    });

    it("never writes to the console by default", async () => {
        const spies = (["log", "info", "warn", "error", "debug"] as const).map((method) => vi.spyOn(console, method).mockImplementation(() => {}));
        await deobfuscate("x = 1");
        await deobfuscate("x =").catch(() => {});
        for (const spy of spies) expect(spy).not.toHaveBeenCalled();
        vi.restoreAllMocks();
    });
});
