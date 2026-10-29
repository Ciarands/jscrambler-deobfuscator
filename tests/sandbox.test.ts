import { afterAll, beforeAll, describe, expect, it } from "vitest";
import { Sandbox } from "../src/core/sandbox.js";

describe("sandbox", () => {
    let sandbox: Sandbox;
    beforeAll(async () => {
        sandbox = await Sandbox.create({ memoryBytes: 32 * 1024 * 1024, stackBytes: 512 * 1024, timeoutMs: 200 });
    });
    afterAll(() => sandbox.dispose());

    it("copies strings out whole, NULs included", () => {
        expect(sandbox.run(`"a" + String.fromCharCode(0) + "b"`)).toEqual({ ok: true, value: "a\0b" });
        expect(sandbox.run(`"\\u0000tag"`)).toEqual({ ok: true, value: "\0tag" });
    });

    it("exposes nothing from the host", () => {
        expect(sandbox.run(`[typeof window, typeof process, typeof require, typeof console].join()`)).toEqual({
            ok: true,
            value: "undefined,undefined,undefined,undefined",
        });
    });

    it("interrupts runaway code and stays usable afterwards", () => {
        const looped = sandbox.run("for (;;) {}");
        expect(looped).toMatchObject({ ok: false, timedOut: true });
        expect(sandbox.run("1 + 1")).toEqual({ ok: true, value: 2 });
        // A guest error that merely says so is no timeout.
        expect(sandbox.run('throw new Error("interrupted")')).toEqual({ ok: false, error: "interrupted", timedOut: false });
    });

    it("calls guest functions with data both ways, keeping what JSON can't carry", () => {
        sandbox.run(`globalThis.echo = { back: function (v) { return [v, typeof v[0], 1 / v[3] < 0, v[5].length]; } };`);
        const payload = [undefined, Number.NaN, Number.POSITIVE_INFINITY, -0, Number.NEGATIVE_INFINITY, "a\0b", { "": 1 }];
        expect(sandbox.invoke(["echo", "back"], payload)).toEqual({ ok: true, value: [payload, "undefined", true, 3] });
    });

    it("reports a guest exception from an invoked function as a failure", () => {
        sandbox.run(`globalThis.boom = function () { throw new TypeError("nope"); };`);
        expect(sandbox.invoke(["boom"], null)).toEqual({ ok: false, error: "nope", timedOut: false });
        expect(sandbox.invoke(["missing", "fn"], null)).toMatchObject({ ok: false });
    });

    it("calls functions of a held object, which no guest name reaches", () => {
        const names = "Object.getOwnPropertyNames(globalThis).sort().join()";
        const before = sandbox.run(names);
        const held = sandbox.hold("({ inc: function (v) { return v + 1; } })");
        if (!held.ok) throw new Error(held.error);
        expect(sandbox.invoke(["inc"], 1, undefined, held.held)).toEqual({ ok: true, value: 2 });
        expect(sandbox.run(names)).toEqual(before);
        // A guest global of the same name is another thing.
        sandbox.run("globalThis.inc = function () { return 0; };");
        expect(sandbox.invoke(["inc"], 1, undefined, held.held)).toEqual({ ok: true, value: 2 });
    });

    it("executes a statement for its effects even when its value can't be copied out", () => {
        const cyclic = "globalThis.table = (function () { var r = [[]]; r[0][0] = r; return r; })();";
        expect(sandbox.execute(cyclic)).toEqual({ ok: true, value: undefined });
        expect(sandbox.run("table[0][0] === table")).toEqual({ ok: true, value: true });
        expect(sandbox.run(cyclic)).toMatchObject({ ok: false });
    });

    it("is repeatable: Math.random is seeded", async () => {
        const other = await Sandbox.create();
        const draw = "[Math.random(), Math.random()].join()";
        const fresh = await Sandbox.create();
        expect(other.run(draw)).toEqual(fresh.run(draw));
        other.dispose();
        fresh.dispose();
    });
});
