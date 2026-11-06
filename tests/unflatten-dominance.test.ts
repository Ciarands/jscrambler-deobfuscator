import { describe, expect, it } from "vitest";
import { dominance } from "../src/passes/unflatten/structure.js";

const graph =
    (edges: Record<string, string[]>) =>
    (id: string): readonly string[] =>
        edges[id] ?? [];

describe("unflatten dominance", () => {
    it("joins a diamond's branches at the entry", () => {
        const { idom, dominates } = dominance("a", ["a", "c", "b", "d"], graph({ a: ["b", "c"], b: ["d"], c: ["d"] }));
        expect(Object.fromEntries(idom)).toEqual({ a: "a", b: "a", c: "a", d: "a" });
        expect(dominates("a", "d")).toBe(true);
        expect(dominates("b", "d")).toBe(false);
    });

    it("keeps a loop header above its body and exit", () => {
        const { idom, dominates } = dominance("a", ["a", "b", "e", "c"], graph({ a: ["b"], b: ["c", "e"], c: ["b"] }));
        expect(Object.fromEntries(idom)).toEqual({ a: "a", b: "a", c: "b", e: "b" });
        expect(dominates("b", "c")).toBe(true);
        expect(dominates("c", "b")).toBe(false);
    });
});
