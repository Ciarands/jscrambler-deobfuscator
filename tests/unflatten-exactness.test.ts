import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import type { Node } from "../src/core/ast.js";
import { SourceMap } from "../src/core/log.js";
import { parse } from "../src/core/parse.js";
import { print } from "../src/core/print.js";
import { forEachChild } from "../src/core/traverse.js";
import { deobfuscate } from "../src/index.js";
import { silentLogger } from "../src/logger.js";
import { unflatten } from "../src/passes/unflatten/index.js";
import { runPipeline } from "../src/pipeline/run.js";

/** What `f()` returns (or throws), as JSON. */
const run = (code: string): string => {
    const context: Record<string, unknown> = {};
    try {
        runInNewContext(`${code}\nresult = f();`, context);
        return JSON.stringify(context["result"]);
    } catch (error) {
        return `threw ${error instanceof Error ? error.constructor.name : String(error)}`;
    }
};

/** Unflatten `source`; returns the output, whether a machine is left, and both behaviours. */
const unflattened = async (source: string) => {
    const { code } = await deobfuscate(source, { passes: ["unflatten"] });
    return { code, flat: code.includes("switch"), expected: run(source), got: run(code) };
};

describe("unflatten keeps what dead code declares (A5)", () => {
    it("keeps a `var` declared only in an unreachable case", async () => {
        const r = await unflattened(`
function f() {
  "use strict";
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: x = 3; s = 0; break;
    case 2: var x = 1; s = 0; break;
  }
  return x;
}`);
        expect(r.expected).toBe("3");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("keeps a `var` declared after a `return` in a case body", async () => {
        const r = await unflattened(`
function f() {
  "use strict";
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: y = 4; s = 2; break;
    case 2: return y; var y; s = 0; break;
  }
}`);
        expect(r.expected).toBe("4");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("keeps a `var` declared after a `return` in a nested block", async () => {
        const r = await unflattened(`
function f() {
  "use strict";
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: q = 5; s = 2; break;
    case 2: if (q) { return q; var q; } s = 0; break;
  }
}`);
        expect(r.expected).toBe("5");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("keeps a function declared in an unreachable case that a reachable case calls", async () => {
        for (const mode of ["", '"use strict";']) {
            const r = await unflattened(`
function f() {
  ${mode}
  var r;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: r = helper(2); s = 0; break;
    case 2: function helper(n) { return n * 21; } s = 0; break;
  }
  return r;
}`);
            expect(r.expected).toBe("42");
            expect(r.flat).toBe(false);
            expect(r.got).toBe(r.expected);
        }
    });

    it("leaves a machine whose case-level function is compared across dispatches", async () => {
        // Every dispatch enters the switch block again and creates a new `g`: one hoisted `g` would compare equal.
        const r = await unflattened(`
function f() {
  var first, same;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: first = g; s = 2; break;
    case 2: same = first === g; s = 0; break;
    case 3: function g() {} s = 0; break;
  }
  return same;
}`);
        expect(r.expected).toBe("false");
        expect(r.got).toBe(r.expected);
    });

    it("leaves a machine whose reachable code reads a `let` of an unreachable case", async () => {
        // The binding is in its temporal dead zone forever; dropping it would make `z` a global lookup.
        const r = await unflattened(`
function f() {
  var r;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: try { r = typeof z; } catch (e) { r = e.constructor.name; } s = 0; break;
    case 2: let z = 1; s = 0; break;
  }
  return r;
}`);
        expect(r.expected).toBe('"ReferenceError"');
        expect(r.got).toBe(r.expected);
    });

    it("drops an unreachable case's `let` that nothing reachable refers to", async () => {
        const r = await unflattened(`
function f() {
  var r;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: r = typeof z; s = 0; break;
    case 2: let w = 1; s = 0; break;
  }
  return r;
}`);
        expect(r.expected).toBe('"undefined"');
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });
});

describe("unflatten keeps lexical loop initializers in their own scope (A6)", () => {
    it("doesn't leak a `let` init into the enclosing block", async () => {
        const r = await unflattened(`
function f() {
  let i = 9, seen = [];
  var s = 1;
  for (let i = 0; s !== 0;) switch (s) {
    case 1: seen.push(i); i++; s = i < 2 ? 1 : 0; break;
  }
  return [i, seen];
}`);
        expect(r.expected).toBe("[9,[0,1]]");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("keeps the per-iteration bindings closures capture", async () => {
        const r = await unflattened(`
function f() {
  var fs = [];
  var s = 1;
  for (let j = 0; s !== 0;) switch (s) {
    case 1: fs.push(function () { return j; }); j++; s = j < 3 ? 1 : 0; break;
  }
  return fs.map(function (g) { return g(); });
}`);
        expect(r.expected).toBe("[1,2,3]");
        expect(r.got).toBe(r.expected);
    });

    it("unflattens when closures capture a binding that never changes", async () => {
        const r = await unflattened(`
function f() {
  var fs = [], n = 0;
  var s = 1;
  for (let k = 5; s !== 0;) switch (s) {
    case 1: fs.push(function () { return k; }); n++; s = n < 3 ? 1 : 0; break;
  }
  return fs.map(function (g) { return g(); });
}`);
        expect(r.expected).toBe("[5,5,5]");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });
});

describe("unflatten machines whose initial state is a choice", () => {
    it("starts with the choice when it is made right before the loop", async () => {
        const r = await unflattened(`
function f() {
  var log = [];
  for (var round = 0; round < 2; round++) {
    var s = round === 0 ? 2 : 3;
    for (; s !== 0;) switch (s) {
      case 2: log.push("a"); s = 3; break;
      case 3: log.push("b"); s = 0; break;
    }
  }
  return log;
}`);
        expect(r.expected).toBe('["a","b","b"]');
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("leaves the machine when other code runs between the choice and the loop", async () => {
        // Evaluating the choice at the loop would run c() after t().
        const r = await unflattened(`
function f() {
  var log = [];
  function c() { log.push("c"); return true; }
  function t() { log.push("t"); }
  var s = c() ? 2 : 3;
  t();
  for (; s !== 0;) switch (s) {
    case 2: log.push("a"); s = 3; break;
    case 3: log.push("b"); s = 0; break;
  }
  return log;
}`);
        expect(r.expected).toBe('["c","t","a","b"]');
        expect(r.got).toBe(r.expected);
    });
});

/** Nodes reachable from `root` more than once (the same object in two places). */
const sharedNodes = (root: Node): Node[] => {
    const seen = new Set<Node>();
    const shared: Node[] = [];
    const walk = (node: Node): void => {
        if (seen.has(node)) shared.push(node);
        seen.add(node);
        forEachChild(node, walk);
    };
    walk(root);
    return shared;
};

describe("unflatten writes every block once (A10)", () => {
    const source = `
var calls = 0;
function bump() { calls++; return calls > 1; }
function f() {
  var n = 0;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: s = bump() ? 2 : 2; break;
    case 2: n += 10; s = bump() ? (bump() ? 3 : 0) : (bump() ? 3 : 0); break;
    case 3: n += 100; s = 0; break;
  }
  return [n, calls];
}`;

    it("keeps a same-target branch's test for its effects", async () => {
        const r = await unflattened(source);
        expect(r.expected).toBe("[110,3]");
        expect(r.flat).toBe(false);
        expect(r.got).toBe(r.expected);
    });

    it("never puts one node in two places", async () => {
        const program = parse(source);
        await runPipeline(program, [unflatten], { logger: silentLogger, source: new SourceMap(source) });
        expect(print(program)).not.toContain("switch");
        expect(sharedNodes(program)).toEqual([]);
    });
});

/** A machine whose one case builds a class with members decorated by `decorator`. */
const decoratedMachine = (decorator: string): string => `
function f() {
  var x;
  var s = 1;
  for (; s !== 0;) switch (s) {
    case 1: x = class { @${decorator} m() {} @${decorator} p = 1; }; s = 0; break;
  }
  return x;
}`;

describe("unflatten sees every use of the state", () => {
    it("leaves a machine whose state a decorator reads", async () => {
        // Decorators don't run in Node yet, so this checks the decision: the state escapes into the decorator call.
        expect((await unflattened(decoratedMachine("d(s)"))).flat).toBe(true);
        expect((await unflattened(decoratedMachine("d(1)"))).flat).toBe(false);
    });
});
