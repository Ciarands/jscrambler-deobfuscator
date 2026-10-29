import { runInNewContext } from "node:vm";
import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";

// A miniature of jscrambler's runtime: its string decoder (stage calls shuffle the table until the first call that
// matches no stage freezes it into a lookup), a wrapper, the stage calls driving the decoder inside an opaque predicate,
// and code that only needs decoded strings.
const RUNTIME = `
function G() {}
G.D = (function () {
  var Q = {
    get: (function (key) {
      var T = "c,b,a";
      T = T.split(",");
      var R = 0;
      var S = function (x) {
        if (R === 0 && x === 7) { R += 1; T.unshift.apply(T, T.splice(-2, 2).splice(0, 1)); }
        else { Q.get = L; return L(x); }
        return R;
      };
      var L = function (y) { return T[y]; };
      return S;
    })("k")
  };
  return Q;
})();
G.w = function () { return typeof G.D.get === "function" ? G.D.get.apply(G.D, arguments) : G.D.get; };
var out = [];
if (G.w(7) === 1) out.push("stage");
function f(host) {
  var unused = [arguments];
  var kept = host.side();
  out.push(G.w(0), G.w(1));
}
`;

const run = (code: string): string => {
    const context: Record<string, unknown> = { host: { side: () => 1 } };
    runInNewContext(code, context);
    return JSON.stringify(context.result);
};

describe("cleanup", () => {
    it("removes the runtime once nothing uses it, and unused locals with pure initializers", async () => {
        const program = `${RUNTIME}f(host);\nresult = out;\n`;
        const { code } = await deobfuscate(program);
        expect(run(code)).toBe(run(program));
        expect(code).not.toMatch(/\bG\b/);
        expect(code).not.toContain("unused");
        expect(code).toContain("var kept = host.side();");
        expect(code).toContain(`out.push("b", "c");`);
    });

    it("keeps the runtime when the storage object escapes", async () => {
        const program = `${RUNTIME}f(host);\nhost.exported = G;\nresult = out;\n`;
        const { code } = await deobfuscate(program);
        expect(run(code)).toBe(run(program));
        expect(code).toContain("function G() {}");
        expect(code).toContain("G.D = ");
    });
});

/** What a script leaves in `result`; `setTimeout` callbacks (code after the prelude) run once it has finished. */
const observed = (source: string): string => {
    const timers: (() => void)[] = [];
    const context: Record<string, unknown> = { setTimeout: (callback: () => void) => timers.push(callback) };
    runInNewContext(source, context);
    for (const callback of timers) callback();
    return JSON.stringify(context.result);
};

/** A storage function, and `f` (from `body`) called after the prelude with an object that has a `G` of its own. */
const withAliases = (body: string, prelude = "") => `
function G() {}
G.k = "storage";
${prelude}
${body}
setTimeout(function () { result = f({ G: { k: "other" } }); });
`;

describe("cleanup: aliases of the storage object", () => {
    it("replaces reads of locals and parameters that only hold the storage object with its name", async () => {
        const bodies = [
            // Reads after the declaration, in functions created later, and in a function declaration nothing can call
            // before the alias is set (only a directive comes first).
            `function f() { "use strict"; var s = G; function inner() { return s.k; } var g = function () { return s.k; }; return [s.k, inner(), g()]; }`,
            // A parameter the call passes the storage function in (the parameter itself stays); an alias initialised
            // from another one, the round after.
            `function f() { var s = G; var t = s; return (function (p) { return [p.k, t.k]; })(G); }`,
            // One of several declarators.
            `function f() { var s = G, x = 1; return [s.k, x]; }`,
        ];
        for (const body of bodies) {
            const program = withAliases(body);
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observed(code)).toBe(observed(program));
            expect(code).not.toMatch(/\b[st]\b|\bp\.k\b/);
        }
    });

    it("keeps reads that may not see the storage object, or where its name means something else", async () => {
        const cases = {
            readBeforeDeclaration: "function f() { var t = s; var s = G; return [typeof t, s.k]; }",
            // The matcher takes `p` and `t` for aliases (it sees `s`'s declaration first), but they get `s` before it is set.
            passedBeforeDeclaration: "function f() { var r = h(); var s = G; function h() { return (function (p) { return typeof p; })(s); } return [r, s.k]; }",
            initialisedBeforeDeclaration: "function f() { var r = h(); var s = G; function h() { var t = s; return typeof t; } return [r, s.k]; }",
            calledBeforeDeclaration: "function f() { var r = inner(); var s = G; function inner() { return typeof s; } return [r, inner()]; }",
            calledFromEarlierDeclarator: "function f() { var r = inner(), s = G; function inner() { return typeof s; } return r; }",
            shadowed: `function f() { var s = G; return (function (G) { return s.k; })({ k: "other" }); }`,
            insideWith: "function f(o) { var s = G; with (o) { return s.k; } }",
            shorthand: "function f() { var s = G; return Object.keys({ s }); }",
        };
        for (const [name, body] of Object.entries(cases)) {
            const program = withAliases(body);
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observed(code), name).toBe(observed(program));
            expect(code, name).toMatch(/\b[st] = /);
        }
    });

    it("keeps every alias when the storage function is reassigned", async () => {
        const program = withAliases(`function f() { var s = G; G = { k: "other" }; return s.k; }`);
        const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
        expect(observed(code)).toBe(observed(program));
        expect(code).toContain("return s.k;");
    });
});

// The prelude's `if` runs without effects outside the storage object; simplify then replaces it by its branch.
const withBranch = (branch: string) => `
(function () {
  function G() {}
  var FLAG = true;
  function put() { String.x = 42; return 1; }
  function take() { var v = String.x; delete String.x; return v; }
  if (FLAG) { ${branch} }
  G.n = 2;
  setTimeout(function () { result = [G.n, G.v, String.x]; });
})();
`;

const rewrite = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["emulate", "simplify", "cleanup"] })).code;

describe("cleanup: statement facts across rewrites", () => {
    it("removes a definition whose statement was seen pure and replaced by one equivalent statement", async () => {
        const input = withBranch("G.k = (put(), delete String.x, 1);");
        const code = await rewrite(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).not.toContain("G.k");
    });

    it("doesn't take a statement split in parts for pure part by part", async () => {
        // Together the parts change nothing outside G; alone, the first one does, and the second depends on it.
        const input = withBranch("G.k = put(); G.v = take();");
        const code = await rewrite(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).toContain("G.k = put();");
    });
});

// A setup call like jscrambler's: it adds a builtin alias (`q1` for split) and a global holding another one.
const withSetup = (later: string, setup = "") => `
function G() {}
G.k = 1;
(function () {
  globalThis.Hx = { f: String.fromCharCode };
  Object.defineProperty(String.prototype, "q1", { value: String.prototype.split, configurable: true, writable: true });
  ${setup}
})();
setTimeout(function () { ${later} });
`;

describe("cleanup: the setup call", () => {
    it("removes it once no code names an alias or a global it added", async () => {
        const input = withSetup('result = "a,b".q1(",");');
        const { code } = await deobfuscate(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).not.toContain("Hx");
    });

    it("keeps it while code names a global it added", async () => {
        const reads = [
            'var key = "f"; result = [Hx[key](65), "a,b".q1(",")];', // by name, once the key is known
            'result = [globalThis["Hx"].f(66)];', // as a property of the global object
        ];
        for (const read of reads) {
            const input = withSetup(read);
            const { code } = await deobfuscate(input);
            expect(observed(code)).toBe(observed(input));
            expect(code).toContain("globalThis.Hx = ");
        }
    });

    it("keeps a call that also changes or deletes a builtin", async () => {
        for (const setup of ['String.prototype.trim = function () { return "changed"; };', "delete String.prototype.trim;"]) {
            const input = withSetup('result = ["a,b".q1(","), typeof " x ".trim];', setup);
            const { code } = await deobfuscate(input);
            expect(observed(code)).toBe(observed(input));
            expect(code).toContain("String.prototype.trim");
        }
    });

    it("keeps a runtime definition that changes any builtin, not only the common ones", async () => {
        const input = 'function G() {}\nG.k = (function () { Map.prototype.tag = function () { return "tagged"; }; return {}; })();\nsetTimeout(function () { result = [new Map().tag()]; });\n';
        const { code } = await deobfuscate(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).toContain("Map.prototype.tag");
    });
});

describe("cleanup: code in literal evals", () => {
    it('keeps the runtime that the code of eval("...") still reads, and only that', async () => {
        const input = 'function G() {}\nG.k = 41;\nG.unused = 1;\nsetTimeout(function () { result = [eval("G.k + 1")]; });\n';
        const { code } = await deobfuscate(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).toContain("G.k = 41;");
        expect(code).not.toContain("G.unused");
    });

    it("reads the code of eval even when more arguments follow it", async () => {
        const input = 'function G() {}\nG.k = 41;\nvar hits = 0;\nsetTimeout(function () { result = [eval("G.k + 1", hits++), hits]; });\n';
        const { code } = await deobfuscate(input);
        expect(observed(code)).toBe(observed(input));
        expect(code).toContain("G.k = 41;");
    });
});

describe("cleanup: dead stores", () => {
    it("drops locals only stored to and updated with primitives, and keeps any that something reads", async () => {
        const input =
            "function f(n) { var state = 576049076; var step = 0; var seen = 0; var minus = -5; state = 2; minus = -1007262805; step += 2; step++; seen += n; var kept = 1; kept += 2; var box = {}; box = 3; box++; return [n, kept]; }\nresult = f(4);\n";
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observed(code)).toBe(observed(input));
        for (const name of ["state", "step", "minus"]) expect(code).not.toContain(name);
        // `seen += n` adds a non-literal, `kept` is read, `box` held an object.
        for (const name of ["seen += n", "kept += 2", "box++"]) expect(code).toContain(name);
    });

    it("keeps unused locals a direct eval can see, and removes those it can't", async () => {
        const input = 'function f() { var seen = 1; return (function () { return eval("seen"); })(); }\nfunction g() { var unseen = 2; return 3; }\nresult = [f(), g()];\n';
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observed(code)).toBe(observed(input));
        expect(code).toContain("var seen = 1;");
        expect(code).not.toContain("unseen");
    });

    it("keeps what can throw: a BigInt update, a let in its dead zone, a read of a let before its declaration", async () => {
        const programs = [
            "function f() { var x = 1n; x += 1; } try { f(); result = ['ran']; } catch (e) { result = [e.name]; }",
            "function f() { var x = 0; x = -1n; x += 1; } try { f(); result = ['ran']; } catch (e) { result = [e.name]; }",
            "function f() { x = 1; let x = 2; } try { f(); result = ['ran']; } catch (e) { result = [e.name]; }",
            "function f() { var unused = x; let x = 1; } try { f(); result = ['ran']; } catch (e) { result = [e.name]; }",
        ];
        for (const input of programs) {
            const { code } = await deobfuscate(input, { passes: ["cleanup"] });
            expect(observed(code)).toBe(observed(input));
        }
    });
});
