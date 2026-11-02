import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

// Miniature runtime: a decoder whose stage calls shuffle the table until a non-stage call freezes it, a wrapper, and
// stage calls inside an opaque predicate.
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

const RUN: Run = { globals: () => ({ host: { side: () => 1 } }), timers: true };

describe("cleanup", () => {
    it("removes the runtime once nothing uses it, and unused locals with pure initializers", async () => {
        const program = `${RUNTIME}f(host);\nresult = out;\n`;
        const { code } = await deobfuscate(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).not.toMatch(/\bG\b/);
        expect(code).not.toContain("unused");
        expect(code).toContain("var kept = host.side();");
        expect(code).toContain(`out.push("b", "c");`);
    });

    it("keeps the runtime when the storage object escapes", async () => {
        const program = `${RUNTIME}f(host);\nhost.exported = G;\nresult = out;\n`;
        const { code } = await deobfuscate(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toContain("function G() {}");
        expect(code).toContain("G.D = ");
    });

    it("removes stores of the runtime as a global the program never names, and keeps one it reads back", async () => {
        // Also a definition made through the store: `(globalThis.P = G).k = v`.
        const program = `${RUNTIME}globalThis.Kept = G;\n(globalThis.Chained = G).x = function () { return G.D; };\nf(host);\nresult = out;\n`;
        const { code } = await deobfuscate(program);
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).not.toMatch(/\bG\b|Kept|Chained/);
        for (const [store, name] of [
            ["globalThis.Kept = G;", "Kept"],
            ["(globalThis.Chained = G).x = function () { return 1; };", "Chained"],
        ]) {
            const readBack = `${RUNTIME}${store}\nf(host);\nresult = [out, typeof globalThis.${name}];\n`;
            const kept = await deobfuscate(readBack);
            expect(observe(kept.code, RUN)).toBe(observe(readBack, RUN));
        }
    });
});

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
            `function f() { var s = G, x = 1; return [s.k, x]; }`,
        ];
        for (const body of bodies) {
            const program = withAliases(body);
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observe(code, RUN)).toBe(observe(program, RUN));
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
            // A sloppy block function binds `G` throughout the inner function (Annex B).
            annexB: "function f() { var s = G; return (function () { var k = s.k; { function G() {} } return k; })(); }",
            insideWith: "function f(o) { var s = G; with (o) { return s.k; } }",
            shorthand: "function f() { var s = G; return Object.keys({ s }); }",
        };
        for (const [name, body] of Object.entries(cases)) {
            const program = withAliases(body);
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observe(code, RUN), name).toBe(observe(program, RUN));
            expect(code, name).toMatch(/\b[st] = /);
        }
    });

    it("keeps every alias when the storage function is reassigned", async () => {
        const program = withAliases(`function f() { var s = G; G = { k: "other" }; return s.k; }`);
        const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
        expect(observe(code, RUN)).toBe(observe(program, RUN));
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
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).not.toContain("G.k");
    });

    it("doesn't take a statement split in parts for pure part by part", async () => {
        // Together the parts change nothing outside G; alone, the first one does, and the second depends on it.
        const input = withBranch("G.k = put(); G.v = take();");
        const code = await rewrite(input);
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).toContain("G.k = put();");
    });
});

// A builder whose method the prelude calls directly and through a wrapper (whose receiver is `receiver`). Later code
// reads what such a call may change outside the builder's state, but never `G.k`.
const withStage = ({ method = "n += x;", builder = "", holder = "{ m: m }", before = "", receiver = "G.k" } = {}) => `
(function () {
  function G() {}
  var A = (function () { return arguments; })(0);
  var box = { f: function (x) { box.v = x; } };
  G.j = {};
  G.k = (function () {
    var n = 0, T = [];
    var m = function (x) { ${method} return n; };
    ${builder}
    return ${holder};
  })();
  G.w = function () { return typeof G.k.m === "function" ? G.k.m.apply(${receiver}, arguments) : G.k.m; };
  ${before}
  G.k.m(3);
  G.w(4);
  setTimeout(function () { result = [A[0], box.v, box.state && box.state.length, G.extra, G.j.v, typeof leaked, String.marked]; });
})();
`;

describe("cleanup: stage calls", () => {
    it("removes stage calls whose function changes only its builder's state", async () => {
        for (const method of ["n += x;", "T.push(x); n = T.length;"]) {
            const program = withStage({ method });
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observe(code, RUN), method).toBe(observe(program, RUN));
            expect(code, method).not.toMatch(/G\.k|G\.w/);
        }
    });

    it("keeps stage calls that may change more than their builder's state", async () => {
        const cases = {
            global: { method: "leaked = x;" },
            storageKey: { method: "G.extra = x;" },
            builtin: { method: "String.marked = x;" },
            argumentsObject: { method: "A[0] = x;" },
            outerObject: { method: "box.v = x;" },
            // The builder hands its state out.
            leakedState: { method: "T.push(x);", builder: "box.state = T;" },
            methodFromOutside: { holder: "{ m: box.f }" },
            // Code that stays replaces what the builder made before the calls.
            replacedHolder: { before: "(function () { G.k = { m: box.f }; })();" },
            rebound: { before: "(function () { var o = function () {}; o.j = G.j; o.k = { m: box.f }; o.w = function (x) { o.k.m(x); }; G = o; })();" },
            // Called through the wrapper, `this` is another key's object.
            writesReceiver: { method: "this.v = x;", receiver: "G.j" },
            // The wrapper's `apply` is the method's own, which writes the wrapper's receiver.
            ownApply: { builder: "m.apply = function (self, args) { self.v = args[0]; };", receiver: "G.j" },
        };
        for (const [name, options] of Object.entries(cases)) {
            const program = withStage(options);
            const { code } = await deobfuscate(program, { passes: ["emulate", "cleanup"] });
            expect(observe(code, RUN), name).toBe(observe(program, RUN));
            expect(code, name).toContain("G.w(4);");
        }
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
        expect(observe(code, RUN)).toBe(observe(input, RUN));
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
            expect(observe(code, RUN)).toBe(observe(input, RUN));
            expect(code).toContain("globalThis.Hx = ");
        }
    });

    it("keeps a call that also changes or deletes a builtin", async () => {
        for (const setup of ['String.prototype.trim = function () { return "changed"; };', "delete String.prototype.trim;"]) {
            const input = withSetup('result = ["a,b".q1(","), typeof " x ".trim];', setup);
            const { code } = await deobfuscate(input);
            expect(observe(code, RUN)).toBe(observe(input, RUN));
            expect(code).toContain("String.prototype.trim");
        }
    });

    it("keeps a runtime definition that changes any builtin, not only the common ones", async () => {
        const input = 'function G() {}\nG.k = (function () { Map.prototype.tag = function () { return "tagged"; }; return {}; })();\nsetTimeout(function () { result = [new Map().tag()]; });\n';
        const { code } = await deobfuscate(input);
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).toContain("Map.prototype.tag");
    });
});

describe("cleanup: code in literal evals", () => {
    it('keeps the runtime that the code of eval("...") still reads, and only that', async () => {
        const input = 'function G() {}\nG.k = 41;\nG.unused = 1;\nsetTimeout(function () { result = [eval("G.k + 1")]; });\n';
        const { code } = await deobfuscate(input);
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).toContain("G.k = 41;");
        expect(code).not.toContain("G.unused");
    });

    it("reads the code of eval even when more arguments follow it", async () => {
        const input = 'function G() {}\nG.k = 41;\nvar hits = 0;\nsetTimeout(function () { result = [eval("G.k + 1", hits++), hits]; });\n';
        const { code } = await deobfuscate(input);
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).toContain("G.k = 41;");
    });
});

describe("cleanup: dead stores", () => {
    it("drops locals only stored to and updated with primitives, and keeps any that something reads", async () => {
        const input =
            "function f(n) { var state = 576049076; var step = 0; var seen = 0; var minus = -5; state = 2; minus = -1007262805; step += 2; step++; seen += n; var kept = 1; kept += 2; var box = {}; box = 3; box++; return [n, kept]; }\nresult = f(4);\n";
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        for (const name of ["state", "step", "minus"]) expect(code).not.toContain(name);
        // `seen += n` adds a non-literal, `kept` is read, `box` held an object.
        for (const name of ["seen += n", "kept += 2", "box++"]) expect(code).toContain(name);
    });

    it("counts a guarded store's branch stores with the `if` they go with", async () => {
        const input = "function f(n) { var last = 0; if (last === n) { last = 1; } else { last = 2; } return n; }\nresult = f(3);\n";
        const { code, report } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).not.toContain("last");
        // The `if` and the declarator.
        expect(report.passes.map((pass) => [pass.changed, pass.stats?.["locals"]])).toEqual([[2, 2]]);
    });

    it("drops locals only given the values of other bindings, unless they are updated or read from a let", async () => {
        const input =
            'var log = [];\nvar table = [1, 2];\nvar hooked = { valueOf: function () { log.push("converted"); return 1; } };\nfunction f(n) { var copy; copy = table; copy = n; copy = f; var bumped; bumped = hooked; bumped += 1; var added; added = 1; added += hooked; return n; }\nfunction g() { var late; late = later; let later = 2; }\ntry { g(); } catch (e) { log.push(e.name); }\nresult = [f(4), log];\n';
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(observe(input, RUN)).toBe('[4,["ReferenceError","converted","converted"]]');
        expect(code).not.toContain("copy");
    });

    it("drops a var declared several times that nothing reads, with its stores, and keeps one read, one with an impure value or a for-in head", async () => {
        const input =
            'var log = [];\nfunction f(o) { var a = ""; var a = "x"; var b = ""; b = ""; var b = "y"; var d = 1; var d; var kept = 1; var kept = 2; var called = o.side(); var called = 3; var k = 0; for (var k in o) log.push(k); return kept; }\nresult = [f({ side: function () { log.push("side"); return 1; } }), log];\n';
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).not.toMatch(/\b[abd]\b/);
        for (const kept of ["var kept = 2;", "var called = o.side();", "var k = 0;", "for (var k in o)"]) expect(code).toContain(kept);
    });

    it("drops a local read only by the tests of ifs that store to it, unless such a test can convert, call or throw", async () => {
        const input = [
            "var log = [];",
            'var hooked = { valueOf: function () { log.push("converted"); return 1; } };',
            'function side() { log.push("side"); return 5; }',
            "function f(n) {",
            "  var last = 0, kept = 0, loose = 0, called = 0, negated = 0, bumped = 0;",
            "  var position = n * 2;",
            "  if (last === position) {} else { last = position; }",
            "  if (!(last !== position) && true) last = 3;",
            "  if (kept !== position) { kept = position; }",
            "  if (loose == hooked) {} else { loose = 1; }",
            "  if (called === side()) { called = 1; }",
            "  if (-hooked === 1) { negated = 1; }",
            "  bumped = hooked;",
            "  if (n === 4) { bumped++; }",
            "  return kept;",
            "}",
            "function g() { var early = 0; if (early === later) { early = 1; } let later = 2; }",
            "try { g(); } catch (e) { log.push(e.name); }",
            "result = [f(4), log];",
        ].join("\n");
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).not.toContain("last");
        for (const kept of ["kept = position;", "loose == hooked", "called === side()", "-hooked === 1", "bumped++", "early === later"]) expect(code).toContain(kept);
    });

    it("drops a dead store of an object a builder function makes, not one whose builder calls, changes another object, sets through a prototype or can throw", async () => {
        const input = [
            "var log = [];",
            "var outer = {};",
            'var proto = { set k(v) { log.push("setter " + v); } };',
            "function f() {",
            "  var table, called, leaks, viaProto, argument, parameter, returned, kept;",
            '  table = [(() => { var o; o = {}; o.link = "a"; o["name"] = 1; return o; })()];',
            '  called = (() => { var o = {}; o.v = log.push("call"); return o; })();',
            "  leaks = (() => { var o = {}; outer.v = 1; return o; })();",
            "  viaProto = (() => { var o = { __proto__: proto }; o.k = 2; return o; })();",
            '  argument = (() => { var o = {}; return o; })(log.push("argument"));',
            '  parameter = ((p = log.push("default")) => { var o = {}; return o; })();',
            '  returned = (() => { var o = {}; return log.push("return"); })();',
            "  kept = (function () { var o = {}; o.a = 1; return o; })();",
            "  return kept;",
            "}",
            "function cyclic() { var made; made = (() => { var o = {}; o.__proto__ = o; return o; })(); }",
            "function cleared() { var made; made = (() => { var o = {}; o = null; o.k = 2; return o; })(); }",
            "for (const g of [cyclic, cleared]) { try { g(); log.push(g.name + ' ran'); } catch (e) { log.push(e.name); } }",
            "result = [f(), outer, log];",
        ].join("\n");
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).not.toContain("table");
        for (const kept of ['log.push("call")', "outer.v = 1;", "o.k = 2;", '"argument"', '"default"', '"return"', "o.__proto__ = o;", "o = null;"]) expect(code).toContain(kept);
    });

    it("drops a script global's dead table and declaration when only its name could reach it, not when the program spells it or may read the global object with an unknown key", async () => {
        const dead = 'var table;\ntable = ["a", "b"];\nfunction unusedHelper() { return 1; }\nresult = 2;\n';
        const { code } = await deobfuscate(dead, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(dead, RUN));
        expect(code).toBe("result = 2;\n");
        const reaches = [
            'result = "table";',
            'var key = host.side() ? "table" : "x";\nresult = typeof globalThis[key];',
            // `this` in a sloppy function called unbound is the global object.
            'function leak(p) { return typeof this[p + "ble"]; }\nresult = leak("ta");',
            // The global object handed on: to a parameter, or as `this` to a strict function.
            'function read(o, p) { return typeof o[p + "ble"]; }\nresult = read(globalThis, "ta");',
            'function strict(p) { "use strict"; return typeof this[p + "ble"]; }\nresult = strict.call(this, "ta");',
        ];
        for (const reach of reaches) {
            const program = `var table;\ntable = ["a", "b"];\n${reach}\n`;
            const kept = await deobfuscate(program, { passes: ["cleanup"] });
            expect(observe(kept.code, RUN)).toBe(observe(program, RUN));
            expect(kept.code).toContain('table = ["a", "b"];');
        }
    });

    it("drops a script global's dead table once the code handing the global object on is itself removed", async () => {
        const program = 'var table;\ntable = ["a", "b"];\nfunction unusedHelper() { return window; }\nresult = 2;\n';
        const { code } = await deobfuscate(program, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(program, RUN));
        expect(code).toBe("result = 2;\n");
    });

    it("keeps unused locals a direct eval can see, and removes those it can't", async () => {
        const input = 'function f() { var seen = 1; return (function () { return eval("seen"); })(); }\nfunction g() { var unseen = 2; return 3; }\nresult = [f(), g()];\n';
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(code).toContain("var seen = 1;");
        expect(code).not.toContain("unseen");
    });

    it("keeps a for-in binding nothing reads and a block function sloppy code sees outside its block", async () => {
        const input = "function f(o) { var n = 0; for (var k in o) n++; return n; }\nfunction g() { if (true) { function inner() {} } return typeof inner; }\nresult = [f({ a: 1, b: 2 }), g()];\n";
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        expect(observe(input, RUN)).toBe('[2,"function"]');
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
            expect(observe(code, RUN)).toBe(observe(input, RUN));
        }
    });

    it("merges a var whose literal value another literal replaces right away, not one any other value replaces", async () => {
        const input =
            'function read() { return g; } var a = ""; var a = "keyCode"; var b = ""; b = "href"; var e = "", e = "done", f = 1, f; var g = "old", g = read(); var h = 0; h = 0; result = [a, b, e, f, g, h];';
        const { code } = await deobfuscate(input, { passes: ["cleanup"] });
        expect(observe(code, RUN)).toBe(observe(input, RUN));
        // `read()` sees the first value of `g`.
        expect(code).toContain('var a = "keyCode";\nvar b = "href";\nvar e = "done", f = 1, f;\nvar g = "old", g = read();\nvar h = 0;\nresult');
    });
});
