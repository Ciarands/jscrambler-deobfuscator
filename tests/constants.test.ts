import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

const RUN: Run = { window: true };

const simplified = async (code: string): Promise<string> => (await deobfuscate(code, { passes: ["simplify"] })).code;

/** A top-level string table whose decoder calls still run, in sequences. */
const TABLE = `var log = [];
var T;
T = [(log.push("built"), "get"), "set", , 3];
`;

describe("constant reads in recursive function declarations", () => {
    it("resolves a constant read inside a self-recursive declaration", async () => {
        const program = `var log = [];
var G = function () {
  var t = 3229;
  function w(n) {
    function z(k) {
      if (k > 0) z(k - 1);
      log.push(t + k);
    }
    z(n);
  }
  w(2);
  return log;
};
result = G();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(3229 + k);");
    });

    it("resolves reads in mutually recursive declarations entered after the definition", async () => {
        const program = `var log = [];
var G = function () {
  var t = 7;
  function even(k) { log.push(t); return k === 0 || odd(k - 1); }
  function odd(k) { log.push(-t); return k !== 0 && even(k - 1); }
  return [even(3), log];
};
result = G();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(7);");
        expect(output).toContain("log.push(-7);");
    });

    it("resolves reads in a declaration that comes before the definition but is only called after it", async () => {
        const program = `var G = function () {
  function read() { return t * 2; }
  function early() { return typeof u; }
  var before = early();
  var t = 21;
  var u = 1;
  return [read(), before, early()];
};
result = G();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("return 42;");
        expect(output).toContain("return typeof u;");
        // A definition inside the declaration itself: its earlier reads run first in each call.
        const inside = `var F = function () {\n  var k;\n  function g() {\n    var r = typeof k;\n    k = 5;\n    return r;\n  }\n  return [g(), g()];\n};\nresult = F();\n`;
        const kept = await simplified(inside);
        expect(observe(kept, RUN)).toBe(observe(inside, RUN));
        expect(kept).toContain("var r = typeof k;");
    });

    it("refuses when a cycle member is called before the definition", async () => {
        const program = `var log = [];
var G = function () {
  z(1);
  var t = 5;
  function z(k) {
    if (k > 0) z(k - 1);
    log.push(t);
  }
  z(1);
  return log;
};
result = G();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(t);");
    });

    it("keeps nothing it assumed while a failed check ran", async () => {
        // Checking x assumes x runs late while it looks at y (called from x): y is fine under that assumption, but
        // x also runs from w, which runs before t is set. y must not keep the verdict it got under the assumption.
        const program = `var G = function () {
  var log = [];
  w();
  var t = 5;
  function x(k) { log.push(t); if (k) y(k - 1); }
  function y(k) { log.push(t + 1); x(k); }
  function w() { x(1); }
  x(0);
  return log;
};
result = G();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(t);");
        expect(output).toContain("log.push(t + 1);");
    });
});

describe("constants declared in nested statement lists", () => {
    it("resolves reads after the declaration in the same block, catch body or case", async () => {
        const program = `var log = [];
function f(flag, mode) {
  if (flag) {
    var a = 2738;
    log.push(a);
    log.push(function () { return a + 1; }());
  }
  try { throw 0; } catch (e) {
    var b = "N";
    log.push(b + "x");
  }
  switch (mode) {
    case 1:
      var c = 5;
      log.push(c * 2);
  }
}
f(true, 1);
f(false, 2);
result = log;
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(2738);");
        expect(output).toContain("return 2739;");
        expect(output).toContain('log.push("Nx");');
        expect(output).toContain("log.push(10);");
    });

    it("keeps reads outside the declaring list, or before the declaration in a loop", async () => {
        const program = `var log = [];
function f(flag) {
  if (flag) {
    var a = 1;
  }
  log.push(a);
  for (var i = 0; i < 2; i++) {
    log.push(b);
    var b = 2;
  }
  switch (flag) {
    case true:
      var c = 3;
    case false:
      log.push(c);
  }
}
f(false);
f(true);
result = log;
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("log.push(a);");
        expect(output).toContain("log.push(b);");
        expect(output).toContain("log.push(c);");
    });
});

describe("constants written once after a bare declaration", () => {
    it("resolves reads after the only write, not before it or outside the write's statement list", async () => {
        const program = `function f(c) {
  var a;
  var log = [typeof a];
  a = "k";
  log.push(a, a.length);
  if (c) {
    var b;
    b = 3;
    log.push(b * 2);
  }
  log.push(typeof b);
  return log;
}
result = [f(true), f(false)];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("var log = [typeof a];");
        expect(output).toContain('log.push("k", 1);');
        expect(output).toContain("log.push(6);");
        expect(output).toContain("log.push(typeof b);");
    });

    it("keeps reads of a variable written by a statement that reads it, and reads between two writes", async () => {
        const program = `function f() {
  var n;
  n = typeof n;
  var m;
  m = 1;
  var first = m;
  m = 2;
  return [n, first, m];
}
result = f();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("var first = m;");
        expect(output).toContain("return [n, first, 2];");
    });
});

describe("constants written by several statements in one list", () => {
    it("resolves strings built in pieces, and reassigned ones, after the last write", async () => {
        const program = `function f(log) {
  var s = "ab";
  s += "cd";
  s += 1;
  var t = "";
  t = "A";
  t += "B";
  var u;
  u = "x";
  u += "y";
  var r = log.push(0);
  r += "x";
  r = "A";
  r += "B";
  var d = "";
  var d = "dis";
  d += "able";
  log.push(s, t, u, r, d);
  return log;
}
result = f([]);
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain('log.push("abcd1", "AB", "xy", "AB", "disable");');
    });

    it("keeps reads before the last write, in closures made before it and in declarations called before it", async () => {
        const program = `function f() {
  var log = [];
  var s = "a";
  function early() { return s; }
  log.push(early(), s);
  var later = () => s;
  s += "b";
  log.push(s, later());
  return log;
}
result = f();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("return s;");
        expect(output).toContain("log.push(early(), s);");
        expect(output).toContain("var later = () => s;");
        expect(output).toContain('log.push("ab", later());');
    });

    it("keeps reads of a variable also written in another statement list, by another operator, or appended to first", async () => {
        const program = `function f(c) {
  var s = "a";
  if (c) {
    s += "b";
  }
  var t = "a";
  for (var i = 0; i < 2; i++) t += "x";
  var u = "a";
  u -= 1;
  var v = "a";
  v += "b";
  v = v + "c";
  var out = [];
  for (var k = 0; k < 2; k++) {
    var w;
    w += "a";
    w += "b";
    out.push(w);
  }
  return [s, t, u, v, out];
}
result = [f(true), f(false)];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("return [s, t, u, v, out];");
        expect(output).toContain("out.push(w);");
    });
});

describe("constant arrays", () => {
    it("resolves reads through slot aliases, variable aliases and the array itself", async () => {
        const program = `${TABLE}function a() {
  var s = [arguments];
  s[4] = T;
  var A = T;
  function b() {
    result = [s[4][1], A[0], s[4].length, A[2], T[3], log];
  }
  b();
}
a();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`result = ["set", "get", 4, undefined, 3, log];`);
        expect(output).toContain(`T = [(log.push("built"), "get"), "set", , 3];`);
    });

    it("resolves reads through an alias assigned once after a bare declaration, in its statement list", async () => {
        const program = `${TABLE}function a(c) {
  var A;
  A = T;
  return [A[1], A.length, b(c)];
}
function b(c) {
  var B;
  if (c) {
    B = T;
    return B[0];
  }
  return "none";
}
result = [a(true), a(false)];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`return ["set", 4, b(c)];`);
        expect(output).toContain(`return "get";`);
    });

    it("resolves reads of a function-local array", async () => {
        const program = `function f(i) {
  var L = ["x", "y", (i, "z")];
  var s = [arguments];
  s[1] = L;
  return [L[0], s[1][2]];
}
result = f(1);
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`return ["x", "z"];`);
    });

    it("allows reads with unknown keys whose value is only converted or tested", async () => {
        const program = `${TABLE}function a(i) {
  var s = [arguments];
  s[2] = T;
  var o = { get: 1, set: 2 };
  var used = [o[s[2][i]], typeof T[i], !T[i], T[i] === "set", T[i] + "!"];
  if (T[i]) used.push("tested");
  return [used, s[2][1]];
}
result = [a(0), a(1), a(7), a("length")];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`return [used, "set"];`);
    });

    it("keeps elements whose value doesn't evaluate, and reads out of bounds", async () => {
        const program = `var log = [];
var T = [(log.push(1), log.length > 0 ? "a" : "b"), "c"];
result = [T[0], T[1], T[2]];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`result = [T[0], "c", T[2]];`);
    });

    it("refuses arrays that change, escape or are read before they are built", async () => {
        const reads = "result = [T[0], T[1], T.length];";
        const cases = {
            "element write": `T[1] = "z";\n${reads}`,
            "length write": `T.length = 1;\n${reads}`,
            delete: `delete T[0];\n${reads}`,
            push: `T.push("z");\n${reads}`,
            "method by computed key": `T["reverse"]();\n${reads}`,
            "passed to a function": `(function (t) { t[0] = "z"; })(T);\n${reads}`,
            stored: `var o = { t: T };\no.t[0] = "z";\n${reads}`,
            "copy used as a value": `(function () {\n  var A;\n  var B = (A = T);\n  B[0] = "z";\n})();\n${reads}`,
            "copy in a parameter": `(function (p) { p = T; arguments[0][0] = "z"; })(0);\n${reads}`,
            "copy written through": `var A = T;\nA[0] = "z";\n${reads}`,
            spread: `result = [...T, T[0]];`,
            "unknown-key read stored": `var k = String.fromCharCode(48);\nvar e = T[k];\n${reads}`,
            "unknown-key read passed": `var k = String.fromCharCode(48);\nresult = [JSON.stringify(T[k]), T[0]];`,
            "unknown-key read called": `var k = "concat";\nresult = [T[k]().length, T[0]];`,
            "read before it is built": `try { result = T[0]; } catch (e) { result = "threw"; }`,
            "globalThis property": `globalThis.T[0] = "z";\n${reads}`,
            "window property by name": `window["T"][0] = "z";\n${reads}`,
            "window property by unknown key": `window[String.fromCharCode(84)][0] = "z";\n${reads}`,
            "top-level this": `this[String.fromCharCode(84)][0] = "z";\n${reads}`,
        };
        for (const [name, code] of Object.entries(cases)) {
            const program = name === "read before it is built" ? `${code}\nvar T = ["get", "set"];\n` : `var T = ["get", "set"];\n${code}\n`;
            const output = await simplified(program);
            expect(observe(output, RUN), name).toBe(observe(program, RUN));
            expect(output, name).toContain("T[0]");
        }
    });

    it("refuses calls of elements, which get the array as this", async () => {
        const program = `var T = [function () { this[1] = "z"; }, "set"];
T[0]();
result = T[1];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("result = T[1];");
    });

    it("refuses arrays built with a spread, whose indices aren't known", async () => {
        const program = `var S = ["a", "c"];
var T = [...S, "b"];
result = T[1];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("result = T[1];");
    });

    it("refuses script-global constants reachable as properties of the global object", async () => {
        const program = `var c = 5;
var d = 6;
window.c = 7;
window[String.fromCharCode(100)] = 8;
result = [c, d];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain("result = [c, d];");
    });

    it("takes a global-object key read from a constant array for one of its elements, whatever the index", async () => {
        // `window[T[k]]` reaches `x` or `undefined`, never `T` itself: T stays constant.
        const safe = `var T = ["x", "beta"];\nvar x = 5;\nfunction pick(k) { return window[T[k]]; }\nresult = [pick(0), pick(7), T[1]];\n`;
        const output = await simplified(safe);
        expect(observe(output, RUN)).toBe(observe(safe, RUN));
        expect(output).toContain('result = [pick(0), pick(7), "beta"];');
        // An element naming the array reaches it (spelled in two parts: no literal says its name).
        const named = `var TU = ["T" + "U", "beta"];\nfunction pick(k) { return window[TU[k]]; }\npick(0)[1] = "changed";\nresult = [TU[1]];\n`;
        const kept = await simplified(named);
        expect(observe(kept, RUN)).toBe(observe(named, RUN));
        expect(kept).toContain("result = [TU[1]];");
    });

    it("refuses reads through a slot written twice, but not the array's own reads", async () => {
        const program = `var T = ["get", "set"];
var U = ["put", "post"];
function a(flag) {
  var s = [arguments];
  s[4] = T;
  if (flag) s[4] = U;
  return [s[4][0], T[0]];
}
result = [a(false), a(true)];
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`return [s[4][0], "get"];`);
    });

    it("refuses reads before the copy into a slot", async () => {
        const program = `var T = ["get", "set"];
function a() {
  var s = [arguments];
  function early() { try { return s[4][0]; } catch (e) { return "unset"; } }
  var before = early();
  s[4] = T;
  return [before, s[4][1]];
}
result = a();
`;
        const output = await simplified(program);
        expect(observe(output, RUN)).toBe(observe(program, RUN));
        expect(output).toContain(`s[4][0]`);
        expect(output).toContain(`return [before, "set"];`);
    });
});
