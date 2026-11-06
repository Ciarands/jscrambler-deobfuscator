import { describe, expect, it } from "vitest";
import { deobfuscate } from "../src/index.js";
import { observe, type Run } from "./helpers.js";

// Both setup variants: aliases on the builtins, and storage getters handing out a function. Calls come static
// (`Owner.name.apply(Owner, args)`), as receiver dispatch (`r[name](...rest)`), or as receiver apply.
const PRELUDE = `
function G() {}
G[3] = (function () { return globalThis; })();
function S(g) {
  function def(owner, name, alias) {
    Object.defineProperty(owner, alias, { get: function () { return owner[name]; }, set: function (v) { owner[name] = v; }, enumerable: false, configurable: true });
  }
  function call(key, target, name, mode) {
    var holder = mode === "static" ? target : target.prototype;
    Object.defineProperty(G, key, { get: function () { return function () {
      var a = Array.prototype.slice.call(arguments);
      if (a.length === 0) return holder[name];
      if (mode === "static") return holder[name].apply(target, a);
      if (mode === "apply") return holder[name].apply(a[0], a.slice(1));
      var r = a[0] === null || a[0] === undefined ? target : a[0];
      return r[name].apply(r, a.slice(1));
    }; }, enumerable: false, configurable: true });
  }
  def(g, "String", "q1Str");
  def(String, "fromCharCode", "q2Fcc");
  def(String.prototype, "split", "q3Spl");
  def(Array.prototype, "join", "q4Joi");
  call("c1", String, "split", "dispatch");
  call("c2", String, "fromCharCode", "static");
  call("c3", g, "String", "static");
  call("c4", Array, "join", "dispatch");
  call("c5", String, "split", "apply");
}
S(G[3]);
`;

const PROGRAM = `${PRELUDE}
var out = [];
var custom = { split: function () { return ["own"]; } };
out.push(q1Str.q2Fcc(72, 105));
out.push("a%b".q3Spl("%").q4Joi("-"));
out.push(G.c1("x,y" + ",z", ",").length);
out.push(G.c1(custom, ",")[0], G.c5(custom, ",")[0]);
out.push(G.c2(65));
out.push(G.c3(5) + "!");
out.push(G.c4() === Array.prototype.join);
function local(String) { return q1Str; }
out.push(local(1) === String);
result = out;
`;

describe("aliases", () => {
    it("replaces every alias style with the builtin call it makes, and keeps behaviour", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["runtime", "global-proxy", "aliases"] });
        expect(code).toContain("out.push(String.fromCharCode(72, 105));");
        expect(code).toContain(`out.push("a%b".split("%").join("-"));`);
        // Dispatch on the receiver: a method call on it. Apply on the receiver: the builtin, called with it as this.
        expect(code).toContain(`out.push(("x,y" + ",z").split(",").length);`);
        expect(code).toContain(`out.push(custom.split(",")[0], String.prototype.split.call(custom, ",")[0]);`);
        expect(code).toContain("out.push(String.fromCharCode(65));");
        expect(code).toContain(`out.push(String(5) + "!");`);
        expect(code).toContain("out.push(Array.prototype.join === Array.prototype.join);");
        expect(observe(code)).toBe(observe(PROGRAM));
    });

    it("keeps an alias where the builtin's name is shadowed", async () => {
        const { code } = await deobfuscate(PROGRAM, { passes: ["runtime", "global-proxy", "aliases"] });
        expect(code).toContain("return q1Str;");
    });
});

// The same setup also forwards globals to host objects the builtins lack (a page's `document`, here `hostDoc`).
const withHost = (
    later: string
) => `${PRELUDE.replace("S(G[3]);", 'S(G[3]);\n(function (g) { Object.defineProperty(g, "q6Hd", { get: function () { return typeof g.hostDoc == "undefined" ? undefined : g.hostDoc; }, set: function (v) { g.hostDoc = v; }, configurable: true }); })(G[3]);')}
setTimeout(function () { ${later} });
`;

/** Model 10: the page has the host objects the script uses. */
const PAGE: Run = { globals: () => ({ hostDoc: { title: "page" } }), timers: true };

/** `q7Un`, an accessor of the global `target`, read after the global `holder` got a value. */
const withAliasOf = (target: string) =>
    withHost("holder = 5; result = [q7Un, typeof q7Un];").replace(
        "S(G[3]);",
        `S(G[3]);\nvar holder = false;\n(function (g) { Object.defineProperty(g, "q7Un", { get: function () { return g.${target} || undefined; }, set: function (v) { g.${target} = v; }, configurable: true }); })(G[3]);`
    );

describe("aliases: host objects", () => {
    it("reads, writes and calls the host object by its own name, and the setup goes", async () => {
        const program = withHost('var seen = [typeof q6Hd, q6Hd.title]; q6Hd = { title: "new" }; seen.push(hostDoc.title, q6Hd.title); result = seen;');
        const { code } = await deobfuscate(program);
        expect(code).not.toContain("q6Hd");
        expect(code).toContain("hostDoc.title");
        expect(observe(code, PAGE)).toBe(observe(program, PAGE));
    });

    it("reads the host object through the global object's names", async () => {
        const program = withHost("result = [globalThis.q6Hd.title, window.q6Hd.title];");
        const { code } = await deobfuscate(program);
        expect(code).not.toContain("q6Hd");
        expect(code).toContain("result = [globalThis.hostDoc.title, window.hostDoc.title];");
        const page: Run = { ...PAGE, window: true };
        expect(observe(code, page)).toBe(observe(program, page));
    });

    it("calls a host function without a this, as the alias did", async () => {
        const program = withHost("result = [q6Hd()];");
        const { code } = await deobfuscate(program);
        expect(code).toContain("result = [hostDoc()];");
        const run: Run = {
            globals: () => ({
                hostDoc: function (this: unknown) {
                    return this === undefined ? "no this" : "this";
                },
            }),
            timers: true,
        };
        expect(observe(code, run)).toBe(observe(program, run));
    });

    it("keeps an alias where the host's name is shadowed, and the setup with it", async () => {
        const program = withHost("var hostDoc = 1; result = [q6Hd.title, hostDoc];");
        const { code } = await deobfuscate(program);
        expect(code).toContain("q6Hd.title");
        expect(code).toContain('Object.defineProperty(g, "q6Hd"');
        expect(observe(code, PAGE)).toBe(observe(program, PAGE));
    });

    it("leaves accessors that read a host object without forwarding it", async () => {
        const accessors = [
            "get: function () { g.hostDoc; return undefined; }, set: function (v) { g.hostDoc = v; }", // reads, hands out nothing
            "get: function () { return g.hostDoc; }, set: function (v) {}", // doesn't write
        ];
        for (const accessor of accessors) {
            const program = withHost('q6Hd = { title: "new" }; result = [typeof q6Hd, typeof hostDoc];').replace(
                /get: function \(\) \{ return typeof g\.hostDoc.*?set: function \(v\) \{ g\.hostDoc = v; \}/,
                accessor
            );
            const { code } = await deobfuscate(program);
            expect(code).toContain("q6Hd");
            expect(observe(code, PAGE)).toBe(observe(program, PAGE));
        }
    });

    it("leaves accessors that look up no missing global: they may read state that changes later", async () => {
        for (const target of ["undefined", "holder"]) {
            const program = withAliasOf(target);
            const { code } = await deobfuscate(program);
            expect(code).toContain("q7Un");
            expect(observe(code, { timers: true })).toBe(observe(program, { timers: true }));
        }
    });

    it("leaves an alias the program deletes or names as a string", async () => {
        for (const later of ["delete q6Hd; result = [typeof q6Hd];", 'Object.defineProperty(globalThis, "q6Hd", { value: 1 }); result = [q6Hd];']) {
            const program = withHost(later);
            const { code } = await deobfuscate(program);
            expect(code).toContain("q6Hd");
            expect(observe(code, PAGE)).toBe(observe(program, PAGE));
        }
    });
});
