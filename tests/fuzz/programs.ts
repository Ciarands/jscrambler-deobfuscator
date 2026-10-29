import { runInNewContext } from "node:vm";

/**
 * Random structured programs and a reference flattener that turns them into jscrambler-style switch machines.
 *
 * Programs only call `T(id)` (record a trace step), `Tg` (the same, as a template tag) and `C()` (read the next input
 * bit), so running a program on the same inputs before and after a transformation and comparing traces checks that
 * control flow is unchanged. Half of them run in strict mode, where a lost `var` throws instead of making a global.
 */

export type Stmt =
    | { k: "T"; id: number }
    | { k: "if"; yes: Stmt[]; no: Stmt[] }
    | { k: "while"; label: string | null; body: Stmt[] }
    | { k: "doWhile"; label: string | null; body: Stmt[] }
    /** `for (;;) { body }`: only left through break/return/throw. */
    | { k: "forever"; label: string | null; body: Stmt[] }
    | { k: "break"; label: string | null }
    | { k: "continue"; label: string | null }
    | { k: "return" }
    | { k: "throw" }
    /** At least one of `handler` and `finalizer`. Jumps inside may leave it. */
    | { k: "try"; body: Stmt[]; handler: Stmt[] | null; finalizer: Stmt[] | null }
    /** Closures over a `let` loop counter, made and called in place: each must see its own iteration's counter. */
    | { k: "closures"; id: number }
    /** `var name;` in unreachable code (after a jump): the only declaration of `name`. */
    | { k: "deadVar"; name: string }
    /** `T(name = id)`, for a `deadVar` earlier in the function. */
    | { k: "setVar"; name: string; id: number }
    /** `function name() {...}` in unreachable code, called from earlier in the same block. */
    | { k: "deadFn"; name: string; id: number }
    | { k: "callFn"; name: string };

export interface Program {
    readonly strict: boolean;
    readonly body: Stmt[];
}

export type Rng = () => number;

export const mulberry32 = (seed: number): Rng => {
    let a = seed | 0;
    return () => {
        a = (a + 0x6d2b79f5) | 0;
        let t = Math.imul(a ^ (a >>> 15), 1 | a);
        t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
        return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
    };
};

interface GenState {
    rng: Rng;
    nextId: number;
    nextLabel: number;
    nextName: number;
    /** `deadVar` names declared so far, in source order: later statements may assign them. */
    vars: string[];
}

interface Loops {
    /** Labels of enclosing loops, innermost last. `null` entries are unlabeled loops. */
    readonly labels: readonly (string | null)[];
    /** Inside a loop, so `break`/`continue` have a target. */
    readonly inLoop: boolean;
}

const pick = <T>(rng: Rng, items: readonly T[]): T => items[Math.floor(rng() * items.length)] as T;

const isJump = (s: Stmt): boolean => s.k === "break" || s.k === "continue" || s.k === "return" || s.k === "throw";

/** Unreachable declarations after the jump that ends `out`; a dead function gets a call earlier in the same block. */
const addDeadCode = (g: GenState, out: Stmt[]): void => {
    if (g.rng() < 0.35) {
        const name = `v${g.nextName++}`;
        out.push({ k: "deadVar", name });
        g.vars.push(name);
    }
    if (g.rng() < 0.3) {
        const name = `h${g.nextName++}`;
        out.push({ k: "deadFn", name, id: g.nextId++ });
        // Before the jump (the jump is at `length - 2` now, or earlier if a var was added).
        const jump = out.findIndex(isJump);
        out.splice(Math.floor(g.rng() * (jump + 1)), 0, { k: "callFn", name });
    }
};

const genSeq = (g: GenState, depth: number, loops: Loops, mustExit = false): Stmt[] => {
    const n = 1 + Math.floor(g.rng() * 3);
    const out: Stmt[] = [];
    for (let i = 0; i < n; i++) {
        const s = genStmt(g, depth, loops);
        out.push(s);
        if (isJump(s)) {
            addDeadCode(g, out);
            return out;
        }
    }
    // A forever loop body needs a way out, or the program never ends.
    if (mustExit)
        out.push({
            k: "if",
            yes: [
                { k: "T", id: g.nextId++ },
                { k: "break", label: null },
            ],
            no: [],
        });
    return out;
};

const genStmt = (g: GenState, depth: number, loops: Loops): Stmt => {
    const r = g.rng();
    if (depth <= 0 || r < 0.24) return { k: "T", id: g.nextId++ };
    if (r < 0.44) return { k: "if", yes: genSeq(g, depth - 1, loops), no: g.rng() < 0.6 ? genSeq(g, depth - 1, loops) : [] };
    if (r < 0.62) {
        const label = g.rng() < 0.3 ? `L${g.nextLabel++}` : null;
        const inner: Loops = { labels: [...loops.labels, label], inLoop: true };
        const kind = pick(g.rng, ["while", "while", "doWhile", "forever"] as const);
        // Every iteration records a step, so a loop that never ends shows up as trace overflow, not a hang.
        return { k: kind, label, body: [{ k: "T", id: g.nextId++ }, ...genSeq(g, depth - 1, inner, kind === "forever")] };
    }
    if (r < 0.7) {
        const handler = g.rng() < 0.75 ? genSeq(g, depth - 1, loops) : null;
        const finalizer = handler === null || g.rng() < 0.3 ? genSeq(g, depth - 1, loops) : null;
        return { k: "try", body: genSeq(g, depth - 1, loops), handler, finalizer };
    }
    if (loops.inLoop && r < 0.82) {
        const labeled = loops.labels.filter((l): l is string => l !== null);
        const label = labeled.length > 0 && g.rng() < 0.4 ? pick(g.rng, labeled) : null;
        return { k: g.rng() < 0.6 ? "break" : "continue", label };
    }
    if (r < 0.86) return { k: "return" };
    if (r < 0.89) return { k: "throw" };
    if (r < 0.93 && g.vars.length > 0) return { k: "setVar", name: pick(g.rng, g.vars), id: g.nextId++ };
    if (r < 0.96) return { k: "closures", id: g.nextId++ };
    return { k: "T", id: g.nextId++ };
};

export const generate = (seed: number, depth = 4): Program => {
    const g: GenState = { rng: mulberry32(seed), nextId: 0, nextLabel: 0, nextName: 0, vars: [] };
    const strict = g.rng() < 0.5;
    return { strict, body: genSeq(g, depth, { labels: [], inLoop: false }) };
};

const closures = (id: number): string => `{ const cl = []; for (let i = 0; i < 2; i++) cl.push(() => T("${id}." + i)); for (const c of cl) c(); }`;

/** Code for statements that are the same structured and flattened. */
const leaf = (s: Stmt): string | undefined => {
    switch (s.k) {
        case "T":
            return `T(${s.id});`;
        case "return":
            return `return T("r");`;
        case "throw":
            return `throw T("x");`;
        case "closures":
            return closures(s.id);
        case "deadVar":
            return `var ${s.name};`;
        case "setVar":
            return `T(${s.name} = ${s.id});`;
        case "deadFn":
            return `function ${s.name}() { return T(${s.id}); }`;
        case "callFn":
            return `${s.name}();`;
        default:
            return undefined;
    }
};

/** Plain JS for statements. Each loop test calls C(). */
export const emitStatements = (seq: readonly Stmt[], indent = "  "): string => {
    const inner = (body: readonly Stmt[]): string => emitStatements(body, `${indent}  `);
    return seq
        .map((s): string => {
            const label = (s.k === "while" || s.k === "doWhile" || s.k === "forever") && s.label !== null ? `${s.label}: ` : "";
            switch (s.k) {
                case "if":
                    return `${indent}if (C()) {\n${inner(s.yes)}\n${indent}}${s.no.length ? ` else {\n${inner(s.no)}\n${indent}}` : ""}`;
                case "while":
                    return `${indent}${label}while (C()) {\n${inner(s.body)}\n${indent}}`;
                case "doWhile":
                    return `${indent}${label}do {\n${inner(s.body)}\n${indent}} while (C());`;
                case "forever":
                    return `${indent}${label}for (;;) {\n${inner(s.body)}\n${indent}}`;
                case "break":
                    return `${indent}break${s.label ? ` ${s.label}` : ""};`;
                case "continue":
                    return `${indent}continue${s.label ? ` ${s.label}` : ""};`;
                case "try": {
                    const handler = s.handler === null ? "" : ` catch (e) {\n${inner(s.handler)}\n${indent}}`;
                    const finalizer = s.finalizer === null ? "" : ` finally {\n${inner(s.finalizer)}\n${indent}}`;
                    return `${indent}try {\n${inner(s.body)}\n${indent}}${handler}${finalizer}`;
                }
                default:
                    return `${indent}${leaf(s)}`;
            }
        })
        .join("\n");
};

/** Plain JS for a program: the body of `function f`. */
export const emit = (program: Program): string => `${program.strict ? '"use strict";\n' : ""}${emitStatements(program.body)}`;

/** Next state: a state id, or `[a, b]` for `C() ? a : b` (nested for `if / else if`). */
type Next = number | [Next, Next];

/** One piece of a case body: a step expression (`T(3)`, mergeable with the transition), or a whole statement. */
type Piece = { readonly step: string } | { readonly code: string };

interface FlatBlock {
    readonly body: Piece[];
    /** Where control goes: a next state, or a statement that leaves (return/throw), maybe with dead code after it. */
    readonly exit: { readonly next: Next } | { readonly end: string; readonly after: readonly string[] };
}

interface LoopTargets {
    readonly label: string | null;
    readonly breakTo: number;
    readonly continueTo: number;
}

/** The loop a `break`/`continue` with this label (or none: innermost) targets. */
const loopFor = (loops: readonly LoopTargets[], label: string | null): LoopTargets => {
    const found = label === null ? loops.at(-1) : loops.toReversed().find((l) => l.label === label);
    if (found === undefined) throw new Error(`no loop for ${label}`);
    return found;
};

/** Whether a `break`/`continue` in `body` leaves it: unlabeled outside any loop of `body`, or to a label not in it. */
const leaves = (body: readonly Stmt[], labels: readonly string[] = [], loopDepth = 0): boolean =>
    body.some((s) => {
        if (s.k === "break" || s.k === "continue") return s.label === null ? loopDepth === 0 : !labels.includes(s.label);
        if (s.k === "if") return leaves(s.yes, labels, loopDepth) || leaves(s.no, labels, loopDepth);
        if (s.k === "while" || s.k === "doWhile" || s.k === "forever") return leaves(s.body, s.label === null ? labels : [...labels, s.label], loopDepth + 1);
        if (s.k === "try") return [s.body, s.handler ?? [], s.finalizer ?? []].some((part) => leaves(part, labels, loopDepth));
        return false;
    });

/** Whether `body` holds a `try` that a `break`/`continue` leaves: such a try can't become nested machines. */
const hasEscapedTry = (body: readonly Stmt[]): boolean =>
    body.some((s) => {
        if (s.k === "if") return hasEscapedTry(s.yes) || hasEscapedTry(s.no);
        if (s.k === "while" || s.k === "doWhile" || s.k === "forever") return hasEscapedTry(s.body);
        if (s.k === "try") return [s.body, s.handler ?? [], s.finalizer ?? []].some((part) => leaves(part) || hasEscapedTry(part));
        return false;
    });

/** Fisher-Yates. */
const shuffle = <T>(items: readonly T[], rng: Rng): T[] => {
    const out = [...items];
    for (let i = out.length - 1; i > 0; i--) {
        const j = Math.floor(rng() * (i + 1));
        [out[i], out[j]] = [out[j] as T, out[i] as T];
    }
    return out;
};

/** How a machine sets its initial state and what its loop's init clause holds. */
type InitStyle = "sibling" | "loop" | "loopExtra" | "separate" | "lexical";

/**
 * Flatten statements the way jscrambler does: one `for (; S !== 0;) switch (S)` machine, with blocks in shuffled case
 * order. Exiting the machine is state 0. A `try` stays whole inside one case, its parts flattened into nested machines
 * with their own state variables; a loop holding a try that a `break`/`continue` leaves stays structured in one case.
 * Code after a jump lands in unreachable cases, or after the `return`/`throw` in the same case.
 */
const flattenStatements = (seq: readonly Stmt[], rng: Rng, names: { next: number }): string => {
    const machine = names.next++;
    const stateVar = machine === 0 ? "s" : `s${machine}`;
    // Machine style, picked per machine like jscrambler's output varies between samples.
    const inSlot = rng() < 0.25; // state kept in an `arguments`-style slot: a[4]
    const init: InitStyle = inSlot ? "sibling" : pick(rng, ["sibling", "sibling", "loop", "loopExtra", "separate", "lexical"] as const);
    // `sx` is 0 and case bodies read it: losing its declaration or its value makes them throw or trace differently.
    const extra = init === "loopExtra" || init === "separate" || init === "lexical" ? `${stateVar}x` : undefined;
    const reversed = rng() < 0.3; // 0 !== s

    const blocks = new Map<number, FlatBlock>();
    let nextId = 1;
    const add = (block: FlatBlock): number => {
        const id = nextId++;
        blocks.set(id, block);
        return id;
    };
    const reserve = (): number => nextId++;

    const step = (id: number): Piece => {
        const value = extra === undefined ? String(id) : `${extra} + ${id}`;
        const roll = rng();
        // Through a nested function whose parameter reuses the state's name, like minified code does: that `s` is a
        // different variable, so the machine must still be unflattened.
        if (roll < 0.12) return { step: `T((function (${stateVar}) { return ${stateVar}; })(${value}))` };
        // A closure reading the loop's (possibly lexical) init variable.
        if (extra !== undefined && roll < 0.24) return { step: `T((() => ${value})())` };
        if (roll < 0.32) return { step: `Tg\`a\${${value}}b\`` };
        return { step: `T(${value})` };
    };

    const cSeq = (body: readonly Stmt[], next: number, loops: readonly LoopTargets[]): number => {
        const jump = body.findIndex(isJump);
        const live = jump === -1 ? body : body.slice(0, jump + 1);
        const dead = jump === -1 ? [] : body.slice(jump + 1);
        const last = live.at(-1);
        let current = next;
        let from = live.length - 1;
        if (dead.length > 0 && (last?.k === "return" || last?.k === "throw") && rng() < 0.5) {
            // Dead declarations right after the return/throw, in the same case.
            current = add({ body: [], exit: { end: leaf(last) as string, after: dead.map((s) => leaf(s) as string) } });
            from--;
        } else if (dead.length > 0) {
            // Dead declarations in a case nothing jumps to.
            add({ body: dead.map((s) => ({ code: leaf(s) as string })), exit: { next } });
        }
        for (let i = from; i >= 0; i--) current = cStmt(live[i] as Stmt, current, loops);
        return current;
    };

    const cStmt = (s: Stmt, next: number, loops: readonly LoopTargets[]): number => {
        switch (s.k) {
            case "T":
                return add({ body: [step(s.id)], exit: { next } });
            case "setVar":
                return add({ body: [{ step: `T(${s.name} = ${s.id})` }], exit: { next } });
            case "callFn":
                return add({ body: [{ step: `${s.name}()` }], exit: { next } });
            case "closures":
            case "deadVar":
            case "deadFn":
                return add({ body: [{ code: leaf(s) as string }], exit: { next } });
            case "if": {
                // `if / else if` sometimes becomes one block with a nested conditional update: S = C() ? a : C() ? b : c.
                const elseIf = s.no.length === 1 && s.no[0]?.k === "if" ? s.no[0] : undefined;
                if (elseIf !== undefined && rng() < 0.5) {
                    return add({ body: [], exit: { next: [cSeq(s.yes, next, loops), [cSeq(elseIf.yes, next, loops), cSeq(elseIf.no, next, loops)]] } });
                }
                return add({ body: [], exit: { next: [cSeq(s.yes, next, loops), cSeq(s.no, next, loops)] } });
            }
            case "while":
            case "doWhile":
            case "forever": {
                // Kept whole: the outermost loop around a try that a jump leaves (it can't jump out of it, at top level).
                if (hasEscapedTry([s]) && !leaves([s])) return add({ body: [{ code: emitStatements([s], "") }], exit: { next } });
                // `head` is where `continue` goes: the test for while/do-while, the top of the body for forever.
                const head = reserve();
                const body = cSeq(s.body, head, [...loops, { label: s.label, breakTo: next, continueTo: head }]);
                // A forever loop's head is an empty block that just jumps into the body.
                blocks.set(head, { body: [], exit: { next: s.k === "forever" ? body : [body, next] } });
                // A do-while enters its body first.
                return s.k === "doWhile" ? body : head;
            }
            case "break":
                return loopFor(loops, s.label).breakTo;
            case "continue":
                return loopFor(loops, s.label).continueTo;
            case "return":
            case "throw":
                return add({ body: [], exit: { end: leaf(s) as string, after: [] } });
            case "try": {
                const part = (statements: readonly Stmt[]): string => `{\n${flattenStatements(statements, rng, names)}\n}`;
                const handler = s.handler === null ? "" : ` catch (${rng() < 0.5 ? "e" : `e${machine}`}) ${part(s.handler)}`;
                const finalizer = s.finalizer === null ? "" : ` finally ${part(s.finalizer)}`;
                return add({ body: [{ code: `try ${part(s.body)}${handler}${finalizer}` }], exit: { next } });
            }
        }
    };

    const entry = cSeq(seq, 0, []);
    const ids = shuffle([...blocks.keys()], rng);

    const state = inSlot ? `${stateVar}a[4]` : stateVar;
    const update = (n: Next): string => (typeof n === "number" ? String(n) : `C() ? ${update(n[0])} : ${update(n[1])}`);

    const cases = ids.map((id, index) => {
        const block = blocks.get(id) as FlatBlock;
        const lines = block.body.map((piece) => ("step" in piece ? `${piece.step};` : piece.code));
        const only = block.body.length === 1 ? block.body[0] : undefined;
        const single = only !== undefined && "step" in only ? only.step : undefined;
        const exit = block.exit;
        const roll = rng();
        if ("end" in exit) {
            lines.push(exit.end, ...exit.after);
        } else if (typeof exit.next === "number" && ids[index + 1] === exit.next && rng() < 0.5) {
            // The next case in source order is the target: fall through, no state change, no break.
        } else if (single !== undefined && roll < 0.3) {
            lines.splice(0, 1, `${single}, ${state} = ${update(exit.next)};`, "break;");
        } else if (single !== undefined && !inSlot && roll < 0.5) {
            // Minified: the transition is the last declarator of a `var`.
            lines.splice(0, 1, `var ${stateVar}v = ${single}, ${state} = ${update(exit.next)};`, "break;");
        } else {
            lines.push(`${state} = ${update(exit.next)};`, "break;");
        }
        return `case ${id}:\n${lines.join("\n")}`;
    });
    const test = reversed ? `0 !== ${state}` : `${state} !== 0`;
    const machineLoop = (head: string) => `for (${head}; ${test};) {\nswitch (${state}) {\n${cases.join("\n")}\n}\n}`;
    switch (init) {
        case "sibling":
            return `${inSlot ? `var ${stateVar}a = [];\n${state} = ${entry};` : `var ${state} = ${entry};`}\n${machineLoop("")}`;
        case "loop":
            return machineLoop(`var ${state} = ${entry}`);
        case "loopExtra":
            // for (var sx = 0, s = 2; ...): dropping the extra declarator makes the bodies throw.
            return machineLoop(`var ${extra} = 0, ${state} = ${entry}`);
        case "separate":
            // var s = 2; for (sx = 0; ...): an init that doesn't set the state runs before the machine.
            return `var ${extra};\nvar ${state} = ${entry};\n${machineLoop(`${extra} = 0`)}`;
        case "lexical":
            // for (let sx = 0; ...): one binding per iteration, captured by closures, never reassigned.
            return `var ${state} = ${entry};\n${machineLoop(`${rng() < 0.5 ? "let" : "const"} ${extra} = 0`)}`;
    }
};

/** Flatten a program: the body of `function f`. */
export const flatten = (program: Program, rng: Rng): string => `${program.strict ? '"use strict";\n' : ""}${flattenStatements(program.body, rng, { next: 0 })}`;

/** Run `function f() { <body> }` with `bits` as the C() inputs and return the trace. Bounded so loops terminate. */
export const runTrace = (body: string, bits: readonly boolean[]): string => {
    const trace: (string | number)[] = [];
    let i = 0;
    let fuel = 300;
    const T = (x: string | number) => {
        trace.push(x);
        if (trace.length > 2000) throw new Error("trace overflow");
        return x;
    };
    const Tg = (_strings: TemplateStringsArray, value: string | number) => T(value);
    const C = () => {
        const v = fuel-- > 0 && (bits[i++ % bits.length] ?? false);
        trace.push(v ? "?1" : "?0");
        if (trace.length > 2000) throw new Error("trace overflow");
        return v;
    };
    try {
        // Test-only: runs code generated by this file, never sample input. The timeout catches loops that never end.
        runInNewContext(`(function () {\n${body}\n})()`, { T, Tg, C }, { timeout: 1000 });
    } catch (error) {
        const message = typeof error === "object" && error !== null && "message" in error ? String(error.message) : String(error);
        trace.push(`EXC:${message}`);
    }
    return trace.join(",");
};
