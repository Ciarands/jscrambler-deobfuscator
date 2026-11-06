import { visitorKeys } from "oxc-parser";
import type { Node } from "./ast.js";
import { isFunctionNode } from "./ast.js";
import { spliceList } from "./list.js";

type Container = Record<string, unknown>;

const fields = (node: Node): Container => node as unknown as Container;

interface Cursor {
    index: number;
}

const RESET = Symbol("reset");

export class Path<N extends Node = Node> {
    node: N;
    #parentPath: Path | null;
    #key: string | null;
    #cursor: Cursor | null;
    #removed = false;
    #skipped = false;

    constructor(node: N, parentPath: Path | null, key: string | null, cursor: Cursor | null) {
        this.node = node;
        this.#parentPath = parentPath;
        this.#key = key;
        this.#cursor = cursor;
    }

    [RESET](node: N, parentPath: Path | null, key: string | null, cursor: Cursor | null): this {
        this.node = node;
        this.#parentPath = parentPath;
        this.#key = key;
        this.#cursor = cursor;
        this.#removed = false;
        this.#skipped = false;
        return this;
    }

    get parent(): Node | null {
        return this.#parentPath === null ? null : this.#parentPath.node;
    }

    get parentPath(): Path | null {
        return this.#parentPath;
    }

    get key(): string | null {
        return this.#key;
    }

    get index(): number | null {
        return this.#cursor?.index ?? null;
    }

    get removed(): boolean {
        return this.#removed;
    }

    get skipped(): boolean {
        return this.#skipped;
    }

    skip(): void {
        this.#skipped = true;
    }

    #list(): Node[] | null {
        if (this.parent === null || this.key === null || this.#cursor === null) return null;
        return fields(this.parent)[this.key] as Node[];
    }

    /** The walker continues into the new node's children; its enter visitor is not called again. */
    replace(node: Node): void {
        if (this.parent === null || this.key === null) throw new Error("Can't replace the root node");
        const list = this.#list();
        if (list !== null && this.#cursor !== null) list[this.#cursor.index] = node;
        else fields(this.parent)[this.key] = node;
        this.node = node as N;
    }

    remove(): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't remove ${this.node.type} from ${this.parent?.type}.${this.key}: not in a list`);
        list.splice(this.#cursor.index, 1);
        this.#cursor.index -= 1;
        this.#removed = true;
        this.#skipped = true;
    }

    /** Inserted nodes are not visited. */
    insertBefore(nodes: readonly Node[]): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't insert next to ${this.node.type}: not in a list`);
        spliceList(list, this.#cursor.index, 0, nodes);
        this.#cursor.index += nodes.length;
    }

    /** Inserted nodes are not visited. */
    insertAfter(nodes: readonly Node[]): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't insert next to ${this.node.type}: not in a list`);
        spliceList(list, this.#cursor.index + 1, 0, nodes);
        this.#cursor.index += nodes.length;
    }

    /** Keeps the walk's cursor consistent; false if `node` isn't a sibling. */
    removeSibling(node: Node): boolean {
        const list = this.#list();
        if (list === null || this.#cursor === null) return false;
        const index = list.indexOf(node);
        if (index === -1 || index === this.#cursor.index) return false;
        list.splice(index, 1);
        if (index < this.#cursor.index) this.#cursor.index -= 1;
        return true;
    }

    /** This node is written, not (only) read: `x = ...`, `x++`, `delete x`, a for-in/of head, a destructuring target. */
    isWriteTarget(): boolean {
        const parent = this.parent;
        if (parent === null) return false;
        if (parent.type === "AssignmentExpression" && this.key === "left") return true;
        if (parent.type === "UpdateExpression") return true;
        if (parent.type === "UnaryExpression" && parent.operator === "delete") return true;
        if ((parent.type === "ForInStatement" || parent.type === "ForOfStatement") && this.key === "left") return true;
        if (parent.type === "AssignmentPattern") return this.key === "left";
        if (parent.type === "Property") return this.key === "value" && this.parentPath?.parent?.type === "ObjectPattern";
        return parent.type === "ArrayPattern" || parent.type === "RestElement";
    }

    isInStatementList(): boolean {
        const parent = this.parent;
        if (parent === null || this.index === null) return false;
        return parent.type === "Program" || parent.type === "BlockStatement" || parent.type === "StaticBlock" || (parent.type === "SwitchCase" && this.key === "consequent");
    }
}

export type VisitFn<N extends Node = Node> = (path: Path<N>) => void;
export type VisitEntry<N extends Node = Node> = VisitFn<N> | { enter?: VisitFn<N>; exit?: VisitFn<N> };
type NodeOfType<T extends string> = Extract<Node, { type: T }>;

export type Visitors = { [T in Node["type"]]?: VisitEntry<NodeOfType<T>> } & {
    enter?: VisitFn;
    exit?: VisitFn;
};

const isNode = (value: unknown): value is Node => typeof value === "object" && value !== null && typeof (value as { type?: unknown }).type === "string";

/**
 * Per node type, a generated function reading each child slot by name: V8 specialises each load to the type's shape,
 * where a loop over keys was the walk's hot spot. Slots are read in turn, after earlier ones were walked.
 */
const compileSlots = <F>(params: readonly string[], body: (key: string) => string): Readonly<Record<string, F | undefined>> => {
    const compiled: Record<string, F | undefined> = Object.create(null) as Record<string, F | undefined>;
    for (const [type, keys] of Object.entries(visitorKeys)) {
        if (keys.length === 0) continue;
        const code = keys.map((key) => `{ const value = node[${JSON.stringify(key)}]; if (typeof value === "object" && value !== null) { ${body(JSON.stringify(key))} } }`).join("\n");
        compiled[type] = new Function("node", ...params, code) as F;
    }
    return compiled;
};

const EACH_CHILD = compileSlots<(node: Node, fn: (child: Node) => void) => void>(
    ["fn"],
    () =>
        'if (Array.isArray(value)) { for (let i = 0; i < value.length; i++) { const child = value[i]; if (typeof child === "object" && child !== null && typeof child.type === "string") fn(child); } } else if (typeof value.type === "string") fn(value);'
);

type ListSlot = (value: unknown[], parentPath: Path, key: string, depth: number) => void;
type OneSlot = (value: Node, parentPath: Path, key: string, depth: number) => void;
const WALK_SLOTS = compileSlots<(node: Node, parentPath: Path, depth: number, list: ListSlot, one: OneSlot) => void>(
    ["parentPath", "depth", "list", "one"],
    (key) => `if (Array.isArray(value)) list(value, parentPath, ${key}, depth); else if (typeof value.type === "string") one(value, parentPath, ${key}, depth);`
);

export const forEachChild = (node: Node, fn: (child: Node) => void): void => {
    EACH_CHILD[node.type]?.(node, fn);
};

/**
 * Pre-order over `root` and its descendants, not entering functions: a function node (`root` too) isn't visited.
 * `enter` returning `false` skips the node's children; `leave` runs after the children of each node entered.
 */
export const walkSkippingFunctions = (root: Node, enter: (node: Node) => boolean, leave?: (node: Node) => void): void => {
    const walk = (node: Node): void => {
        if (isFunctionNode(node) || !enter(node)) return;
        EACH_CHILD[node.type]?.(node, walk);
        leave?.(node);
    };
    walk(root);
};

/** The input nests deeper than the walk's stack allows: the file fails (closed) with this instead of a bare RangeError. */
export class NestingError extends Error {
    constructor(depth?: number) {
        super(`the input nests too deeply to process${depth === undefined ? "" : ` (${depth}+ levels)`}`);
        this.name = "NestingError";
    }
}

export const isStackOverflow = (error: unknown): boolean => error instanceof RangeError && error.message.includes("call stack");

/** Depth-first in `visitorKeys` order. Visitors may replace/remove the current node and insert siblings (not visited). */
export const traverse = (root: Node, visitors: Visitors): void => {
    const byType = visitors as Record<string, VisitEntry<Node> | undefined>;
    const enterAny = visitors.enter;
    const exitAny = visitors.exit;
    const paths: Path[] = [];
    const pathAt = (depth: number, node: Node, parentPath: Path | null, key: string | null, cursor: Cursor | null): Path => {
        const existing = paths[depth];
        if (existing !== undefined) return existing[RESET](node, parentPath, key, cursor);
        const created = new Path(node, parentPath, key, cursor);
        paths[depth] = created;
        return created;
    };

    const list: ListSlot = (value, parentPath, key, depth) => {
        const cursor: Cursor = { index: 0 };
        for (; cursor.index < value.length; cursor.index++) {
            const child: unknown = value[cursor.index];
            if (isNode(child)) visit(pathAt(depth + 1, child, parentPath, key, cursor), depth + 1);
        }
    };
    const one: OneSlot = (value, parentPath, key, depth) => visit(pathAt(depth + 1, value, parentPath, key, null), depth + 1);

    const visit = (path: Path, depth: number): void => {
        const entry = byType[path.node.type];
        const enter = typeof entry === "function" ? entry : entry?.enter;
        const exit = typeof entry === "function" ? undefined : entry?.exit;

        enterAny?.(path);
        if (!path.skipped) enter?.(path);

        if (!path.skipped) {
            const node = path.node;
            WALK_SLOTS[node.type]?.(node, path, depth, list, one);
        }

        if (!path.removed) {
            exit?.(path);
            exitAny?.(path);
        }
    };

    try {
        visit(pathAt(0, root, null, null, null), 0);
    } catch (error) {
        throw isStackOverflow(error) ? new NestingError(paths.length) : error;
    }
};

/** Replace nodes by identity in one walk, for passes that decide before rewriting. Replacements aren't walked into. */
export const replaceNodes = (root: Node, replacements: ReadonlyMap<Node, Node>): number => {
    if (replacements.size === 0) return 0;
    let replaced = 0;
    traverse(root, {
        enter(path) {
            const replacement = replacements.get(path.node);
            if (replacement === undefined) return;
            path.replace(replacement);
            path.skip();
            replaced++;
        },
    });
    return replaced;
};
