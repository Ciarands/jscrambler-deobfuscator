import { visitorKeys } from "oxc-parser";
import type { Node } from "./ast.js";

type Container = Record<string, unknown>;

/** AST nodes are plain objects; the walker reads and writes their child fields by name (from `visitorKeys`). */
const fields = (node: Node): Container => node as unknown as Container;

/** Position of the node currently being visited inside an array, shared with the loop that walks the array. */
interface Cursor {
    index: number;
}

/** Re-points a path at another node (module-private: only the walker reuses paths). */
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

    /** The walker keeps one path per depth and points it at each node in turn: paths aren't kept past their visit. */
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

    /** Property of the parent holding this node, e.g. `"body"` or `"test"`. */
    get key(): string | null {
        return this.#key;
    }

    /** Index inside the parent's array, or `null` when the node is a plain property. */
    get index(): number | null {
        return this.#cursor?.index ?? null;
    }

    get removed(): boolean {
        return this.#removed;
    }

    get skipped(): boolean {
        return this.#skipped;
    }

    /** Don't walk this node's children. */
    skip(): void {
        this.#skipped = true;
    }

    #list(): Node[] | null {
        if (this.parent === null || this.key === null || this.#cursor === null) return null;
        return fields(this.parent)[this.key] as Node[];
    }

    /** Replace this node. The walker continues into the new node's children; its enter visitor is not called again. */
    replace(node: Node): void {
        if (this.parent === null || this.key === null) throw new Error("Can't replace the root node");
        const list = this.#list();
        if (list !== null && this.#cursor !== null) list[this.#cursor.index] = node;
        else fields(this.parent)[this.key] = node;
        this.node = node as N;
    }

    /** Remove this node from an array (statement lists, arguments, sequence items...). */
    remove(): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't remove ${this.node.type} from ${this.parent?.type}.${this.key}: not in a list`);
        list.splice(this.#cursor.index, 1);
        this.#cursor.index -= 1;
        this.#removed = true;
        this.#skipped = true;
    }

    /** Insert nodes before this one in the parent's array. They are not visited. */
    insertBefore(nodes: readonly Node[]): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't insert next to ${this.node.type}: not in a list`);
        list.splice(this.#cursor.index, 0, ...nodes);
        this.#cursor.index += nodes.length;
    }

    /** Insert nodes after this one in the parent's array. They are not visited. */
    insertAfter(nodes: readonly Node[]): void {
        const list = this.#list();
        if (list === null || this.#cursor === null) throw new Error(`Can't insert next to ${this.node.type}: not in a list`);
        list.splice(this.#cursor.index + 1, 0, ...nodes);
        this.#cursor.index += nodes.length;
    }

    /** Remove another node from the same array as this one, keeping the walk consistent. Returns false if it isn't there. */
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

    /** This node is an element of a statement list (program, block, static block or `case` body). */
    isInStatementList(): boolean {
        const parent = this.parent;
        if (parent === null || this.index === null) return false;
        return parent.type === "Program" || parent.type === "BlockStatement" || parent.type === "StaticBlock" || (parent.type === "SwitchCase" && this.key === "consequent");
    }
}

export type VisitFn<N extends Node = Node> = (path: Path<N>) => void;
export type VisitEntry<N extends Node = Node> = VisitFn<N> | { enter?: VisitFn<N>; exit?: VisitFn<N> };
type NodeOfType<T extends string> = Extract<Node, { type: T }>;

/** Visitors keyed by node type, plus `enter`/`exit` for every node. */
export type Visitors = { [T in Node["type"]]?: VisitEntry<NodeOfType<T>> } & {
    enter?: VisitFn;
    exit?: VisitFn;
};

/** Child slots (from `visitorKeys`) hold nodes or nothing. */
const isNode = (value: unknown): value is Node => typeof value === "object" && value !== null && typeof (value as { type?: unknown }).type === "string";

/** Call `fn` on each direct child node of `node`, in source order. */
export const forEachChild = (node: Node, fn: (child: Node) => void): void => {
    const container = fields(node);
    for (const key of visitorKeys[node.type] ?? []) {
        const value = container[key];
        if (Array.isArray(value)) {
            for (const child of value) if (isNode(child)) fn(child);
        } else if (isNode(value)) {
            fn(value);
        }
    }
};

/**
 * Walk `root` depth-first in source order (oxc `visitorKeys` order).
 *
 * Visitors may replace or remove the current node and insert siblings; the walk stays consistent.
 * Nodes inserted next to the current one are not visited.
 */
export const traverse = (root: Node, visitors: Visitors): void => {
    const byType = visitors as Record<string, VisitEntry<Node> | undefined>;
    const enterAny = visitors.enter;
    const exitAny = visitors.exit;
    // One path per depth, re-pointed for each sibling (paths aren't kept past their visit).
    const paths: Path[] = [];
    const pathAt = (depth: number, node: Node, parentPath: Path | null, key: string | null, cursor: Cursor | null): Path => {
        const existing = paths[depth];
        if (existing !== undefined) return existing[RESET](node, parentPath, key, cursor);
        const created = new Path(node, parentPath, key, cursor);
        paths[depth] = created;
        return created;
    };

    const visit = (path: Path, depth: number): void => {
        const entry = byType[path.node.type];
        const enter = typeof entry === "function" ? entry : entry?.enter;
        const exit = typeof entry === "function" ? undefined : entry?.exit;

        enterAny?.(path);
        if (!path.skipped) enter?.(path);

        if (!path.skipped) {
            const node = fields(path.node);
            const keys = visitorKeys[path.node.type];
            if (keys !== undefined) {
                for (const key of keys) {
                    const value = node[key];
                    if (Array.isArray(value)) {
                        const cursor: Cursor = { index: 0 };
                        for (; cursor.index < value.length; cursor.index++) {
                            const child: unknown = value[cursor.index];
                            if (isNode(child)) visit(pathAt(depth + 1, child, path, key, cursor), depth + 1);
                        }
                    } else if (isNode(value)) {
                        visit(pathAt(depth + 1, value, path, key, null), depth + 1);
                    }
                }
            }
        }

        if (!path.removed) {
            exit?.(path);
            exitAny?.(path);
        }
    };

    visit(pathAt(0, root, null, null, null), 0);
};

/**
 * Replace nodes by identity in one walk: for passes that decide first (collecting candidates, asking the sandbox in a
 * batch) and rewrite afterwards. Paths can't be kept for later: their array cursors move on as the walk does.
 * Replacements are not walked into. Returns how many nodes were replaced.
 */
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
