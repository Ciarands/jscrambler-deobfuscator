import type { Visitor, NodePath } from "@babel/traverse";
import * as t from "@babel/types";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

function getMemberExpressionName(node: t.MemberExpression): string | null {
    const parts: string[] = [];
    let current: t.Expression | t.PrivateName = node;

    while (t.isMemberExpression(current)) {
        if (t.isIdentifier(current.property) && !current.computed) {
            parts.unshift(current.property.name);
        } else if (t.isStringLiteral(current.property)) {
            parts.unshift(current.property.value);
        } else if (t.isNumericLiteral(current.property)) {
            parts.unshift(String(current.property.value));
        } else {
            parts.unshift("[computed]");
        }
        current = current.object;
    }

    if (t.isIdentifier(current)) {
        parts.unshift(current.name);
    } else {
        return null;
    }

    return parts.join(".");
}

function isGlobalThisProxy(functionBody: t.Statement[]): boolean {
    let hasGlobalThisCheck = false;
    let hasDefineProperty = false;
    let hasWindowFallback = false;
    let hasReturnThis = false;

    const checkNode = (node: any): void => {
        if (!node) return;

        if (t.isBinaryExpression(node) && t.isUnaryExpression(node.left) && node.left.operator === "typeof" && t.isIdentifier(node.left.argument) && node.left.argument.name === "globalThis") {
            hasGlobalThisCheck = true;
        }

        // Object["defineProperty"]
        if (
            t.isCallExpression(node) &&
            t.isMemberExpression(node.callee) &&
            ((t.isIdentifier(node.callee.object) && node.callee.object.name === "Object") || t.isIdentifier(node.callee.object, { name: "Object" })) &&
            ((t.isIdentifier(node.callee.property) && node.callee.property.name === "defineProperty") || (t.isStringLiteral(node.callee.property) && node.callee.property.value === "defineProperty"))
        ) {
            hasDefineProperty = true;
        }

        // "return this"
        if (t.isReturnStatement(node) && t.isThisExpression(node.argument)) {
            hasReturnThis = true;
        }

        if (t.isIdentifier(node) && node.name === "window") {
            hasWindowFallback = true;
        }

        // recurse child nodes
        if (Array.isArray(node)) {
            node.forEach(checkNode);
        } else if (typeof node === "object") {
            Object.keys(node).forEach((key) => {
                if (key !== "loc" && key !== "start" && key !== "end") {
                    checkNode(node[key]);
                }
            });
        }
    };

    functionBody.forEach(checkNode);

    return hasGlobalThisCheck && hasDefineProperty && hasWindowFallback && hasReturnThis;
}

const globalThisProxies = new Set<string>();

const visitor: Visitor<any> = {
    Program: {
        enter(path, state) {
            globalThisProxies.clear();
            state?.logger?.debug?.("[prepare] Program enter");
        },
        exit(path, state) {
            if (globalThisProxies.size === 0) return;

            // for (const name of Array.from(globalThisProxies)) {
            //     t.addComment(path.node, "leading", ` globalThis proxy: \`${name}\` `, true);
            //     state?.logger?.debug?.(`[prepare] Marked proxy name: ${name}`);
            // }

            path.traverse({
                Identifier(p) {
                    if (p.isReferencedIdentifier() && globalThisProxies.has(p.node.name)) {
                        t.addComment(p.node, "leading", " globalThis ", false);
                        state?.logger?.debug?.(`[prepare] Annotated identifier reference: ${p.node.name}`);
                    }
                },
                MemberExpression(p) {
                    const full = getMemberExpressionName(p.node);
                    if (full && globalThisProxies.has(full)) {
                        t.addComment(p.node, "leading", " globalThis ", false);
                        state?.logger?.debug?.(`[prepare] Annotated member reference: ${full}`);
                    }
                },
            });
        },
    },

    // do not tag FunctionDeclaration to avoid false positives on wrappers/global decls
    FunctionExpression(path, state) {
        // The function must be either:
        // 1) The right-hand side of an assignment, or
        // 2) The initializer of a variable declarator, or
        // 3) The callee of a CallExpression whose result is assigned (IIFE assigned)

        let assignedContainer: NodePath | null = null;

        const parent = path.parentPath;
        if (!parent) return;

        if (parent.isAssignmentExpression() && parent.node.right === path.node) {
            assignedContainer = parent;
        } else if (parent.isVariableDeclarator() && parent.node.init === path.node) {
            assignedContainer = parent;
        } else if (parent.isCallExpression() && parent.node.callee === path.node) {
            const gp = parent.parentPath;
            if (gp && gp.isAssignmentExpression() && gp.node.right === parent.node) {
                assignedContainer = gp;
            } else if (gp && gp.isVariableDeclarator() && gp.node.init === parent.node) {
                assignedContainer = gp;
            } else {
                return;
            }
        } else {
            return;
        }

        if (!isGlobalThisProxy(path.node.body.body)) return;

        let targetRHS: any = null;
        if (assignedContainer.isAssignmentExpression()) {
            targetRHS = (assignedContainer as any).get("right");
        } else if (assignedContainer.isVariableDeclarator()) {
            targetRHS = (assignedContainer as any).get("init");
        }
        if (targetRHS) {
            targetRHS.replaceWith(t.identifier("globalThis"));
            state?.logger?.debug?.("[prepare] Replaced proxy IIFE with globalThis");
        }

        if (assignedContainer.isAssignmentExpression()) {
            const left = assignedContainer.node.left;
            if (t.isIdentifier(left)) {
                globalThisProxies.add(left.name);
                state?.logger?.debug?.(`[prepare] Detected proxy name: ${left.name}`);
            } else if (t.isMemberExpression(left)) {
                const fullName = getMemberExpressionName(left);
                if (fullName) {
                    globalThisProxies.add(fullName);
                    state?.logger?.debug?.(`[prepare] Detected proxy name: ${fullName}`);
                }
            }
        } else if (assignedContainer.isVariableDeclarator()) {
            const id = assignedContainer.node.id;
            if (t.isIdentifier(id)) {
                globalThisProxies.add(id.name);
                state?.logger?.debug?.(`[prepare] Detected proxy name: ${id.name}`);
            } else if (t.isMemberExpression(id)) {
                const fullName = getMemberExpressionName(id);
                if (fullName) {
                    globalThisProxies.add(fullName);
                    state?.logger?.debug?.(`[prepare] Detected proxy name: ${fullName}`);
                }
            }
        }
    },

    StringLiteral(path, state) {
        /* babel automatically decodes escape sequences into node.value if we clear the 'extra' property which 
        contains the raw/escaped representation then Babel generates clean output without escape sequences & other stuff */
        if (path.node.extra) {
            delete path.node.extra;
        }
    },

    // TODO: normalize BinaryExpressions / UniaryExpressions (e.g. +"1" should be resolved to numeric literal 1)
};

export const prepareTransformer: Transformer = {
    name: "prepare",
    description: "Initial preparation and setup of the AST",
    priority: TransformerPriority.PREPARE,
    visitor,
};
