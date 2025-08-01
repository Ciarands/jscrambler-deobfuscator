import * as t from '@babel/types';

function resolveIdentifierChain(node, scope) {
    let current = node;
    const seen = new Set();

    while (t.isIdentifier(current) && !seen.has(current.name)) {
        seen.add(current.name);
        const binding = scope.getBinding(current.name);

        if (binding && binding.path.isVariableDeclarator() && binding.path.node.init) {
            current = binding.path.node.init;
        } else {
            break;
        }
    }
    return current;
}

function areNodesEquivalentAfterResolution(nodeA, nodeB, scope) {
    const resolvedA = resolveIdentifierChain(nodeA, scope);
    const resolvedB = resolveIdentifierChain(nodeB, scope);
    return t.isNodesEquivalent(resolvedA, resolvedB);
}

function isWrapperFunction(node, scope) {
    if (
        !t.isFunctionExpression(node) ||
        node.body.body.length !== 1 ||
        !t.isReturnStatement(node.body.body[0])
    ) {
        return null;
    }
    const returnArg = node.body.body[0].argument;
    if (!t.isConditionalExpression(returnArg)) {
        return null;
    }
    const { test, consequent, alternate } = returnArg;
    if (!t.isBinaryExpression(test) || (test.operator !== '===' && test.operator !== '==')) {
        return null;
    }
    let typeofExpr = null;
    if (
        t.isUnaryExpression(test.left, { operator: 'typeof' }) &&
        t.isStringLiteral(test.right, { value: 'function' })
    ) {
        typeofExpr = test.left;
    } else if (
        t.isUnaryExpression(test.right, { operator: 'typeof' }) &&
        t.isStringLiteral(test.left, { value: 'function' })
    ) {
        typeofExpr = test.right;
    } else {
        return null;
    }
    const targetExpression = typeofExpr.argument;
    if (!t.isMemberExpression(targetExpression)) {
        return null;
    }

    const functionBodyScope = node.body.scope;
    if (!areNodesEquivalentAfterResolution(alternate, targetExpression, functionBodyScope)) {
        return null;
    }
    if (
        !t.isCallExpression(consequent) ||
        !t.isMemberExpression(consequent.callee) ||
        !t.isIdentifier(consequent.callee.property, { name: 'apply' })
    ) {
        return null;
    }
    if (
        !areNodesEquivalentAfterResolution(
            consequent.callee.object,
            targetExpression,
            functionBodyScope
        )
    ) {
        return null;
    }
    const applyArgs = consequent.arguments;
    if (applyArgs.length !== 2) return null;
    if (
        !areNodesEquivalentAfterResolution(applyArgs[0], targetExpression.object, functionBodyScope)
    ) {
        return null;
    }
    if (!t.isIdentifier(applyArgs[1], { name: 'arguments' })) {
        return null;
    }
    return targetExpression;
}

function getMemberKey(node) {
    if (node.computed && (t.isStringLiteral(node.property) || t.isNumericLiteral(node.property))) {
        return node.property.value;
    }
    if (!node.computed && t.isIdentifier(node.property)) {
        return node.property.name;
    }
    return null;
}

export const inlineWrapperFunctions = {
    priority: 100,
    visitor: {
        Program(programPath) {
            const baseObjectNode = programPath.node.injectedGlobal;

            if (!baseObjectNode || !t.isIdentifier(baseObjectNode)) {
                console.error(
                    ' |-> No injected global base object found. Halting. (prepare.js didnt find global object func!)'
                );
                console.warn(
                    ' |-> FIXME (knownissue): This happens on some samples, it will still work.'
                );
                return;
            }
            console.log(` |-> Base Object is the injected global: "${baseObjectNode.name}".`);

            const wrapperMap = new Map();
            console.log(' |-> Pass 1: Mapping all wrappers...');
            programPath.traverse({
                AssignmentExpression(path) {
                    const { left, right } = path.node;
                    if (path.node.operator !== '=' || !t.isMemberExpression(left)) return;

                    let baseObjectCandidate = left.object;
                    if (t.isAssignmentExpression(baseObjectCandidate)) {
                        baseObjectCandidate = baseObjectCandidate.right;
                    }

                    if (
                        !areNodesEquivalentAfterResolution(
                            baseObjectCandidate,
                            baseObjectNode,
                            path.scope
                        )
                    )
                        return;

                    const targetMemberExpr = isWrapperFunction(right, path.scope);
                    if (targetMemberExpr) {
                        const wrapperKey = getMemberKey(left);
                        if (wrapperKey !== null) {
                            wrapperMap.set(wrapperKey, targetMemberExpr);
                        }
                    }
                },
            });

            if (wrapperMap.size === 0) {
                console.log(' |-> No wrapper function definitions found. Halting.');
                return;
            }
            console.log(
                ` |-> Mapping complete. Found ${wrapperMap.size} unique wrapper definitions.`
            );

            console.log(' |-> Pass 2: Inlining calls and removing definitions...');
            programPath.traverse({
                CallExpression: {
                    exit(callPath) {
                        const callee = callPath.node.callee;
                        if (!t.isMemberExpression(callee)) return;

                        if (
                            !areNodesEquivalentAfterResolution(
                                callee.object,
                                baseObjectNode,
                                callPath.scope
                            )
                        )
                            return;

                        const wrapperKey = getMemberKey(callee);
                        if (wrapperKey !== null && wrapperMap.has(wrapperKey)) {
                            const targetMemberExpr = wrapperMap.get(wrapperKey);
                            if (callPath.node.arguments.length === 0) {
                                callPath.replaceWith(targetMemberExpr);
                            } else {
                                callPath.replaceWith(
                                    t.callExpression(targetMemberExpr, callPath.node.arguments)
                                );
                            }
                        }
                    },
                },
                AssignmentExpression: {
                    exit(assignmentPath) {
                        const { left, right } = assignmentPath.node;
                        if (!t.isMemberExpression(left)) return;

                        let baseObjectCandidate = left.object;
                        if (t.isAssignmentExpression(baseObjectCandidate)) {
                            baseObjectCandidate = baseObjectCandidate.right;
                        }

                        if (
                            !areNodesEquivalentAfterResolution(
                                baseObjectCandidate,
                                baseObjectNode,
                                assignmentPath.scope
                            )
                        )
                            return;

                        const wrapperKey = getMemberKey(left);
                        if (wrapperKey !== null && wrapperMap.has(wrapperKey)) {
                            if (isWrapperFunction(right, assignmentPath.scope)) {
                                assignmentPath.replaceWith(t.identifier('undefined'));
                            }
                        }
                    },
                },
            });

            programPath.scope.crawl();
            programPath.traverse({
                SequenceExpression: {
                    exit(p) {
                        const filtered = p.node.expressions.filter(
                            (e) => !t.isIdentifier(e, { name: 'undefined' })
                        );
                        if (filtered.length === 0 && p.parentPath.isExpressionStatement()) {
                            p.remove();
                        } else if (filtered.length === 1) {
                            p.replaceWith(filtered[0]);
                        } else if (filtered.length < p.node.expressions.length) {
                            p.node.expressions = filtered;
                        }
                    },
                },
            });
        },
    },
};
