import * as t from '@babel/types';

function valueToNode(value) {
    if (value === undefined) {
        return t.identifier('undefined');
    }
    return t.valueToNode(value);
}

export const inlineArrayBuilder = {
    visitor: {
        Function(path) {
            const functionScope = path.scope;
            const bodyPath = path.get('body');

            if (!bodyPath.isBlockStatement()) return;

            const trackers = new Map();
            let hasChanges = false;

            for (const name in functionScope.bindings) {
                trackers.set(name, {
                    values: new Map(),
                    pathsToRemove: new Set(),
                });
            }

            const evaluateNode = (node) => {
                if (t.isStringLiteral(node) || t.isNumericLiteral(node) || t.isBooleanLiteral(node)) {
                    return { success: true, value: node.value };
                }
                if (t.isNullLiteral(node)) {
                    return { success: true, value: null };
                }
                if (t.isIdentifier(node, { name: 'undefined' })) {
                    return { success: true, value: undefined };
                }
                if (t.isBinaryExpression(node, { operator: '+' })) {
                    const left = evaluateNode(node.left);
                    const right = evaluateNode(node.right);
                    if (left.success && right.success) {
                        return { success: true, value: left.value + right.value };
                    }
                }
                if (t.isMemberExpression(node) && t.isIdentifier(node.object) && t.isNumericLiteral(node.property)) {
                    const tracker = trackers.get(node.object.name);
                    if (tracker && tracker.values.has(node.property.value)) {
                        return { success: true, value: tracker.values.get(node.property.value) };
                    }
                }
                return { success: false };
            };

            bodyPath.traverse({
                AssignmentExpression(assignmentPath) {
                    const { left, right, operator } = assignmentPath.node;

                    if (!t.isMemberExpression(left) || !t.isIdentifier(left.object) || !t.isNumericLiteral(left.property)) {
                        return;
                    }

                    const arrayName = left.object.name;
                    const index = left.property.value;
                    const tracker = trackers.get(arrayName);

                    if (!tracker) return;

                    const evalResult = evaluateNode(right);
                    if (evalResult.success) {
                        if (operator === '=') {
                            tracker.values.set(index, evalResult.value);
                        } else if (operator === '+=') {
                            const existingValue = tracker.values.get(index) || '';
                            tracker.values.set(index, existingValue + evalResult.value);
                        } else {
                            return;
                        }
                        const statement = assignmentPath.findParent(p => p.isStatement());
                        if (statement) {
                            tracker.pathsToRemove.add(statement);
                        }
                    }
                },
            });
            bodyPath.traverse({
                MemberExpression(memberPath) {
                    if (!memberPath.parentPath.isAssignmentExpression({ left: memberPath.node })) {
                        const { object, property } = memberPath.node;
                        if (t.isIdentifier(object) && t.isNumericLiteral(property)) {
                            const tracker = trackers.get(object.name);
                            if (tracker && tracker.values.has(property.value)) {
                                const constValue = tracker.values.get(property.value);
                                if (typeof constValue === 'number' && 
                                    (memberPath.parentPath.isUpdateExpression() || 
                                     memberPath.parentPath.isAssignmentExpression())) {
                                    return;
                                }
                                const replacementNode = valueToNode(constValue);
                                if (replacementNode) {
                                    memberPath.replaceWith(replacementNode);
                                    hasChanges = true;
                                    return;
                                }
                            }
                        }
                    }

                    if (memberPath.node.computed && t.isMemberExpression(memberPath.node.property)) {
                        const propertyExpr = memberPath.node.property;
                        if (t.isIdentifier(propertyExpr.object) && t.isNumericLiteral(propertyExpr.property)) {
                            const tracker = trackers.get(propertyExpr.object.name);
                            const index = propertyExpr.property.value;
                            if (tracker && tracker.values.has(index)) {
                                const constValue = tracker.values.get(index);
                                if (typeof constValue === 'number' && 
                                    (memberPath.parentPath.isUpdateExpression() || 
                                     memberPath.parentPath.isAssignmentExpression())) {
                                    return;
                                }
                                const replacementNode = valueToNode(constValue);
                                if (replacementNode) {
                                    memberPath.get('property').replaceWith(replacementNode);
                                    hasChanges = true;
                                }
                            }
                        }
                    }
                },
            });

            if (hasChanges) {
                for (const tracker of trackers.values()) {
                    const sortedPaths = Array.from(tracker.pathsToRemove).sort((a, b) => b.key - a.key);
                    for (const p of sortedPaths) {
                        if (p && !p.removed) {
                            p.remove();
                        }
                    }
                }
                functionScope.crawl();
                for (const name in functionScope.bindings) {
                    const binding = functionScope.getBinding(name);
                    if (binding && binding.references === 0 && binding.path.isVariableDeclarator()) {
                        binding.path.remove();
                    }
                }
            }
        },
    },
};