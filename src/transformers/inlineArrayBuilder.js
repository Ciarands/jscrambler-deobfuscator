import * as t from '@babel/types';

function valueToNode(value) {
    if (value === undefined) {
        return t.identifier('undefined');
    }
    return t.valueToNode(value);
}

export const inlineArrayBuilder = {
    priority: 300,
    visitor: {
        Function(path) {
            const functionScope = path.scope;
            const bodyPath = path.get('body');

            if (!bodyPath.isBlockStatement()) return;

            const trackers = new Map();
            let foundPaths = 0;
            let hasChanges = false;

            for (const name in functionScope.bindings) {
                trackers.set(name, {
                    values: new Map(),
                    poisoned: new Set(),
                    assignments: [],
                });
            }
            if (!trackers.size) return;

            // Only track identifiers that resolve to this function's own binding, not a
            // same-named variable in a nested function.
            const getTracker = (path, name) =>
                path.scope.getBinding(name) === functionScope.getBinding(name)
                    ? trackers.get(name)
                    : undefined;
            const isTrackedSlot = (node) =>
                t.isMemberExpression(node) &&
                node.computed &&
                t.isIdentifier(node.object) &&
                t.isNumericLiteral(node.property);
            const getConstant = (path, node) => {
                if (!isTrackedSlot(node)) return { found: false };
                const tracker = getTracker(path, node.object.name);
                const index = node.property.value;
                if (!tracker || tracker.poisoned.has(index) || !tracker.values.has(index)) {
                    return { found: false };
                }
                return { found: true, value: tracker.values.get(index) };
            };
            const evaluateNode = (node, path) => {
                if (
                    t.isStringLiteral(node) ||
                    t.isNumericLiteral(node) ||
                    t.isBooleanLiteral(node)
                ) {
                    return { success: true, value: node.value };
                }
                if (t.isNullLiteral(node)) {
                    return { success: true, value: null };
                }
                if (t.isIdentifier(node, { name: 'undefined' })) {
                    return { success: true, value: undefined };
                }
                if (t.isBinaryExpression(node, { operator: '+' })) {
                    const left = evaluateNode(node.left, path);
                    const right = evaluateNode(node.right, path);
                    if (left.success && right.success) {
                        return { success: true, value: left.value + right.value };
                    }
                }
                const constant = getConstant(path, node);
                if (constant.found) {
                    return { success: true, value: constant.value };
                }
                return { success: false };
            };

            bodyPath.traverse({
                AssignmentExpression(path) {
                    const { left, right, operator } = path.node;
                    if (!isTrackedSlot(left)) return;

                    const tracker = getTracker(path, left.object.name);
                    if (!tracker) return;
                    const index = left.property.value;

                    const evalResult = evaluateNode(right, path);
                    if (!evalResult.success || (operator !== '=' && operator !== '+=')) {
                        tracker.poisoned.add(index);
                        return;
                    }
                    if (operator === '=') {
                        tracker.values.set(index, evalResult.value);
                    } else {
                        const existingValue = tracker.values.get(index) || '';
                        tracker.values.set(index, existingValue + evalResult.value);
                    }
                    foundPaths += 1;
                    tracker.assignments.push({ path, index });
                },
                UpdateExpression(path) {
                    const { argument } = path.node;
                    if (!isTrackedSlot(argument)) return;
                    const tracker = getTracker(path, argument.object.name);
                    if (tracker) tracker.poisoned.add(argument.property.value);
                },
                'ForInStatement|ForOfStatement'(path) {
                    const { left } = path.node;
                    if (!isTrackedSlot(left)) return;
                    const tracker = getTracker(path, left.object.name);
                    if (tracker) tracker.poisoned.add(left.property.value);
                },
            });

            if (!foundPaths) return;
            console.log(` |-> Found ${trackers.size} target bindings.`);
            console.log(`   |-> Discovered ${foundPaths} target paths.`);

            bodyPath.traverse({
                MemberExpression(path) {
                    if (path.parentPath.isForInStatement({ left: path.node })) {
                        return;
                    }

                    if (
                        !path.parentPath.isAssignmentExpression({ left: path.node }) &&
                        !path.parentPath.isUpdateExpression()
                    ) {
                        const constant = getConstant(path, path.node);
                        if (constant.found) {
                            const replacementNode = valueToNode(constant.value);
                            if (replacementNode && !t.isNullLiteral(replacementNode)) {
                                path.replaceWith(replacementNode);
                                hasChanges = true;
                                return;
                            }
                        }
                    }

                    if (path.node.computed) {
                        const constant = getConstant(path, path.node.property);
                        if (constant.found) {
                            const replacementNode = valueToNode(constant.value);
                            if (replacementNode && !t.isNullLiteral(replacementNode)) {
                                path.get('property').replaceWith(replacementNode);
                                hasChanges = true;
                            }
                        }
                    }
                },
            });

            if (hasChanges) {
                let removedPaths = 0;
                for (const tracker of trackers.values()) {
                    for (const { path: assignPath, index } of tracker.assignments) {
                        if (tracker.poisoned.has(index) || assignPath.removed) continue;
                        // Remove only the assignment itself; never take other code in the
                        // statement with it, and keep it when its value is used.
                        const parent = assignPath.parentPath;
                        if (parent.isExpressionStatement()) {
                            parent.remove();
                            removedPaths += 1;
                        } else if (
                            parent.isSequenceExpression() &&
                            parent.node.expressions[parent.node.expressions.length - 1] !==
                                assignPath.node
                        ) {
                            assignPath.remove();
                            removedPaths += 1;
                        }
                    }
                }
                functionScope.crawl();
                for (const name in functionScope.bindings) {
                    const binding = functionScope.getBinding(name);
                    if (
                        !binding ||
                        binding.references !== 0 ||
                        !binding.path.isVariableDeclarator()
                    ) {
                        continue;
                    }
                    // Dropping the declaration is only safe if nothing else writes to the
                    // variable (it would become an implicit global) and the initializer has
                    // no side effects.
                    const init = binding.path.get('init');
                    if (binding.constantViolations.length > 0 || (init.node && !init.isPure())) {
                        continue;
                    }
                    binding.path.remove();
                    removedPaths += 1;
                }

                console.log(`   |-> Removed ${removedPaths} related paths.`);
            } else {
                console.warn('  |-> No modified paths!');
            }
        },
    },
};
