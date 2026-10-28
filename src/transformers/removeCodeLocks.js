import * as t from '@babel/types';
import generator from '@babel/generator';

export const removeCodeLocks = {
    priority: 150,
    visitor: {
        Program(programPath) {

            const baseObjectNode = programPath.node.injectedGlobal;

            if (!baseObjectNode || !t.isIdentifier(baseObjectNode)) {
                console.error(
                    ' |-> No injected global base object found. Halting. (removeCodeLocks.js didnt find global object func!)'
                );
                return;
            }
            console.log(` |-> Base Object is the injected global: "${baseObjectNode.name}".`);

            let globalKey = null;
            let functionName = null;
            let hasName = false;

            programPath.traverse({
                AssignmentExpression(assignPath) {

                    const node = assignPath.node;

                    let potentialGlobalKey;
                    if (!t.isMemberExpression(node.left)
                        || !t.isIdentifier(node.left.object)
                        || baseObjectNode.name != node.left.object.name) return;

                    if (t.isNumericLiteral(node.left.property)) {
                        potentialGlobalKey = node.left.property.value;
                        hasName = false;
                    } else if (t.isIdentifier(node.left.property) && !node.left.computed) {
                        potentialGlobalKey = node.left.property.name;
                        hasName = true;
                    } else {
                        return;
                    }

                    if (!t.isCallExpression(node.right)
                        || (!t.isFunctionExpression(node.right.callee)
                        && !t.isArrowFunctionExpression(node.right.callee))) return;

                    assignPath.get('right').traverse({
                        AssignmentExpression(innerPath) {

                            const innerNode = innerPath.node;

                            if (!t.isAssignmentExpression(innerNode) || innerNode.operator !== '=') return;

                            const innerRight = innerNode.right;
                            if (!t.isFunctionExpression(innerRight) && !t.isArrowFunctionExpression(innerRight)) return;

                            let found = false;
                            innerPath.get('right').traverse({
                                ReturnStatement(retPath) {
                                    const retArg = retPath.node.argument;
                                    if (t.isNumericLiteral(retArg)) {
                                        found = true;
                                        retPath.stop();
                                    }
                                }
                            });

                            if (found) {
                                const innerLeft = innerNode.left;
                                if (t.isMemberExpression(innerLeft) && t.isIdentifier(innerLeft.property)) {
                                    functionName = innerLeft.property.name;
                                    globalKey = potentialGlobalKey;
                                    innerPath.stop();
                                    assignPath.stop();
                                }
                            }
                        }
                    });
                }
            });

            if (!functionName || globalKey === null) {
                console.log(" |-> Failed to locate scoring function");
                return;
            }

            console.log(` |-> Found scoring function ${baseObjectNode.name}[${globalKey}].${functionName}`);

            let totalRemoved = 0;

            const isTarget = (node) => {
                if (!t.isMemberExpression(node) || node.computed) return false;
                if (!t.isIdentifier(node.property, { name: functionName })) return false;

                const obj = node.object;
                if (!t.isMemberExpression(obj)) return false;
                if (hasName) {
                    if (obj.computed || !t.isIdentifier(obj.property) || obj.property.name !== globalKey) return false;
                } else if (!t.isNumericLiteral(obj.property) || obj.property.value !== globalKey) return false;

                const innerObj = obj.object;
                if (!t.isIdentifier(innerObj, { name: baseObjectNode.name })) return false;

                return true;
            };

            programPath.traverse({
                SequenceExpression(sequencePath) {
                    const expressions = sequencePath.node.expressions;
                    const newExpressions = expressions.filter(e => !isTarget(e));
                    const diff = expressions.length - newExpressions.length;

                    if (diff > 0) {
                        totalRemoved += diff;
                        if (newExpressions.length === 1) {
                            sequencePath.replaceWith(newExpressions[0]);
                        } else if (newExpressions.length === 0) {
                            if (sequencePath.parentPath.isExpressionStatement()) {
                                sequencePath.parentPath.remove();
                            } else {
                                sequencePath.remove();
                            }
                        } else {
                            sequencePath.node.expressions = newExpressions;
                        }
                    }
                },
                ExpressionStatement(expressionPath) {
                    if (isTarget(expressionPath.node.expression)) {
                        expressionPath.remove();
                        totalRemoved++;
                    }
                }
            });

            console.log(" |->   Removed scoring function references. " + totalRemoved);
        }
    }
};
