import * as t from '@babel/types';
import generate from '@babel/generator';

function safeValueToNode(value) {
    if (value === undefined) {
        return t.identifier('undefined');
    }
    try {
        return t.valueToNode(value);
    } catch (e) {
        return null;
    }
}

export const inlineStringArray = {
    priority: 800,
    visitor: {
        Program(path) {
            console.log(' |-> Starting inlining pass...');

            let arrayInfo = null;
            let anyInlineFailed = false;
            let arrayDefinitionPath = null;

            path.traverse({
                AssignmentExpression(path) {
                    if (arrayInfo) return;
                    const right = path.get('right');
                    if (!right.isCallExpression() || !right.get('callee').isFunctionExpression()) {
                        return;
                    }

                    const iifePath = right.get('callee');
                    iifePath.traverse({
                        ArrayExpression(arrayPath) {
                            const parentMemberExpr = arrayPath.parentPath;
                            if (
                                !parentMemberExpr.isMemberExpression({
                                    object: arrayPath.node,
                                })
                            )
                                return;
                            const grandParentReturn = parentMemberExpr.parentPath;
                            if (
                                !grandParentReturn.isReturnStatement({
                                    argument: parentMemberExpr.node,
                                })
                            )
                                return;
                            const accessorFunc = grandParentReturn.findParent((p) =>
                                p.isFunctionExpression()
                            );
                            if (!accessorFunc) return;
                            const objectProp = accessorFunc.findParent((p) =>
                                p.isObjectProperty({
                                    value: accessorFunc.node,
                                })
                            );
                            if (!objectProp) return;
                            const evalResults = arrayPath
                                .get('elements')
                                .map((el) => el.evaluate());
                            if (!evalResults.every((r) => r.confident)) {
                                return;
                            }
                            const theArray = evalResults.map((r) => r.value);
                            const objectName = generate.default(path.node.left);
                            const accessorName = objectProp.get('key').isIdentifier()
                                ? objectProp.get('key').node.name
                                : objectProp.get('key').node.value;
                            arrayInfo = {
                                objectName,
                                accessorName,
                                theArray,
                            };
                            arrayDefinitionPath = path.getStatementParent();
                            console.log(` |-> Successfully parsed literal array!`);
                            console.log(`   |-> Object Name: '${objectName}'`);
                            console.log(`   |->  Accessor Name: '${accessorName}'`);
                            console.log(`   |->  Array Size:${theArray.length}\n`);
                            arrayPath.stop();
                        },
                    });
                    if (arrayInfo) {
                        path.stop();
                    }
                },
            });

            if (!arrayInfo) {
                console.log(' |-> No target array definition found. Exiting.');
                return;
            }

            let replacementsMade = 0;

            path.traverse({
                CallExpression(path) {
                    const callee = path.get('callee');
                    if (!callee.isMemberExpression()) return;
                    const { objectName, accessorName, theArray } = arrayInfo;
                    if (
                        generate.default(callee.node.object) === objectName &&
                        callee.get('property').isIdentifier({
                            name: accessorName,
                        })
                    ) {
                        const evaluation = path.get('arguments.0').evaluate();
                        if (evaluation.confident && typeof evaluation.value === 'number') {
                            const index = evaluation.value;
                            if (index >= 0 && index < theArray.length) {
                                const resolvedValue = theArray[index];
                                const replacementNode = safeValueToNode(resolvedValue);
                                if (replacementNode) {
                                    // console.log(` |-> Inlining ${generate.default(path.node)} -> ${generate.default(replacementNode)}`);
                                    path.replaceWith(replacementNode);
                                    replacementsMade++;
                                } else {
                                    console.warn(
                                        ` |-> Could not create a literal node for value at index ${index}.`
                                    );
                                    anyInlineFailed = true;
                                }
                            } else {
                                console.warn(
                                    ` |-> Index ${index} is out of bounds for call: ${generate.default(
                                        path.node
                                    )}`
                                );
                                anyInlineFailed = true;
                            }
                        } else {
                            console.warn(
                                ` |-> Could not statically resolve index for call: ${generate.default(
                                    path.node
                                )}`
                            );
                            anyInlineFailed = true;
                        }
                    }
                },
            });

            console.log(` |-> Made ${replacementsMade} replacements.`);
            if (anyInlineFailed) {
                console.log(
                    ' |-> One or more node(s) could not be resolved due to above warnings, skipping cleanup step.'
                );
            } else if (
                arrayDefinitionPath &&
                !arrayDefinitionPath.removed &&
                replacementsMade > 0
            ) {
                try {
                    arrayDefinitionPath.remove();
                    console.log(' |-> Cleanup: Removed original array definition.');
                } catch (e) {
                    console.error(' |-> Cleanup failed.', e);
                }
            }

            path.skip();
        },
    },
};
