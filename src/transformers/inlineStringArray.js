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
            console.log(' |-> Starting string array inlining pass...');

            let arrayInfo = null;
            let arrayDefinitionPath = null;

            path.traverse({
                AssignmentExpression(assignmentPath) {
                    if (arrayInfo) return;

                    const right = assignmentPath.get('right');
                    if (!right.isCallExpression()) return;
                    const iife = right.get('callee');
                    if (!iife.isFunction()) return;

                    let foundInIIFE = false;

                    iife.traverse({
                        ObjectProperty(propPath) {
                            const accessorFunc = propPath.get('value');
                            if (!accessorFunc.isFunctionExpression()) return;
                            let returnedArray = null;
                            accessorFunc.traverse({
                                ReturnStatement(returnPath) {
                                    const arg = returnPath.get('argument');
                                    if (!arg.isMemberExpression()) return;

                                    const arrayCandidate = arg.get('object');
                                    if (arrayCandidate.isArrayExpression()) {
                                        returnedArray = arrayCandidate;
                                        returnPath.stop();
                                    }
                                },
                            });

                            if (!returnedArray) return;
                            const evalResults = returnedArray
                                .get('elements')
                                .map((el) => el.evaluate());

                            if (!evalResults.every((r) => r.confident)) {
                                console.warn(
                                    ' |-> Found a potential array, but could not evaluate all its elements confidently.'
                                );
                                return;
                            }

                            const theArray = evalResults.map((r) => r.value);
                            const objectNameString = generate.default(
                                assignmentPath.node.left
                            ).code;

                            const key = propPath.get('key');
                            const accessorName = key.isIdentifier()
                                ? key.node.name
                                : key.node.value;

                            arrayInfo = {
                                objectNameString,
                                accessorName,
                                theArray,
                            };

                            arrayDefinitionPath = assignmentPath.getStatementParent();
                            console.log(
                                ` |-> Successfully fingerprinted and parsed the literal array!`
                            );
                            console.log(`   |-> Object Name: '${objectNameString}'`);
                            console.log(`   |-> Accessor Name: '${accessorName}'`);
                            console.log(`   |-> Array Size: ${theArray.length}\n`);

                            foundInIIFE = true;
                            propPath.stop();
                        },
                    });

                    if (foundInIIFE) {
                        assignmentPath.stop();
                    }
                },
            });

            if (!arrayInfo) {
                console.log(' |-> No target array definition found. Exiting.');
                return;
            }

            let replacementsMade = 0;
            let anyInlineFailed = false;

            path.traverse({
                CallExpression(callPath) {
                    const callee = callPath.get('callee');
                    if (!callee.isMemberExpression()) return;

                    const { objectNameString, accessorName, theArray } = arrayInfo;
                    if (generate.default(callee.node.object).code !== objectNameString) return;

                    const property = callee.get('property');
                    const isAccessorMatch =
                        property.isIdentifier({ name: accessorName }) ||
                        property.isStringLiteral({ value: accessorName });

                    if (!isAccessorMatch) return;

                    const firstArg = callPath.get('arguments.0');
                    if (!firstArg) {
                        anyInlineFailed = true;
                        return;
                    }

                    const evaluation = firstArg.evaluate();

                    if (evaluation.confident && typeof evaluation.value === 'number') {
                        const index = evaluation.value;
                        if (index >= 0 && index < theArray.length) {
                            const resolvedValue = theArray[index];
                            const replacementNode = safeValueToNode(resolvedValue);

                            if (replacementNode) {
                                // console.log(` |-> Inlining ${generate.default(path.node).code} -> ${generate.default(replacementNode).code}`);
                                callPath.replaceWith(replacementNode);
                                replacementsMade++;
                            } else {
                                console.warn(
                                    ` |-> Could not create a literal node for value at index ${index}.`
                                );
                                anyInlineFailed = true;
                            }
                        } else {
                            console.warn(
                                ` |-> Index ${index} is out of bounds for call: ${
                                    generate.default(callPath.node).code
                                }`
                            );
                            anyInlineFailed = true;
                        }
                    } else {
                        console.warn(
                            ` |-> Could not statically resolve index for call: ${
                                generate.default(callPath.node).code
                            }`
                        );
                        anyInlineFailed = true;
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
