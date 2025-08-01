import * as t from '@babel/types';

let largeStringInfo = null;
let decoderInfo = null;

function getNumericValue(node) {
    if (t.isNumericLiteral(node)) {
        return node.value;
    }
    if (t.isUnaryExpression(node) && node.operator === '-' && t.isNumericLiteral(node.argument)) {
        return -node.argument.value;
    }
    return NaN;
}

function correctlyShuffle(arr, ops) {
    const newArr = [...arr];
    for (const op of ops) {
        const p1 = newArr.splice(op.s1_offset, op.s1_length);
        const p2 = p1.splice(op.s2_offset, op.s2_length);
        newArr.unshift(...p2);
    }
    return newArr;
}

function findDecoderData(funcPath) {
    let separator = '';
    const shuffleOps = [];

    funcPath.traverse({
        CallExpression(path) {
            const callee = path.get('callee');
            const args = path.get('arguments');
            const calleeNode = callee.node;

            if (
                !separator &&
                callee.isMemberExpression() &&
                t.isIdentifier(calleeNode.property, { name: 'split' })
            ) {
                const separatorArg = args.length === 1 ? args[0] : args[1];
                if (separatorArg && separatorArg.isStringLiteral()) {
                    separator = separatorArg.node.value;
                }
            }

            let outerSplicePath = null;
            if (
                t.isMemberExpression(calleeNode) &&
                t.isIdentifier(calleeNode.property, { name: 'apply' })
            ) {
                const object = callee.get('object');
                // Pattern A: array.unshift.apply(array, spliceChain)
                if (
                    args.length === 2 &&
                    object.isMemberExpression() &&
                    t.isIdentifier(object.node.property, { name: 'unshift' })
                ) {
                    outerSplicePath = args[1];
                }
                // Pattern B: _.apply(_.unshift(), array, spliceChain)
                else if (args.length === 3) {
                    const firstArg = args[0];
                    if (
                        firstArg.isCallExpression() &&
                        t.isIdentifier(firstArg.get('callee.property').node, { name: 'unshift' })
                    ) {
                        outerSplicePath = args[2];
                    }
                }
            }

            if (outerSplicePath) {
                const outerArgs = outerSplicePath.get('arguments');
                if (!outerSplicePath.isCallExpression() || outerArgs.length < 3) return;

                const innerSplicePath = outerArgs[0];
                const innerArgs = innerSplicePath.get('arguments');
                if (!innerSplicePath.isCallExpression() || innerArgs.length < 3) return;

                const op = {
                    s1_offset: getNumericValue(innerArgs[1].node),
                    s1_length: getNumericValue(innerArgs[2].node),
                    s2_offset: getNumericValue(outerArgs[1].node),
                    s2_length: getNumericValue(outerArgs[2].node),
                };

                if (!Object.values(op).some(isNaN)) {
                    shuffleOps.push(op);
                }
                path.skip();
                return;
            }

            // fallback
            if (callee.isMemberExpression() && callee.get('object').isCallExpression()) {
                const innerCall = callee.get('object');
                const getNumericArgs = (callPath) =>
                    callPath
                        .get('arguments')
                        .filter((p) => t.isNumericLiteral(p.node) || t.isUnaryExpression(p.node));

                const innerNumericArgs = getNumericArgs(innerCall);
                const outerNumericArgs = getNumericArgs(path);

                if (innerNumericArgs.length >= 2 && outerNumericArgs.length >= 2) {
                    const op = {
                        s1_offset: getNumericValue(innerNumericArgs[0].node),
                        s1_length: getNumericValue(innerNumericArgs[1].node),
                        s2_offset: getNumericValue(outerNumericArgs[0].node),
                        s2_length: getNumericValue(outerNumericArgs[1].node),
                    };
                    if (!Object.values(op).some(isNaN)) {
                        shuffleOps.push(op);
                    }
                }
            }
        },
    });

    if (separator && shuffleOps.length > 0) {
        return { separator, shuffleOps };
    }

    if (!separator)
        console.error(' |-> Candidate decoder did not contain a recognizable split operation.');
    if (shuffleOps.length === 0)
        console.error(
            ' |-> Candidate decoder did not contain any recognizable shuffle operations.'
        );
    return null;
}

export const solveStringArray = {
    priority: 600,
    visitor: {
        Program: {
            enter(path) {
                largeStringInfo = null;
                decoderInfo = null;
                path.traverse({
                    FunctionDeclaration(funcPath) {
                        if (largeStringInfo) return;
                        const body = funcPath.get('body.body');
                        if (body.length !== 1 || !body[0].isReturnStatement()) return;
                        const returnArg = body[0].get('argument');
                        if (!returnArg.isStringLiteral() || returnArg.node.value.length < 50)
                            return;
                        console.log(
                            ` |-> Found string function identifier: "${
                                funcPath.node.id?.name || '(anonymous)'
                            }"`
                        );
                        largeStringInfo = { value: returnArg.node.value, path: funcPath };
                        funcPath.stop();
                    },
                });
            },
            exit(path) {
                if (!largeStringInfo || !decoderInfo) {
                    const missing = [];
                    if (!largeStringInfo) missing.push('large string function');
                    if (!decoderInfo) missing.push('decoder IIFE');
                    console.error(` |-> Aborting. Could not find: ${missing.join(' and ')}.`);
                    return;
                }
                console.log(' |-> Targets found, attempting to reveal strings...');
                const { value: uriString } = largeStringInfo;
                const { xorKey, separator, shuffleOps, replacementPath, propKey, isNested } =
                    decoderInfo;

                console.log(
                    `   |-> Successfully extracted ${shuffleOps.length} shuffle operations.`
                );
                const decodedString = decodeURIComponent(uriString);
                let xorResult = '';
                for (let i = 0; i < decodedString.length; i++) {
                    xorResult += String.fromCharCode(
                        decodedString.charCodeAt(i) ^ xorKey.charCodeAt(i % xorKey.length)
                    );
                }
                let processedArray = xorResult.split(separator);
                processedArray = correctlyShuffle(processedArray, shuffleOps);
                console.log(`   |-> Decrypted array with ${processedArray.length} elements.`);

                const finalArrayNode = t.arrayExpression(
                    processedArray.map((s) => t.stringLiteral(s))
                );
                const indexIdentifier = t.identifier('index');
                const newFunctionNode = t.functionExpression(
                    null,
                    [indexIdentifier],
                    t.blockStatement([
                        t.returnStatement(
                            t.memberExpression(finalArrayNode, indexIdentifier, true)
                        ),
                    ])
                );

                if (isNested) {
                    const assignmentPath = replacementPath.findParent((p) =>
                        p.isAssignmentExpression()
                    );
                    const newRight = t.objectExpression([
                        t.objectProperty(t.identifier(propKey), newFunctionNode),
                    ]);
                    if (assignmentPath) {
                        assignmentPath.get('right').replaceWith(newRight);
                        console.log(`   |-> Replaced nested decoder with a clean accessor object.`);
                    } else {
                        const outerIife = replacementPath.findParent(
                            (p) =>
                                p.isCallExpression() &&
                                (p.get('callee').isFunctionExpression() ||
                                    p.get('callee').isArrowFunctionExpression())
                        );
                        if (outerIife) {
                            outerIife.replaceWith(newRight);
                            console.log(
                                `   |-> Replaced nested decoder IIFE with a clean accessor object. (early return fallback)`
                            );
                        }
                    }
                } else {
                    replacementPath.replaceWith(newFunctionNode);
                    console.log('   |-> Replaced simple decoder IIFE with a new accessor function.');
                }

                largeStringInfo.path.remove();
                console.log('   |-> Removed string function.');
            },
        },
        CallExpression(path) {
            if (decoderInfo || !largeStringInfo) return;
            const callee = path.get('callee');
            const args = path.get('arguments');

            if (
                !(callee.isFunctionExpression() || callee.isArrowFunctionExpression()) ||
                args.length !== 1 ||
                !args[0].isStringLiteral()
            ) {
                return;
            }
            const xorKey = args[0].node.value;
            console.log(` |-> Found candidate decoder IIFE`);
            console.log(`   |-> Identifier: ${callee.name}`);
            console.log(`   |-> XOR Key: "${xorKey}"`);
            const data = findDecoderData(callee);
            if (!data) {
                console.error(` |-> Candidate with key "${xorKey}" failed verification.`);
                return;
            }
            console.log(` |-> Sucessfully verified candidate function`);
            console.log(`   |->  Separator: "${data.separator}"`);
            console.log(`   |->  Shuffles: ${data.shuffleOps.length}`);

            const assignmentPath = path.findParent((p) => p.isAssignmentExpression());
            if (assignmentPath) {
                const propPath = path.findParent((p) => p.isObjectProperty());
                if (propPath) {
                    const keyNode = propPath.get('key').node;
                    const propKey = t.isIdentifier(keyNode) ? keyNode.name : keyNode.value;
                    decoderInfo = {
                        xorKey,
                        ...data,
                        replacementPath: path,
                        propKey,
                        isNested: true,
                    };
                    path.stop();
                }
            } else {
                decoderInfo = {
                    xorKey,
                    ...data,
                    replacementPath: path,
                    propKey: null,
                    isNested: false,
                };
                path.stop();
            }
        },
    },
};
