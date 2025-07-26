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

function findDecoderIngredients(funcPath) {
    let separator = '';
    const shuffleOps = [];

    funcPath.traverse({
        "AssignmentExpression|CallExpression"(path) {
            let callPath = path.isCallExpression() ? path : path.get('right');
            if (!callPath.isCallExpression()) return;

            const callee = callPath.get('callee');
            const args = callPath.get('arguments');

            if (callee.isMemberExpression() && t.isIdentifier(callee.node.property, { name: 'split' }) && args.length === 1 && args[0].isStringLiteral()) {
                separator = args[0].node.value;
            }
            else if (args.length === 2 && args[1].isStringLiteral() && args[1].node.value.length < 5) {
                separator = args[1].node.value;
            }

            let innerCall, outerCall = callPath;
            if (callee.isMemberExpression() && callee.get('object').isCallExpression()) {
                innerCall = callee.get('object');
            }
            else {
                const nestedCallArg = args.find(p =>
                    p.isCallExpression() && p.get('arguments').some(arg => arg.isNumericLiteral() || arg.isUnaryExpression())
                );
                if (nestedCallArg) {
                    innerCall = nestedCallArg;
                }
            }
            
            if (innerCall) {
                const innerNumericArgs = innerCall.get('arguments').filter(p => t.isNumericLiteral(p.node) || t.isUnaryExpression(p.node));
                const outerNumericArgs = outerCall.get('arguments').filter(p => t.isNumericLiteral(p.node) || t.isUnaryExpression(p.node));

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

    if (!separator) console.error('[VERIFY-FAIL] Candidate decoder did not contain a recognizable split operation.');
    if (shuffleOps.length === 0) console.error('[VERIFY-FAIL] Candidate decoder did not contain any recognizable shuffle operations.');
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
                        if (!returnArg.isStringLiteral() || returnArg.node.value.length < 50) return;
                        console.log(`[SOLVE-STR] Found large string function: "${funcPath.node.id?.name || '(anonymous)'}"`);
                        largeStringInfo = { value: returnArg.node.value, path: funcPath };
                        funcPath.stop();
                    }
                });
            },
            exit(path) {
                if (!largeStringInfo || !decoderInfo) {
                    const missing = [];
                    if (!largeStringInfo) missing.push("large string function");
                    if (!decoderInfo) missing.push("decoder IIFE");
                    console.error(`[SOLVE-STR] Aborting. Could not find: ${missing.join(' and ')}.`);
                    return;
                }
                console.log('[SOLVE-STR] Both targets found. Starting deobfuscation...');
                const { value: uriString } = largeStringInfo;
                const { xorKey, separator, shuffleOps, path: decoderPath } = decoderInfo;

                console.log(`[SOLVE-STR] Successfully extracted ${shuffleOps.length} shuffle operations.`);
                const decodedString = decodeURIComponent(uriString);
                let xorResult = '';
                for (let i = 0; i < decodedString.length; i++) {
                    xorResult += String.fromCharCode(decodedString.charCodeAt(i) ^ xorKey.charCodeAt(i % xorKey.length));
                }
                let processedArray = xorResult.split(separator);
                processedArray = correctlyShuffle(processedArray, shuffleOps);
                console.log(`[SOLVE-STR] Decrypted array with ${processedArray.length} elements.`);

                const finalArrayNode = t.arrayExpression(processedArray.map(s => t.stringLiteral(s)));
                const indexIdentifier = t.identifier("index");
                const newFunctionNode = t.functionExpression(null, [indexIdentifier],
                    t.blockStatement([t.returnStatement(t.memberExpression(finalArrayNode, indexIdentifier, true))])
                );

                decoderPath.replaceWith(newFunctionNode);
                console.log('[SOLVE-STR] Replaced decoder IIFE with a new accessor function.');
                largeStringInfo.path.remove();
                console.log('[SOLVE-STR] Removed large string function.');
            },
        },
        CallExpression(path) {
            if (decoderInfo || !largeStringInfo) return;
            const callee = path.get('callee');
            const args = path.get('arguments');
            if (!callee.isFunctionExpression() || args.length !== 1 || !args[0].isStringLiteral()) {
                return;
            }
            const xorKey = args[0].node.value;
            console.log(`[SOLVE-STR] Found candidate decoder IIFE with key "${xorKey}". Verifying...`);
            const ingredients = findDecoderIngredients(callee);

            if (ingredients) {
                console.log(`[SOLVE-STR] Verification successful! Separator: "${ingredients.separator}", Shuffles: ${ingredients.shuffleOps.length}.`);
                decoderInfo = {
                    xorKey,
                    separator: ingredients.separator,
                    shuffleOps: ingredients.shuffleOps,
                    path: path,
                };
                path.stop();
            } else {
                 console.log(`[SOLVE-STR] Candidate with key "${xorKey}" failed verification.`);
            }
        },
    },
};