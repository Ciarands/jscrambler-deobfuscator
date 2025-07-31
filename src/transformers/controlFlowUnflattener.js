import * as t from '@babel/types';
import generator from '@babel/generator';

const generatedArraysMap = new Map();

function generateCyclicalArray(size, offsetValue, key) {
    let matrix = [];
    for (let row = 0; row < size; row++) {
        matrix[row] = [];
    }

    for (let currentRow = 0; currentRow < size; currentRow++) {
        for (let sourceRow = size - 1; sourceRow >= 0; sourceRow--) {
            let keyIndex = 0;
            let baseOffset = key[keyIndex];
            if (baseOffset === 0) continue;
            let modulus = baseOffset;

            let destCol = (sourceRow + offsetValue * currentRow) % modulus;
            if (matrix[sourceRow]) {
                matrix[currentRow][destCol] = matrix[sourceRow];
            }
        }
    }
    return matrix;
}

function processVarDeclarations(statements, hoistedVars) {
    return statements.flatMap((stmt) => {
        if (!t.isVariableDeclaration(stmt, { kind: 'var' })) {
            return [stmt];
        }
        const assignments = [];
        for (const decl of stmt.declarations) {
            if (t.isIdentifier(decl.id)) {
                hoistedVars.add(decl.id.name);
                if (decl.init) {
                    assignments.push(
                        t.expressionStatement(t.assignmentExpression('=', decl.id, decl.init))
                    );
                }
            }
        }
        return assignments;
    });
}

function areVarsEquivalent(node1, node2) {
    if (t.isIdentifier(node1) && t.isIdentifier(node2)) {
        return node1.name === node2.name;
    }
    return t.isNodesEquivalent(node1, node2);
}

export const controlFlowUnflattener = {
    priority: 200,
    visitor: {
        AssignmentExpression(path) {
            const left = path.get('left');
            const right = path.get('right');

            if (!right.isCallExpression()) return;
            const args = right.get('arguments');
            if (
                args.length !== 3 ||
                !args[0].isNumericLiteral() ||
                !args[1].isNumericLiteral() ||
                !args[2].isArrayExpression()
            )
                return;

            const arrayArgElements = args[2].get('elements');
            if (arrayArgElements.length !== 1 || !arrayArgElements[0].isNumericLiteral()) return;

            const callee = right.get('callee');
            if (!callee.isFunction()) return;

            let returnStmtPath;
            callee.get('body').traverse({
                ReturnStatement(p) {
                    if (p.getFunctionParent().node === callee.node) {
                        if (p.get('argument').isObjectExpression()) {
                            returnStmtPath = p;
                            p.stop();
                        }
                    }
                },
            });
            if (!returnStmtPath) return;

            const objectProperties = returnStmtPath.get('argument.properties');
            if (objectProperties.length !== 1 || !objectProperties[0].isObjectProperty()) return;

            const objectPropertyPath = objectProperties[0];
            const propertyKeyNode = objectPropertyPath.get('key');
            if (!propertyKeyNode.isIdentifier()) return;
            const propertyName = propertyKeyNode.node.name;

            const baseIdentifierCode = generator.default(left.node).code;
            const fullKey = `${baseIdentifierCode}.${propertyName}`;

            const arg1 = args[0].node.value;
            const arg2 = args[1].node.value;
            const arg3 = [arrayArgElements[0].node.value];

            console.log(
                ` |-> Found cyclical array generator. Base object: "${baseIdentifierCode}", Property: "${propertyName}"`
            );
            console.log(` |->   - Arguments: size=${arg1}, offset=${arg2}, key=[${arg3}]`);

            const realArray = generateCyclicalArray(arg1, arg2, arg3);
            generatedArraysMap.set(fullKey, realArray);
            console.log(` |->   - In-memory array generated and stored for key: "${fullKey}"`);

            const parentStatement = path.findParent((p) => p.isStatement());
            if (parentStatement) {
                parentStatement.remove();
            }
        },

        ForStatement: {
            exit(path) {
                const { node } = path;
                if (node.update) return;
                if (!t.isBinaryExpression(node.test, { operator: '!==' })) return;
                const stateObjectToIdMap = new Map();
                let nextStateId = 0;

                const resolveAndGetStateId = (node) => {
                    const raw = generator.default(node).code;
                    if (t.isNumericLiteral(node)) {
                        const id = node.value;
                        return { id, raw };
                    }
                    if (t.isMemberExpression(node)) {
                        const indices = [];
                        let baseObjectNode = node;
                        while (
                            t.isMemberExpression(baseObjectNode) &&
                            baseObjectNode.computed &&
                            t.isNumericLiteral(baseObjectNode.property)
                        ) {
                            indices.unshift(baseObjectNode.property.value);
                            baseObjectNode = baseObjectNode.object;
                        }

                        const baseKey = generator.default(baseObjectNode).code;
                        if (generatedArraysMap.has(baseKey)) {
                            try {
                                let stateObj = generatedArraysMap.get(baseKey);
                                for (const index of indices) {
                                    stateObj = stateObj[index];
                                }
                                if (stateObj === undefined) return { id: null, raw };

                                if (stateObjectToIdMap.has(stateObj)) {
                                    return { id: stateObjectToIdMap.get(stateObj), raw };
                                } else {
                                    const newId = nextStateId++;
                                    stateObjectToIdMap.set(stateObj, newId);
                                    return { id: newId, raw };
                                }
                            } catch (e) {
                                return { id: null, raw };
                            }
                        }
                    }
                    return { id: null, raw };
                };

                let stateVar, terminalValueNode;
                const { left, right } = node.test;
                if (t.isIdentifier(left) || t.isMemberExpression(left)) {
                    stateVar = left;
                    terminalValueNode = right;
                } else if (t.isIdentifier(right) || t.isMemberExpression(right)) {
                    stateVar = right;
                    terminalValueNode = left;
                } else {
                    return;
                }

                const terminalInfo = resolveAndGetStateId(terminalValueNode);
                if (terminalInfo.id === null) return;
                const terminalId = terminalInfo.id;

                let switchStatement;
                if (t.isBlockStatement(node.body)) {
                    if (node.body.body.length !== 1 || !t.isSwitchStatement(node.body.body[0]))
                        return;
                    switchStatement = node.body.body[0];
                } else if (t.isSwitchStatement(node.body)) {
                    switchStatement = node.body;
                } else {
                    return;
                }

                if (!areVarsEquivalent(switchStatement.discriminant, stateVar)) return;
                console.log(` |-> Found state machine with terminal value: ${terminalInfo.raw}`);

                let initialStateInfo = null;
                let initializerPath = null;
                let inLoopInitializer = false;

                const findInitialState = (initNode, path) => {
                    let valueInfo = null;
                    if (t.isVariableDeclaration(initNode)) {
                        for (const declarator of initNode.declarations) {
                            if (areVarsEquivalent(declarator.id, stateVar) && declarator.init) {
                                valueInfo = resolveAndGetStateId(declarator.init);
                                if (valueInfo.id !== null) break;
                            }
                        }
                    } else if (t.isExpressionStatement(initNode)) {
                        const expr = initNode.expression;
                        if (
                            t.isAssignmentExpression(expr, { operator: '=' }) &&
                            areVarsEquivalent(expr.left, stateVar)
                        ) {
                            valueInfo = resolveAndGetStateId(expr.right);
                        }
                    }
                    if (valueInfo && valueInfo.id !== null) {
                        initialStateInfo = valueInfo;
                        initializerPath = path;
                        return true;
                    }
                    return false;
                };

                if (node.init && findInitialState(node.init, path)) {
                    inLoopInitializer = true;
                } else {
                    for (let i = path.key - 1; i >= 0; i--) {
                        const siblingPath = path.getSibling(i);
                        if (!siblingPath.node) continue;
                        if (findInitialState(siblingPath.node, siblingPath)) break;
                        const siblingNode = siblingPath.node;
                        if (
                            t.isForStatement(siblingNode) ||
                            t.isWhileStatement(siblingNode) ||
                            t.isDoWhileStatement(siblingNode) ||
                            t.isIfStatement(siblingNode) ||
                            t.isReturnStatement(siblingNode) ||
                            t.isSwitchStatement(siblingNode)
                        ) {
                            break;
                        }
                    }
                }

                if (initialStateInfo === null) {
                    console.log(' |-> Could not determine initial state.');
                    return;
                }
                const initialId = initialStateInfo.id;
                console.log(` |-> Initial state: ${initialStateInfo.raw}`);

                const caseMap = new Map();
                for (const switchCase of switchStatement.cases) {
                    if (!switchCase.test) continue;
                    const caseInfo = resolveAndGetStateId(switchCase.test);
                    if (caseInfo.id === null) continue;
                    const caseBody = switchCase.consequent.filter(
                        (stmt) => !t.isBreakStatement(stmt)
                    );
                    caseMap.set(caseInfo.id, caseBody);
                }
                console.log(` |-> Found ${caseMap.size} switch cases`);

                function getStateUpdateRhs(body) {
                    const lastStmt = body.length > 0 ? body[body.length - 1] : null;
                    if (!lastStmt) return null;
                    if (t.isExpressionStatement(lastStmt)) {
                        const expr = lastStmt.expression;
                        if (t.isSequenceExpression(expr)) {
                            const lastInSequence = expr.expressions[expr.expressions.length - 1];
                            if (
                                t.isAssignmentExpression(lastInSequence, { operator: '=' }) &&
                                areVarsEquivalent(lastInSequence.left, stateVar)
                            ) {
                                return lastInSequence.right;
                            }
                        } else if (
                            t.isAssignmentExpression(expr, { operator: '=' }) &&
                            areVarsEquivalent(expr.left, stateVar)
                        ) {
                            return expr.right;
                        }
                    }
                    if (t.isVariableDeclaration(lastStmt)) {
                        const lastDeclarator =
                            lastStmt.declarations[lastStmt.declarations.length - 1];
                        if (
                            lastDeclarator &&
                            areVarsEquivalent(lastDeclarator.id, stateVar) &&
                            lastDeclarator.init
                        ) {
                            return lastDeclarator.init;
                        }
                    }
                    return null;
                }

                function doesPathLeadTo(startId, targetId, visited) {
                    if (startId === targetId) return true;
                    if (visited.has(startId) || startId === terminalId) return false;
                    visited.add(startId);
                    const body = caseMap.get(startId);
                    if (!body) return false;
                    const stateUpdateRhs = getStateUpdateRhs(body);
                    if (!stateUpdateRhs) return false;
                    const nextStateInfo = resolveAndGetStateId(stateUpdateRhs);
                    if (nextStateInfo.id !== null) {
                        return doesPathLeadTo(nextStateInfo.id, targetId, visited);
                    } else if (t.isConditionalExpression(stateUpdateRhs)) {
                        const consequentInfo = resolveAndGetStateId(stateUpdateRhs.consequent);
                        const alternateInfo = resolveAndGetStateId(stateUpdateRhs.alternate);
                        if (consequentInfo.id === null || alternateInfo.id === null) return false;
                        const consequentPath = doesPathLeadTo(
                            consequentInfo.id,
                            targetId,
                            new Set(visited)
                        );
                        const alternatePath = doesPathLeadTo(
                            alternateInfo.id,
                            targetId,
                            new Set(visited)
                        );
                        return consequentPath || alternatePath;
                    }
                    return false;
                }

                let success = true;
                const hoistedVars = new Set();
                const memo = new Map();

                function unflatten(currentId, recursionStack) {
                    if (currentId === terminalId) return [];
                    if (memo.has(currentId)) return memo.get(currentId);
                    if (recursionStack.has(currentId)) {
                        return [];
                    }
                    const caseBody = caseMap.get(currentId);
                    if (!caseBody) {
                        success = false;
                        return null;
                    }
                    const newRecursionStack = new Set(recursionStack);
                    newRecursionStack.add(currentId);
                    const lastStmtInCase =
                        caseBody.length > 0 ? caseBody[caseBody.length - 1] : null;

                    if (t.isReturnStatement(lastStmtInCase)) {
                        const result = processVarDeclarations(caseBody, hoistedVars);
                        memo.set(currentId, result);
                        return result;
                    }
                    let stateUpdateRhs = getStateUpdateRhs(caseBody);
                    let bodyWithoutUpdate = caseBody;
                    if (stateUpdateRhs) {
                        const lastStmt = caseBody[caseBody.length - 1];
                        bodyWithoutUpdate = caseBody.slice(0, -1);
                        if (
                            t.isExpressionStatement(lastStmt) &&
                            t.isSequenceExpression(lastStmt.expression)
                        ) {
                            const expressions = lastStmt.expression.expressions.slice(0, -1);
                            bodyWithoutUpdate.push(
                                ...expressions.map((e) => t.expressionStatement(e))
                            );
                        } else if (
                            t.isVariableDeclaration(lastStmt) &&
                            lastStmt.declarations.length > 1
                        ) {
                            const newDeclarators = lastStmt.declarations.slice(0, -1);
                            bodyWithoutUpdate.push(
                                t.variableDeclaration(lastStmt.kind, newDeclarators)
                            );
                        }
                    }
                    const processedBody = processVarDeclarations(bodyWithoutUpdate, hoistedVars);
                    let result;
                    if (!stateUpdateRhs) {
                        success = false;
                        return null;
                    }

                    const nextStateInfo = resolveAndGetStateId(stateUpdateRhs);
                    if (nextStateInfo.id !== null) {
                        const nextBlock = unflatten(nextStateInfo.id, newRecursionStack);
                        if (!success) return null;
                        result = [...processedBody, ...nextBlock];
                    } else if (t.isConditionalExpression(stateUpdateRhs)) {
                        const { test, consequent, alternate } = stateUpdateRhs;
                        const trueBranchInfo = resolveAndGetStateId(consequent);
                        const falseBranchInfo = resolveAndGetStateId(alternate);
                        if (trueBranchInfo.id === null || falseBranchInfo.id === null) {
                            success = false;
                            return null;
                        }

                        if (trueBranchInfo.id === currentId) {
                            const loopBody = t.blockStatement(processedBody);
                            const doWhileLoop = t.doWhileStatement(test, loopBody);
                            const afterLoopBody = unflatten(falseBranchInfo.id, newRecursionStack);
                            if (!success) return null;
                            result = [doWhileLoop, ...afterLoopBody];
                        } else if (falseBranchInfo.id === currentId) {
                            const loopBody = t.blockStatement(processedBody);
                            const negatedTest = t.unaryExpression('!', test, true);
                            const doWhileLoop = t.doWhileStatement(negatedTest, loopBody);
                            const afterLoopBody = unflatten(trueBranchInfo.id, newRecursionStack);
                            if (!success) return null;
                            result = [doWhileLoop, ...afterLoopBody];
                        } else {
                            const isWhileLoop = doesPathLeadTo(
                                trueBranchInfo.id,
                                currentId,
                                new Set()
                            );
                            if (isWhileLoop) {
                                const loopBodyNodes = unflatten(
                                    trueBranchInfo.id,
                                    newRecursionStack
                                );
                                if (!success) return null;
                                const afterLoopNodes = unflatten(
                                    falseBranchInfo.id,
                                    newRecursionStack
                                );
                                if (!success) return null;
                                const whileLoop = t.whileStatement(
                                    test,
                                    t.blockStatement(loopBodyNodes)
                                );
                                result = [...processedBody, whileLoop, ...afterLoopNodes];
                            } else {
                                const trueBranchBody = unflatten(
                                    trueBranchInfo.id,
                                    newRecursionStack
                                );
                                const falseBranchBody = unflatten(
                                    falseBranchInfo.id,
                                    newRecursionStack
                                );
                                if (!success) return null;
                                const ifStatement = t.ifStatement(
                                    test,
                                    t.blockStatement(trueBranchBody),
                                    falseBranchBody.length > 0
                                        ? t.blockStatement(falseBranchBody)
                                        : null
                                );
                                result = [...processedBody, ifStatement];
                            }
                        }
                    } else {
                        success = false;
                        return null;
                    }
                    memo.set(currentId, result);
                    return result;
                }

                const unflattenedBody = unflatten(initialId, new Set());

                if (success && unflattenedBody) {
                    const newNodes = [];
                    if (hoistedVars.size > 0) {
                        const declarators = Array.from(hoistedVars).map((varName) =>
                            t.variableDeclarator(t.identifier(varName))
                        );
                        newNodes.push(t.variableDeclaration('var', declarators));
                    }
                    newNodes.push(...unflattenedBody);
                    console.log(
                        ` |-> Successfully unflattened state machine. Generated ${newNodes.length} nodes.`
                    );
                    path.replaceWithMultiple(newNodes);
                    if (initializerPath && !inLoopInitializer) {
                        if (initializerPath.isVariableDeclaration()) {
                            const declarators = initializerPath.node.declarations;
                            if (declarators.length === 1) {
                                initializerPath.remove();
                            } else {
                                const declIndex = declarators.findIndex((d) =>
                                    areVarsEquivalent(d.id, stateVar)
                                );
                                if (declIndex > -1) declarators.splice(declIndex, 1);
                            }
                        } else {
                            initializerPath.remove();
                        }
                    }
                } else {
                    console.log(' |-> Failed to unflatten state machine. Reverting changes.');
                }
            },
        },
    },
};
