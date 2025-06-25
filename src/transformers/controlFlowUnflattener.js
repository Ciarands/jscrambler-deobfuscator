import * as t from '@babel/types';

function processVarDeclarations(statements, hoistedVars) {
    return statements.flatMap(stmt => {
        if (!t.isVariableDeclaration(stmt, { kind: 'var' })) {
            return [stmt];
        }
        const assignments = [];
        for (const decl of stmt.declarations) {
            if (t.isIdentifier(decl.id)) {
                hoistedVars.add(decl.id.name);
                if (decl.init) {
                    assignments.push(t.expressionStatement(t.assignmentExpression('=', decl.id, decl.init)));
                }
            }
        }
        return assignments;
    });
}

export const controlFlowUnflattener = {
    visitor: {
        ForStatement: {
            exit(path) {
                const { node } = path;
                if (node.init || node.update) return;
                if (!t.isBinaryExpression(node.test, { operator: '!==' })) return;
                const stateVar = node.test.left;
                if (!t.isIdentifier(stateVar) && !t.isMemberExpression(stateVar)) return;
                const terminalValueNode = node.test.right;
                if (!t.isNumericLiteral(terminalValueNode)) return;
                const terminalValue = terminalValueNode.value;
                if (!t.isBlockStatement(node.body) || node.body.body.length !== 1) return;
                const switchStatement = node.body.body[0];
                if (!t.isSwitchStatement(switchStatement) || !t.isNodesEquivalent(switchStatement.discriminant, stateVar)) return;

                console.log(`[UNFLATTEN] Found state machine with terminal value: ${terminalValue}`);

                let initialState = null;
                let initializerPath = null;
                for (let i = path.key - 1; i >= 0; i--) {
                    const siblingPath = path.getSibling(i);
                    if (!siblingPath.node) continue;
                    if (siblingPath.isVariableDeclaration()) {
                        const declarator = siblingPath.node.declarations.find(d => t.isNodesEquivalent(d.id, stateVar) && d.init && t.isNumericLiteral(d.init));
                        if (declarator) {
                            initialState = declarator.init.value;
                            initializerPath = siblingPath;
                            break;
                        }
                    } else if (siblingPath.isExpressionStatement()) {
                        const expr = siblingPath.node.expression;
                        if (t.isAssignmentExpression(expr, { operator: '=' }) && t.isNodesEquivalent(expr.left, stateVar) && t.isNumericLiteral(expr.right)) {
                            initialState = expr.right.value;
                            initializerPath = siblingPath;
                            break;
                        }
                    } else if (!siblingPath.isFunctionDeclaration()) {
                        break;
                    }
                }
                if (initialState === null) return;

                console.log(`[UNFLATTEN] Initial state: ${initialState}`);

                const caseMap = new Map();
                for (const switchCase of switchStatement.cases) {
                    if (!switchCase.test || !t.isNumericLiteral(switchCase.test)) return;
                    const caseBody = switchCase.consequent.filter(stmt => !t.isBreakStatement(stmt));
                    caseMap.set(switchCase.test.value, caseBody);
                }

                console.log(`[UNFLATTEN] Found ${caseMap.size} switch cases`);

                let success = true;
                const hoistedVars = new Set();
                const memo = new Map(); // Cache results for each state

                function unflatten(currentState, recursionStack) {
                    if (currentState === terminalValue) {
                        return [];
                    }
                    if (memo.has(currentState)) {
                        return memo.get(currentState);
                    }
                    if (recursionStack.has(currentState)) {
                        return [];
                    }

                    const caseBody = caseMap.get(currentState);
                    if (!caseBody) {
                        success = false;
                        return null;
                    }
        
                    const newRecursionStack = new Set(recursionStack);
                    newRecursionStack.add(currentState);
                    const lastStmt = caseBody[caseBody.length - 1];
                    let stateUpdateRhs = null;
                    let bodyWithoutUpdate = caseBody;

                    if (t.isExpressionStatement(lastStmt) && t.isAssignmentExpression(lastStmt.expression, { operator: '=' }) && t.isNodesEquivalent(lastStmt.expression.left, stateVar)) {
                        stateUpdateRhs = lastStmt.expression.right;
                        bodyWithoutUpdate = caseBody.slice(0, -1);
                    }

                    const processedBody = processVarDeclarations(bodyWithoutUpdate, hoistedVars);
                    
                    let result;
                    if (!stateUpdateRhs) {
                        result = processedBody;
                    } else if (t.isNumericLiteral(stateUpdateRhs)) {
                        const nextBlock = unflatten(stateUpdateRhs.value, newRecursionStack);
                        if (!success) return null;
                        result = [...processedBody, ...nextBlock];
                    } else if (t.isConditionalExpression(stateUpdateRhs)) {
                        const { test, consequent, alternate } = stateUpdateRhs;
                        if (!t.isNumericLiteral(consequent) || !t.isNumericLiteral(alternate)) {
                            success = false;
                            return null;
                        }

                        const trueBranchBody = unflatten(consequent.value, newRecursionStack);
                        if (!success) return null;
                        const falseBranchBody = unflatten(alternate.value, newRecursionStack);
                        if (!success) return null;

                        if (trueBranchBody.length === 0 && newRecursionStack.has(consequent.value)) {
                            const whileStatement = t.whileStatement(test, t.blockStatement(processedBody));
                            result = [whileStatement, ...falseBranchBody];
                        } else {
                            const ifStatement = t.ifStatement(
                                test,
                                t.blockStatement(trueBranchBody),
                                falseBranchBody.length > 0 ? t.blockStatement(falseBranchBody) : null
                            );
                            result = [...processedBody, ifStatement];
                        }
                    } else {
                        success = false;
                        return null;
                    }
                    
                    memo.set(currentState, result);
                    return result;
                }
                
                const unflattenedBody = unflatten(initialState, new Set());

                if (success) {
                    const newNodes = [];
                    if (hoistedVars.size > 0) {
                        const declarators = Array.from(hoistedVars).map(varName => t.variableDeclarator(t.identifier(varName)));
                        newNodes.push(t.variableDeclaration('var', declarators));
                    }
                    newNodes.push(...unflattenedBody);

                    console.log(`[UNFLATTEN] Successfully unflattened state machine. Generated ${newNodes.length} nodes.`);
                    path.replaceWithMultiple(newNodes);
                    
                    if (initializerPath.isVariableDeclaration()) {
                        const declarators = initializerPath.node.declarations;
                        const declIndex = declarators.findIndex(d => t.isNodesEquivalent(d.id, stateVar));
                        if (declIndex !== -1) {
                            if (declarators.length === 1) {
                                initializerPath.remove();
                            } else {
                                declarators.splice(declIndex, 1);
                            }
                        }
                    } else {
                        initializerPath.remove();
                    }
                } else {
                    console.log('[UNFLATTEN] Failed to unflatten state machine');
                }
            }
        }
    }
};