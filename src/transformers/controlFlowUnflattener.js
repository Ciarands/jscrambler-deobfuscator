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

function areVarsEquivalent(node1, node2) {
    if (t.isIdentifier(node1) && t.isIdentifier(node2)) {
        return node1.name === node2.name;
    }
    return t.isNodesEquivalent(node1, node2);
}

export const controlFlowUnflattener = {
    priority: 100,
    visitor: {
        ForStatement: {
            exit(path) {
                const { node } = path;
                if (node.update) return;

                if (!t.isBinaryExpression(node.test, { operator: '!==' })) return;

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

                if (!t.isNumericLiteral(terminalValueNode)) return;
                const terminalValue = terminalValueNode.value;

                let switchStatement;
                if (t.isBlockStatement(node.body)) {
                    if (node.body.body.length !== 1 || !t.isSwitchStatement(node.body.body[0])) return;
                    switchStatement = node.body.body[0];
                } else if (t.isSwitchStatement(node.body)) {
                    switchStatement = node.body;
                } else {
                    return;
                }

                if (!areVarsEquivalent(switchStatement.discriminant, stateVar)) return;
                console.log(` |-> Found state machine with terminal value: ${terminalValue}`);

                let initialState = null;
                let initializerPath = null;
                let inLoopInitializer = false;

                if (t.isVariableDeclaration(node.init)) {
                    for(const declarator of node.init.declarations){
                         if (areVarsEquivalent(declarator.id, stateVar) && declarator.init && t.isNumericLiteral(declarator.init)) {
                            initialState = declarator.init.value;
                            inLoopInitializer = true;
                            break;
                        }
                    }
                }

                if (initialState === null) {
                    for (let i = path.key - 1; i >= 0; i--) {
                        const siblingPath = path.getSibling(i);
                        if (!siblingPath.node) continue;
                        if (siblingPath.isVariableDeclaration()) {
                             for(const declarator of siblingPath.node.declarations){
                                if (areVarsEquivalent(declarator.id, stateVar) && declarator.init && t.isNumericLiteral(declarator.init)) {
                                    initialState = declarator.init.value;
                                    initializerPath = siblingPath;
                                    break;
                                }
                            }
                            if(initialState !== null) break;
                        } else if (siblingPath.isExpressionStatement()) {
                            const expr = siblingPath.node.expression;
                            if (t.isAssignmentExpression(expr, { operator: '=' }) && areVarsEquivalent(expr.left, stateVar) && t.isNumericLiteral(expr.right)) {
                                initialState = expr.right.value;
                                initializerPath = siblingPath;
                                break;
                            }
                        } else if (!siblingPath.isFunctionDeclaration()) {
                            break;
                        }
                    }
                }

                if (initialState === null) {
                    console.log(' |-> Could not determine initial state.');
                    return;
                }
                console.log(` |-> Initial state: ${initialState}`);

                const caseMap = new Map();
                for (const switchCase of switchStatement.cases) {
                    if (!switchCase.test || !t.isNumericLiteral(switchCase.test)) continue;
                    const caseBody = switchCase.consequent.filter(stmt => !t.isBreakStatement(stmt));
                    caseMap.set(switchCase.test.value, caseBody);
                }
                console.log(` |-> Found ${caseMap.size} switch cases`);
                
                function getStateUpdateRhs(body) {
                    const lastStmt = body.length > 0 ? body[body.length - 1] : null;
                    if (!lastStmt) return null;

                    // --- Fingerprint: Assignment in an ExpressionStatement ---
                    if (t.isExpressionStatement(lastStmt)) {
                        const expr = lastStmt.expression;
                        if (t.isSequenceExpression(expr)) {
                            const lastInSequence = expr.expressions[expr.expressions.length - 1];
                            if (t.isAssignmentExpression(lastInSequence, { operator: '=' }) && areVarsEquivalent(lastInSequence.left, stateVar)) {
                                return lastInSequence.right;
                            }
                        } else if (t.isAssignmentExpression(expr, { operator: '=' }) && areVarsEquivalent(expr.left, stateVar)) {
                            return expr.right;
                        }
                    }

                    // --- Fingerprint: Assignment as the initializer of the last declarator in a VariableDeclaration ---
                    if (t.isVariableDeclaration(lastStmt)) {
                        const lastDeclarator = lastStmt.declarations[lastStmt.declarations.length - 1];
                        if (lastDeclarator && areVarsEquivalent(lastDeclarator.id, stateVar) && lastDeclarator.init) {
                            return lastDeclarator.init;
                        }
                    }

                    return null;
                }
                
                function doesPathLeadTo(startState, targetState, visited) {
                    if (startState === targetState) return true;
                    if (visited.has(startState) || startState === terminalValue) return false;
                    
                    visited.add(startState);
                    
                    const body = caseMap.get(startState);
                    if (!body) return false;
                    
                    const stateUpdateRhs = getStateUpdateRhs(body);
                    if (!stateUpdateRhs) return false;

                    if (t.isNumericLiteral(stateUpdateRhs)) {
                        return doesPathLeadTo(stateUpdateRhs.value, targetState, visited);
                    } else if (t.isConditionalExpression(stateUpdateRhs)) {
                        if (!t.isNumericLiteral(stateUpdateRhs.consequent) || !t.isNumericLiteral(stateUpdateRhs.alternate)) {
                            return false; // cannot statically analyze
                        }
                        const consequentPath = doesPathLeadTo(stateUpdateRhs.consequent.value, targetState, new Set(visited));
                        const alternatePath = doesPathLeadTo(stateUpdateRhs.alternate.value, targetState, new Set(visited));
                        return consequentPath || alternatePath;
                    }
                    
                    return false;
                }

                let success = true;
                const hoistedVars = new Set();
                const memo = new Map();

                function unflatten(currentState, recursionStack) {
                    if (currentState === terminalValue) return [];
                    if (memo.has(currentState)) return memo.get(currentState);
                    if (recursionStack.has(currentState)) {
                        console.log(` |-> Detected unresolved loop at state ${currentState}. Bailing on this path.`);
                        return [];
                    }

                    const caseBody = caseMap.get(currentState);
                    if (!caseBody) { success = false; return null; }

                    const newRecursionStack = new Set(recursionStack);
                    newRecursionStack.add(currentState);

                    const lastStmtInCase = caseBody.length > 0 ? caseBody[caseBody.length - 1] : null;

                    if (t.isReturnStatement(lastStmtInCase)) {
                        console.log(` |-> Found return statement at state ${currentState}`);
                        const result = processVarDeclarations(caseBody, hoistedVars);
                        memo.set(currentState, result);
                        return result;
                    }

                    let stateUpdateRhs = getStateUpdateRhs(caseBody);
                    let bodyWithoutUpdate = caseBody;

                    if (stateUpdateRhs) {
                        const lastStmt = caseBody[caseBody.length - 1];
                        bodyWithoutUpdate = caseBody.slice(0, -1);
                        if (t.isExpressionStatement(lastStmt) && t.isSequenceExpression(lastStmt.expression)) {
                            const expressions = lastStmt.expression.expressions.slice(0, -1);
                            bodyWithoutUpdate.push(...expressions.map(e => t.expressionStatement(e)));
                        } else if (t.isVariableDeclaration(lastStmt) && lastStmt.declarations.length > 1) {
                            // `var x = 1, state = 123;` becomes `var x = 1;`
                            const newDeclarators = lastStmt.declarations.slice(0, -1);
                            bodyWithoutUpdate.push(t.variableDeclaration(lastStmt.kind, newDeclarators));
                        }
                    }

                    const processedBody = processVarDeclarations(bodyWithoutUpdate, hoistedVars);

                    let result;
                    if (!stateUpdateRhs) {
                        // no state update and no return, something is wrong.
                        success = false;
                        return null;
                    } else if (t.isNumericLiteral(stateUpdateRhs)) {
                        const nextBlock = unflatten(stateUpdateRhs.value, newRecursionStack);
                        if (!success) return null;
                        result = [...processedBody, ...nextBlock];
                    } else if (t.isConditionalExpression(stateUpdateRhs)) {
                        const { test, consequent, alternate } = stateUpdateRhs;
                        if (!t.isNumericLiteral(consequent) || !t.isNumericLiteral(alternate)) {
                            console.log(' |-> Conditional state update with non-literal branches, cannot unflatten.');
                            success = false; return null;
                        }
                        const trueBranchState = consequent.value;
                        const falseBranchState = alternate.value;

                        // --- Fingerprint: do-while loop ---
                        if (trueBranchState === currentState) {
                            const loopBody = t.blockStatement(processedBody);
                            const doWhileLoop = t.doWhileStatement(test, loopBody);
                            const afterLoopBody = unflatten(falseBranchState, newRecursionStack);
                            if (!success) return null;
                            result = [doWhileLoop, ...afterLoopBody];
                            memo.set(currentState, result);
                            return result;
                        }
                        if (falseBranchState === currentState) {
                            const loopBody = t.blockStatement(processedBody);
                            const negatedTest = t.unaryExpression('!', test, true);
                            const doWhileLoop = t.doWhileStatement(negatedTest, loopBody);
                            const afterLoopBody = unflatten(trueBranchState, newRecursionStack);
                            if (!success) return null;
                            result = [doWhileLoop, ...afterLoopBody];
                            memo.set(currentState, result);
                            return result;
                        }

                        // --- Fingerprint: while loop vs. if statement ---
                        const isWhileLoop = doesPathLeadTo(trueBranchState, currentState, new Set());
                        
                        if (isWhileLoop) {
                            console.log(` |-> Identified while-loop at state ${currentState}`);
                            const loopBodyNodes = unflatten(trueBranchState, newRecursionStack);
                            if (!success) return null;
                            const afterLoopNodes = unflatten(falseBranchState, newRecursionStack);
                            if (!success) return null;

                            const whileLoop = t.whileStatement(test, t.blockStatement(loopBodyNodes));
                            result = [...processedBody, whileLoop, ...afterLoopNodes];
                        } else {
                            const trueBranchBody = unflatten(trueBranchState, newRecursionStack);
                            if (!success) return null;
                            const falseBranchBody = unflatten(falseBranchState, newRecursionStack);
                            if (!success) return null;

                            const ifStatement = t.ifStatement(
                                test,
                                t.blockStatement(trueBranchBody),
                                falseBranchBody.length > 0 ? t.blockStatement(falseBranchBody) : null
                            );
                            result = [...processedBody, ifStatement];
                        }

                    } else {
                        console.log(' |-> Unhandled state update type.');
                        success = false;
                        return null;
                    }

                    memo.set(currentState, result);
                    return result;
                }

                const unflattenedBody = unflatten(initialState, new Set());
                
                if (success && unflattenedBody) {
                    const newNodes = [];
                    if (hoistedVars.size > 0) {
                        const declarators = Array.from(hoistedVars).map(varName => t.variableDeclarator(t.identifier(varName)));
                        newNodes.push(t.variableDeclaration('var', declarators));
                    }
                    newNodes.push(...unflattenedBody);

                    console.log(` |-> Successfully unflattened state machine. Generated ${newNodes.length} nodes.`);
                    path.replaceWithMultiple(newNodes);

                    if (initializerPath && !inLoopInitializer) {
                        if (initializerPath.isVariableDeclaration()) {
                            const declarators = initializerPath.node.declarations;
                            const declIndex = declarators.findIndex(d => areVarsEquivalent(d.id, stateVar));
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
                    }
                } else {
                    console.log(' |-> Failed to unflatten state machine. Reverting changes.');
                }
            }
        }
    }
};