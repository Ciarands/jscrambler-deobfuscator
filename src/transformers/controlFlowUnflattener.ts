import type { Visitor } from "@babel/traverse";
import type { Statement, Node } from "@babel/types";
import * as t from "@babel/types";
import generator from "@babel/generator";
import type { Transformer } from "../types.js";
import { TransformerPriority } from "../types.js";

// TODO: Complete cyclical-array flattening variant impl

let generatedArraysMap: Map<string, any> | null = null;
const fingerprintedKeys = new Set<string>();
let numericTotal = 0;
let numericUndone = 0;
let cycTotal = 0;
let cycUndone = 0;

function generateCyclicalArray(size: number, offsetValue: number, key: number[]): any[] {
    const matrix: any[] = [];
    for (let row = 0; row < size; row++) {
        matrix[row] = [];
    }

    for (let currentRow = 0; currentRow < size; currentRow++) {
        for (let sourceRow = size - 1; sourceRow >= 0; sourceRow--) {
            let keyIndex = 0;
            const baseOffset = key[keyIndex];
            if (baseOffset === 0) continue;
            const modulus = baseOffset;

            const destCol = (sourceRow + offsetValue * currentRow) % modulus;
            if (matrix[sourceRow]) {
                matrix[currentRow][destCol] = matrix[sourceRow];
            }
        }
    }
    return matrix;
}

function processVarDeclarations(statements: readonly Statement[], hoistedVars: Set<string>): Statement[] {
    return statements.flatMap((stmt) => {
        if (!t.isVariableDeclaration(stmt, { kind: "var" })) {
            return [stmt];
        }
        const assignments: Statement[] = [];
        for (const decl of stmt.declarations) {
            if (t.isIdentifier(decl.id)) {
                hoistedVars.add(decl.id.name);
                if (decl.init) {
                    assignments.push(t.expressionStatement(t.assignmentExpression("=", decl.id, decl.init)));
                }
            }
        }
        return assignments;
    });
}

function areVarsEquivalent(node1: Node, node2: Node): boolean {
    if (t.isIdentifier(node1) && t.isIdentifier(node2)) {
        return node1.name === node2.name;
    }
    return t.isNodesEquivalent(node1, node2);
}

const visitor: Visitor<any> = {
    Program: {
        enter(_path, state) {
            generatedArraysMap = new Map();
            fingerprintedKeys.clear();
            numericTotal = 0;
            numericUndone = 0;
            cycTotal = 0;
            cycUndone = 0;
            state?.logger?.debug?.("[CFU] Program enter - init per-file state");
        },
        exit(path, state) {
            const totalMachines = numericTotal + cycTotal;
            const totalUndone = numericUndone + cycUndone;
            const successPct = totalMachines > 0 ? Math.round((totalUndone / totalMachines) * 100) : 0;
            const generatorName = fingerprintedKeys.size > 0 ? `\`${Array.from(fingerprintedKeys)[0]}\`` : "undefined";
            const table = ` ControlFlowUnflattner:\n\t- ${numericTotal} numeric literal state machines found\n\t\t- ${numericUndone} patterns undone\n\t- ${cycTotal} cyclical-array state machines found\n\t\t- ${cycUndone} patterns undone\n\t- ${totalUndone} total patterns undone / ${totalMachines} total CFF state machines (${successPct}%)\n\t- Cyclical-array generator: ${generatorName} `;
            t.addComment(path.node, "leading", table, false);

            generatedArraysMap = null;
            fingerprintedKeys.clear();
            state?.logger?.debug?.("[CFU] Program exit");
        },
    },

    AssignmentExpression(path, state) {
        const left = path.get("left");
        const right = path.get("right");

        if (!right.isCallExpression()) return;
        const args = right.get("arguments");
        if (args.length !== 3 || !args[0].isNumericLiteral() || !args[1].isNumericLiteral() || !args[2].isArrayExpression()) return;

        const arrayArgElements = args[2].get("elements");
        if (arrayArgElements.length !== 1 || !arrayArgElements[0].isNumericLiteral()) return;

        const callee = right.get("callee");
        if (!callee.isFunction()) return;

        let returnStmtPath: any;
        callee.get("body").traverse({
            ReturnStatement(p) {
                if (p.getFunctionParent().node === callee.node) {
                    if (p.get("argument").isObjectExpression()) {
                        returnStmtPath = p;
                        p.stop();
                    }
                }
            },
        });
        if (!returnStmtPath) return;

        const objectProperties = returnStmtPath.get("argument.properties");
        if (objectProperties.length !== 1 || !objectProperties[0].isObjectProperty()) return;

        const objectPropertyPath = objectProperties[0];
        const propertyKeyNode = objectPropertyPath.get("key");
        if (!propertyKeyNode.isIdentifier()) return;
        const propertyName = propertyKeyNode.node.name;

        const baseIdentifierCode = generator.default(left.node).code;
        const fullKey = `${baseIdentifierCode}.${propertyName}`;

        const arg1 = args[0].node.value;
        const arg2 = args[1].node.value;
        const arg3 = [arrayArgElements[0].node.value];

        if (generatedArraysMap) {
            const realArray = generateCyclicalArray(arg1, arg2, arg3);
            generatedArraysMap.set(fullKey, realArray);
            fingerprintedKeys.add(fullKey);
            state?.logger?.debug?.(`[CFU] Generated cyclical array for ${fullKey} (size=${arg1}, offset=${arg2}, key=[${arg3.join(",")}])`);
        }

        const parentStatement = path.findParent((p) => p.isStatement());
        if (parentStatement) {
            parentStatement.remove();
        }
    },

    ForStatement: {
        exit(path, state) {
            const { node } = path;
            if (node.update) return;
            if (!t.isBinaryExpression(node.test, { operator: "!==" })) return;
            const stateObjectToIdMap = new Map<any[], number>();
            let nextStateId = 0;
            let usedCyclicalRef = false;

            const resolveAndGetStateId = (n: Node): { id: number | null; raw: string } => {
                const raw = generator.default(n).code;
                if (t.isNumericLiteral(n)) {
                    return { id: n.value, raw };
                }
                if (t.isMemberExpression(n)) {
                    const indices: number[] = [];
                    let baseObjectNode: Node = n;
                    while (t.isMemberExpression(baseObjectNode) && baseObjectNode.computed && t.isNumericLiteral(baseObjectNode.property)) {
                        indices.unshift(baseObjectNode.property.value);
                        baseObjectNode = baseObjectNode.object;
                    }

                    const baseKey = generator.default(baseObjectNode).code;
                    if (generatedArraysMap && generatedArraysMap.has(baseKey)) {
                        try {
                            let stateObj: any[] = generatedArraysMap.get(baseKey);
                            for (const index of indices) {
                                stateObj = stateObj[index];
                            }
                            if (stateObj === undefined) return { id: null, raw };
                            usedCyclicalRef = true;

                            if (stateObjectToIdMap.has(stateObj)) {
                                return { id: stateObjectToIdMap.get(stateObj)!, raw };
                            } else {
                                const newId = nextStateId++;
                                stateObjectToIdMap.set(stateObj, newId);
                                return { id: newId, raw };
                            }
                        } catch {
                            return { id: null, raw };
                        }
                    }
                }
                return { id: null, raw };
            };

            let stateVar: Node, terminalValueNode: Node;
            const { left, right } = node.test as t.BinaryExpression;
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

            let switchStatement: t.SwitchStatement | undefined;
            if (t.isBlockStatement(node.body)) {
                if (node.body.body.length !== 1 || !t.isSwitchStatement(node.body.body[0])) return;
                switchStatement = node.body.body[0] as t.SwitchStatement;
            } else if (t.isSwitchStatement(node.body)) {
                switchStatement = node.body as t.SwitchStatement;
            } else {
                return;
            }

            if (!areVarsEquivalent(switchStatement.discriminant, stateVar)) return;

            let initialStateInfo: { id: number; raw: string } | null = null;
            let initializerPath: any = null;
            let inLoopInitializer = false;

            const findInitialState = (initNode: Node, p: any): boolean => {
                let valueInfo: { id: number | null; raw: string } | null = null;
                if (t.isVariableDeclaration(initNode)) {
                    for (const declarator of initNode.declarations) {
                        if (areVarsEquivalent(declarator.id, stateVar as any) && declarator.init) {
                            valueInfo = resolveAndGetStateId(declarator.init);
                            if (valueInfo.id !== null) break;
                        }
                    }
                } else if (t.isExpressionStatement(initNode)) {
                    const expr = initNode.expression;
                    if (t.isAssignmentExpression(expr, { operator: "=" }) && areVarsEquivalent(expr.left, stateVar as any)) {
                        valueInfo = resolveAndGetStateId(expr.right);
                    }
                }
                if (valueInfo && valueInfo.id !== null) {
                    initialStateInfo = valueInfo as any;
                    initializerPath = p;
                    return true;
                }
                return false;
            };

            if (node.init && findInitialState(node.init as any, path)) {
                inLoopInitializer = true;
            } else {
                for (let i = (path.key as number) - 1; i >= 0; i--) {
                    const siblingPath: any = (path as any).getSibling(i);
                    if (!siblingPath.node) continue;
                    if (findInitialState(siblingPath.node, siblingPath)) break;
                    const siblingNode: any = siblingPath.node;
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
                return;
            }
            const initialId = initialStateInfo.id;

            const caseMap = new Map<number, Statement[]>();
            for (const switchCase of switchStatement.cases) {
                if (!switchCase.test) continue;
                const caseInfo = resolveAndGetStateId(switchCase.test);
                if (caseInfo.id === null) continue;
                const caseBody = switchCase.consequent.filter((stmt) => !t.isBreakStatement(stmt));
                caseMap.set(caseInfo.id, caseBody);
            }
            state?.logger?.debug?.(`[CFU] SM cases: ${caseMap.size}`);

            const variant = usedCyclicalRef ? "cyclical-array" : "numeric";
            if (variant === "cyclical-array") {
                cycTotal++;
            } else {
                numericTotal++;
            }

            function getStateUpdateRhs(body: readonly Statement[]): Node | null {
                const lastStmt = body.length > 0 ? body[body.length - 1] : null;
                if (!lastStmt) return null;
                if (t.isExpressionStatement(lastStmt)) {
                    const expr = lastStmt.expression;
                    if (t.isSequenceExpression(expr)) {
                        const lastInSequence = expr.expressions[expr.expressions.length - 1];
                        if (t.isAssignmentExpression(lastInSequence, { operator: "=" }) && areVarsEquivalent(lastInSequence.left, stateVar as any)) {
                            return lastInSequence.right;
                        }
                    } else if (t.isAssignmentExpression(expr, { operator: "=" }) && areVarsEquivalent(expr.left, stateVar as any)) {
                        return expr.right;
                    }
                }
                if (t.isVariableDeclaration(lastStmt)) {
                    const lastDeclarator = lastStmt.declarations[lastStmt.declarations.length - 1];
                    if (lastDeclarator && areVarsEquivalent(lastDeclarator.id, stateVar as any) && lastDeclarator.init) {
                        return lastDeclarator.init;
                    }
                }
                return null;
            }

            function doesPathLeadTo(startId: number, targetId: number, visited: Set<number>): boolean {
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
                    const consequentPath = doesPathLeadTo(consequentInfo.id, targetId, new Set(visited));
                    const alternatePath = doesPathLeadTo(alternateInfo.id, targetId, new Set(visited));
                    return consequentPath || alternatePath;
                }
                return false;
            }

            let success = true;
            const hoistedVars = new Set<string>();
            const memo = new Map<number, Statement[] | null>();

            function unflatten(currentId: number, recursionStack: Set<number>): Statement[] | null {
                if (currentId === terminalId) return [];
                if (memo.has(currentId)) return memo.get(currentId)!;
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
                const lastStmtInCase = caseBody.length > 0 ? caseBody[caseBody.length - 1] : null;

                if (t.isReturnStatement(lastStmtInCase)) {
                    const result = processVarDeclarations(caseBody, hoistedVars);
                    memo.set(currentId, result);
                    return result;
                }
                const stateUpdateRhs = getStateUpdateRhs(caseBody);
                let bodyWithoutUpdate = caseBody;
                if (stateUpdateRhs) {
                    const lastStmt = caseBody[caseBody.length - 1];
                    bodyWithoutUpdate = caseBody.slice(0, -1);
                    if (t.isExpressionStatement(lastStmt) && t.isSequenceExpression(lastStmt.expression)) {
                        const expressions = lastStmt.expression.expressions.slice(0, -1);
                        bodyWithoutUpdate.push(...expressions.map((e) => t.expressionStatement(e)));
                    } else if (t.isVariableDeclaration(lastStmt) && lastStmt.declarations.length > 1) {
                        const newDeclarators = lastStmt.declarations.slice(0, -1);
                        bodyWithoutUpdate.push(t.variableDeclaration(lastStmt.kind, newDeclarators));
                    }
                }
                const processedBody = processVarDeclarations(bodyWithoutUpdate, hoistedVars);
                let result: Statement[] | null;
                if (!stateUpdateRhs) {
                    success = false;
                    return null;
                }

                const nextStateInfo = resolveAndGetStateId(stateUpdateRhs);
                if (nextStateInfo.id !== null) {
                    const nextBlock = unflatten(nextStateInfo.id, new Set(newRecursionStack));
                    if (!success || !nextBlock) return null;
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
                        const afterLoopBody = unflatten(falseBranchInfo.id, new Set(newRecursionStack));
                        if (!success || !afterLoopBody) return null;
                        result = [doWhileLoop, ...afterLoopBody];
                    } else if (falseBranchInfo.id === currentId) {
                        const loopBody = t.blockStatement(processedBody);
                        const negatedTest = t.unaryExpression("!", test, true);
                        const doWhileLoop = t.doWhileStatement(negatedTest, loopBody);
                        const afterLoopBody = unflatten(trueBranchInfo.id, new Set(newRecursionStack));
                        if (!success || !afterLoopBody) return null;
                        result = [doWhileLoop, ...afterLoopBody];
                    } else {
                        const isWhileLoop = doesPathLeadTo(trueBranchInfo.id, currentId, new Set());
                        if (isWhileLoop) {
                            const loopBodyNodes = unflatten(trueBranchInfo.id, new Set(newRecursionStack));
                            if (!success || !loopBodyNodes) return null;
                            const afterLoopNodes = unflatten(falseBranchInfo.id, new Set(newRecursionStack));
                            if (!success || !afterLoopNodes) return null;
                            const whileLoop = t.whileStatement(test, t.blockStatement(loopBodyNodes));
                            result = [...processedBody, whileLoop, ...afterLoopNodes];
                        } else {
                            const trueBranchBody = unflatten(trueBranchInfo.id, new Set(newRecursionStack));
                            const falseBranchBody = unflatten(falseBranchInfo.id, new Set(newRecursionStack));
                            if (!success || !trueBranchBody || !falseBranchBody) return null;
                            const ifStatement = t.ifStatement(test, t.blockStatement(trueBranchBody), falseBranchBody.length > 0 ? t.blockStatement(falseBranchBody) : null);
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
                const newNodes: Statement[] = [];
                if (hoistedVars.size > 0) {
                    const declarators = Array.from(hoistedVars).map((varName) => t.variableDeclarator(t.identifier(varName)));
                    newNodes.push(t.variableDeclaration("var", declarators));
                }
                newNodes.push(...unflattenedBody);
                path.replaceWithMultiple(newNodes);
                if (variant === "cyclical-array") {
                    cycUndone++;
                    state?.logger?.debug?.(`[CFU] Successfully unflattened CFF (variant=${variant}) to ${newNodes.length} node(s)`);
                } else {
                    numericUndone++;
                    state?.logger?.debug?.(`[CFU] Successfully unflattened CFF (variant=${variant}) to ${newNodes.length} node(s)`);
                }
                if (initializerPath && !inLoopInitializer) {
                    if (initializerPath.isVariableDeclaration()) {
                        const declarators = initializerPath.node.declarations;
                        if (declarators.length === 1) {
                            initializerPath.remove();
                        } else {
                            const declIndex = declarators.findIndex((d: any) => areVarsEquivalent(d.id, stateVar));
                            if (declIndex > -1) declarators.splice(declIndex, 1);
                        }
                    } else {
                        initializerPath.remove();
                    }
                }
            } else {
                state?.logger?.debug?.(`[CFU] Failed to unflatten CFF (variant=${variant}) - leaving original code`);
            }
        },
    },
};

export const controlFlowUnflattener: Transformer = {
    name: "controlFlowUnflattener",
    description: "Detects and reconstructs control flow",
    priority: TransformerPriority.CONTROL_FLOW_UNFLATTENER,
    visitor: visitor,
};
