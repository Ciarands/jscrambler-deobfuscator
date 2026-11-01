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
            console.log(`   |-> Arguments: size=${arg1}, offset=${arg2}, key=[${arg3}]`);

            const realArray = generateCyclicalArray(arg1, arg2, arg3);
            generatedArraysMap.set(fullKey, realArray);
            console.log(`   |-> In-memory array generated and stored for key: "${fullKey}"`);

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
                    console.log('   |-> Could not determine initial state.');
                    return;
                }
                const initialId = initialStateInfo.id;
                console.log(`   |-> Initial state: ${initialStateInfo.raw}`);

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
                console.log(`   |-> Found ${caseMap.size} switch cases`);

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

                const EXIT = Symbol('EXIT');

                function splitOffStateUpdate(caseBody, stateUpdateRhs) {
                    const lastStmt = caseBody[caseBody.length - 1];
                    const withoutUpdate = caseBody.slice(0, -1);
                    if (
                        t.isExpressionStatement(lastStmt) &&
                        t.isSequenceExpression(lastStmt.expression)
                    ) {
                        const expressions = lastStmt.expression.expressions.slice(0, -1);
                        withoutUpdate.push(...expressions.map((e) => t.expressionStatement(e)));
                    } else if (
                        t.isVariableDeclaration(lastStmt) &&
                        lastStmt.declarations.length > 1
                    ) {
                        const newDeclarators = lastStmt.declarations.slice(0, -1);
                        withoutUpdate.push(t.variableDeclaration(lastStmt.kind, newDeclarators));
                    }
                    return withoutUpdate;
                }

                function buildCfg() {
                    const cfg = new Map();
                    const asTarget = (id) => (id === terminalId ? EXIT : id);
                    for (const [id, caseBody] of caseMap) {
                        const lastStmt = caseBody.length > 0 ? caseBody[caseBody.length - 1] : null;
                        if (t.isReturnStatement(lastStmt)) {
                            cfg.set(id, { kind: 'return', body: caseBody });
                            continue;
                        }
                        const stateUpdateRhs = getStateUpdateRhs(caseBody);
                        if (!stateUpdateRhs) {
                            cfg.set(id, { kind: 'invalid', body: caseBody });
                            continue;
                        }
                        const body = splitOffStateUpdate(caseBody, stateUpdateRhs);
                        const nextInfo = resolveAndGetStateId(stateUpdateRhs);
                        if (nextInfo.id !== null) {
                            cfg.set(id, { kind: 'jump', body, nextId: asTarget(nextInfo.id) });
                            continue;
                        }
                        if (t.isConditionalExpression(stateUpdateRhs)) {
                            const trueInfo = resolveAndGetStateId(stateUpdateRhs.consequent);
                            const falseInfo = resolveAndGetStateId(stateUpdateRhs.alternate);
                            if (trueInfo.id === null || falseInfo.id === null) {
                                cfg.set(id, { kind: 'invalid', body });
                                continue;
                            }
                            cfg.set(id, {
                                kind: 'branch',
                                body,
                                test: stateUpdateRhs.test,
                                trueId: asTarget(trueInfo.id),
                                falseId: asTarget(falseInfo.id),
                            });
                            continue;
                        }

                        cfg.set(id, { kind: 'invalid', body });
                    }
                    return cfg;
                }

                function successorsOf(id, cfg) {
                    const node = cfg.get(id);
                    if (!node) return [];
                    if (node.kind === 'return') return [EXIT];
                    if (node.kind === 'jump') return [node.nextId];
                    if (node.kind === 'branch') return [node.trueId, node.falseId];
                    return [];
                }

                function buildGraphMaps(cfg) {
                    const nodeIds = [...cfg.keys()];
                    const succMap = new Map();
                    const predMap = new Map();
                    for (const id of [...nodeIds, EXIT]) {
                        succMap.set(id, []);
                        predMap.set(id, []);
                    }
                    for (const id of nodeIds) {
                        const succs = successorsOf(id, cfg);
                        succMap.set(id, succs);
                        for (const s of succs) predMap.get(s).push(id);
                    }
                    return { succMap, predMap };
                }

                function computeDominators(entry, getSuccessors) {
                    const order = [];
                    const visited = new Set();
                    (function dfs(id) {
                        visited.add(id);
                        for (const s of getSuccessors(id)) {
                            if (!visited.has(s)) dfs(s);
                        }
                        order.push(id);
                    })(entry);
                    order.reverse();

                    const index = new Map(order.map((id, i) => [id, i]));
                    const preds = new Map(order.map((id) => [id, []]));
                    for (const id of order) {
                        for (const s of getSuccessors(id)) {
                            if (preds.has(s)) preds.get(s).push(id);
                        }
                    }

                    const idom = new Map([[entry, entry]]);
                    function intersect(a, b) {
                        while (a !== b) {
                            while (index.get(a) > index.get(b)) a = idom.get(a);
                            while (index.get(b) > index.get(a)) b = idom.get(b);
                        }
                        return a;
                    }

                    let changed = true;
                    while (changed) {
                        changed = false;
                        for (const id of order) {
                            if (id === entry) continue;
                            const ps = preds.get(id).filter((p) => idom.has(p));
                            if (!ps.length) continue;
                            let newIdom = ps[0];
                            for (const p of ps.slice(1)) newIdom = intersect(newIdom, p);
                            if (idom.get(id) !== newIdom) {
                                idom.set(id, newIdom);
                                changed = true;
                            }
                        }
                    }
                    return idom;
                }

                function dominates(a, b, idom) {
                    if (!idom.has(b)) return false;
                    let cur = b;
                    while (true) {
                        if (cur === a) return true;
                        const next = idom.get(cur);
                        if (next === cur) return false;
                        cur = next;
                    }
                }

                function computeLoops(nodeIds, succMap, predMap, fwdIdom) {
                    const latchesByHeader = new Map();
                    for (const u of nodeIds) {
                        for (const v of succMap.get(u)) {
                            if (v === EXIT) continue;
                            if (dominates(v, u, fwdIdom)) {
                                if (!latchesByHeader.has(v)) latchesByHeader.set(v, new Set());
                                latchesByHeader.get(v).add(u);
                            }
                        }
                    }
                    const loopInfo = new Map();
                    for (const [header, latches] of latchesByHeader) {
                        const loopSet = new Set([header, ...latches]);
                        const worklist = [...latches];
                        while (worklist.length) {
                            const n = worklist.pop();
                            for (const p of predMap.get(n)) {
                                if (!loopSet.has(p)) {
                                    loopSet.add(p);
                                    worklist.push(p);
                                }
                            }
                        }
                        loopInfo.set(header, { nodes: loopSet, latches: Array.from(latches) });
                    }
                    return loopInfo;
                }

                const cfg = buildCfg();
                const { succMap, predMap } = buildGraphMaps(cfg);
                const nodeIds = [...cfg.keys()];

                let fwdIdom = new Map();
                let ipdom = new Map();
                let loopInfo = new Map();
                if (cfg.has(initialId)) {
                    fwdIdom = computeDominators(initialId, (id) => succMap.get(id) || []);
                    ipdom = computeDominators(EXIT, (id) => predMap.get(id) || []);
                    loopInfo = computeLoops(nodeIds, succMap, predMap, fwdIdom);
                }

                let success = true;
                const hoistedVars = new Set();
                const memo = new Map();
                const inProgress = new Set();

                function structure(id, stopId) {
                    if (id === EXIT || id === stopId) return [];
                    if (memo.has(id) && memo.get(id).has(stopId)) {
                        return memo.get(id).get(stopId);
                    }
                    if (inProgress.has(id)) {
                        success = false;
                        return null;
                    }

                    const node = cfg.get(id);
                    if (!node || node.kind === 'invalid') {
                        success = false;
                        return null;
                    }

                    inProgress.add(id);
                    const result = buildNode(id, node, stopId);
                    inProgress.delete(id);
                    if (!success) return null;
                    if (!memo.has(id)) memo.set(id, new Map());
                    memo.get(id).set(stopId, result);
                    return result;
                }

                function buildNode(id, node, stopId) {
                    const body = processVarDeclarations(node.body, hoistedVars);

                    if (node.kind === 'return') {
                        return body;
                    }

                    const loopData = loopInfo.get(id);
                    if (loopData) {
                        const { nodes: loopSet, latches } = loopData;

                        if (node.kind === 'branch') {
                            const trueIn = loopSet.has(node.trueId);
                            const falseIn = loopSet.has(node.falseId);
                            let entryId, exitId, testExpr;
                            if (trueIn && !falseIn) {
                                entryId = node.trueId;
                                exitId = node.falseId;
                                testExpr = node.test;
                            } else if (falseIn && !trueIn) {
                                entryId = node.falseId;
                                exitId = node.trueId;
                                testExpr = t.unaryExpression('!', node.test, true);
                            } else {
                                success = false;
                                return null;
                            }

                            if (entryId === id) {
                                const doWhileLoop = t.doWhileStatement(testExpr, t.blockStatement(body));
                                const rest = structure(exitId, stopId);
                                if (!success) return null;
                                return [doWhileLoop, ...rest];
                            } else {
                                let updateExpr = null;
                                let latchId = null;
                                if (latches.length === 1) {
                                    latchId = latches[0];
                                    const latchNode = cfg.get(latchId);
                                    if (latchNode && latchNode.kind === 'jump' && latchNode.body.length === 1) {
                                        const stmt = latchNode.body[0];
                                        if (t.isExpressionStatement(stmt)) {
                                            const expr = stmt.expression;
                                            if (t.isUpdateExpression(expr) || t.isAssignmentExpression(expr)) {
                                                updateExpr = expr;
                                            }
                                        }
                                    }
                                }

                                if (updateExpr && latchId !== null) {
                                    const loopBodyNodes = structure(entryId, latchId);
                                    if (!success) return null;
                                    const rest = structure(exitId, stopId);
                                    if (!success) return null;
                                    const forLoop = t.forStatement(null, testExpr, updateExpr, t.blockStatement(loopBodyNodes));
                                    return [...body, forLoop, ...rest];
                                } else {
                                    const loopBodyNodes = structure(entryId, id);
                                    if (!success) return null;
                                    const rest = structure(exitId, stopId);
                                    if (!success) return null;
                                    const whileLoop = t.whileStatement(testExpr, t.blockStatement(loopBodyNodes));
                                    return [...body, whileLoop, ...rest];
                                }
                            }
                        } else if (node.kind === 'jump') {
                            if (latches.length !== 1) {
                                success = false;
                                return null;
                            }
                            const latchId = latches[0];
                            const latchNode = cfg.get(latchId);

                            if (!latchNode || latchNode.kind !== 'branch') {
                                success = false;
                                return null;
                            }

                            let exitId, testExpr;
                            if (latchNode.trueId === id) {
                                exitId = latchNode.falseId;
                                testExpr = latchNode.test;
                            } else if (latchNode.falseId === id) {
                                exitId = latchNode.trueId;
                                testExpr = t.unaryExpression('!', latchNode.test, true);
                            } else {
                                success = false;
                                return null;
                            }

                            const middleNodes = structure(node.nextId, latchId);
                            if (!success) return null;

                            const latchBody = processVarDeclarations(latchNode.body, hoistedVars);

                            const doWhileBody = t.blockStatement([...body, ...middleNodes, ...latchBody]);
                            const doWhileLoop = t.doWhileStatement(testExpr, doWhileBody);

                            const rest = structure(exitId, stopId);
                            if (!success) return null;

                            return [doWhileLoop, ...rest];
                        }
                    }

                    if (node.kind === 'jump') {
                        if (node.nextId === EXIT && stopId !== null) {
                            return [...body, t.breakStatement()];
                        }
                        const rest = structure(node.nextId, stopId);
                        if (!success) return null;
                        return [...body, ...rest];
                    }

                    let joinId = ipdom.has(id) ? ipdom.get(id) : null;
                    if (joinId === EXIT || joinId === stopId) {
                        joinId = null;
                    }
                    const branchStopId = joinId !== null ? joinId : stopId;
                    const trueBranchBody = structure(node.trueId, branchStopId);
                    const falseBranchBody = structure(node.falseId, branchStopId);
                    if (!success) return null;

                    let alternateNode = null;
                    if (falseBranchBody.length === 1 && t.isIfStatement(falseBranchBody[0])) {
                        alternateNode = falseBranchBody[0];
                    } else if (falseBranchBody.length > 0) {
                        alternateNode = t.blockStatement(falseBranchBody);
                    }
                    const ifStatement = t.ifStatement(
                        node.test,
                        t.blockStatement(trueBranchBody),
                        alternateNode
                    );
                    const tailNodes = joinId !== null ? structure(joinId, stopId) : [];
                    if (!success) return null;
                    return [...body, ifStatement, ...tailNodes];
                }

                const unflattenedBody =
                    cfg.has(initialId) ? structure(initialId, null) : null;

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
                        `   |-> Successfully unflattened state machine. Generated ${newNodes.length} nodes.`
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
                    console.warn('   |-> Failed to unflatten state machine. Reverting changes.');
                }
            },
        },
    },
};
