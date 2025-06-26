import * as t from '@babel/types';
import generator from '@babel/generator';

function isGlobalProxyFunction(callExprPath) {
  console.log('[CLEANUP] Checking node for proxy function DNA...');

  if (!callExprPath.isCallExpression() || !callExprPath.get('callee').isFunctionExpression()) {
    console.error('[CLEANUP] FAILED: Node is not an IIFE.');
    return false;
  }
  console.log('[CLEANUP] PASSED: Node is an IIFE.');

  const functionBody = callExprPath.get('callee.body.body');
  const ifStatementPath = functionBody.find(p => p.isIfStatement());
  if (!ifStatementPath) {
    console.error('[CLEANUP] FAILED: Did not find an IfStatement in the function body.');
    return false;
  }
  console.log('[CLEANUP] PASSED: Found an IfStatement.');
  const testPath = ifStatementPath.get('test');
  if (!testPath.isBinaryExpression({ operator: '===' })) {
    console.log(`[CLEANUP] FAILED: Test is not a BinaryExpression with '===', it is a '${testPath.node.type}'.`);
    return false;
  }
  if (!testPath.get('left').isUnaryExpression({ operator: 'typeof' })) {
    console.log(`[CLEANUP] FAILED: Left side of test is not a UnaryExpression with 'typeof'.`);
    return false;
  }
  if (!testPath.get('left.argument').isIdentifier({ name: 'globalThis' })) {
    console.log(`[CLEANUP] FAILED: Argument of 'typeof' is not the identifier 'globalThis'.`);
    return false;
  }
  console.log('[CLEANUP] PASSED: Test condition `typeof globalThis === "object"` matched.');

  const alternatePath = ifStatementPath.get('alternate');
  if (!alternatePath || !alternatePath.isBlockStatement()) {
    console.error('[CLEANUP] FAILED: No "else" block (BlockStatement) found.');
    return false;
  }
  const tryStatementPath = alternatePath.get('body').find(p => p.isTryStatement());
  if (!tryStatementPath) {
    console.error('[CLEANUP] FAILED: Did not find a TryStatement in the "else" block.');
    return false;
  }
  console.log('[CLEANUP] PASSED: Found a TryStatement.');

  const catchClausePath = tryStatementPath.get('handler');
  if (!catchClausePath || !catchClausePath.isCatchClause()) {
    console.error('[CLEANUP] FAILED: TryStatement has no CatchClause.');
    return false;
  }
  console.log('[CLEANUP] PASSED: Found a CatchClause (Relaxed Check).');

  console.log('[CLEANUP] SUCCESS: Node matched all proxy function DNA checks!');
  return true;
}

function getRootObjectName(memberExpr) {
  let current = memberExpr;
  while (t.isMemberExpression(current)) {
    current = current.object;
  }
  if (t.isIdentifier(current)) {
    return current.name;
  }
  return null;
}

const generateCode = (node) => generator.default(node, { compact: true }).code;

export const finalCleanup = {
  visitor: {
    Program: {
      exit(path) {
        console.log("[CLEANUP] Starting final cleanup visitor...");
        let proxyFunctionIdentifierPath = null;
        let rootObjectName = null;
        let functionToDeleteName = null;

        console.log("[CLEANUP] PASS 1: Searching for the global proxy function assignment...");
        path.traverse({
          AssignmentExpression(assignPath) {
            const left = assignPath.get('left');
            const right = assignPath.get('right');

            if (left.isMemberExpression() && isGlobalProxyFunction(right)) {
              proxyFunctionIdentifierPath = left;
              rootObjectName = getRootObjectName(left.node);

              console.log(`[CLEANUP] Found proxy function assignment: ${generateCode(left.node)}`);
              console.log(`[CLEANUP] Extracted root object name: ${rootObjectName}`);

              assignPath.stop();
            }
          },
        });

        if (!proxyFunctionIdentifierPath || !rootObjectName) {
          console.error("[CLEANUP] ABORTING: Could not find the proxy function. No changes will be made.");
          return;
        }
        
        const proxyPattern = generateCode(proxyFunctionIdentifierPath.node);
        console.log(`[CLEANUP] Proxy function identifier pattern is: ${proxyPattern}`);
        console.log("[CLEANUP] PASS 2: Searching for the wrapper function call...");
        path.traverse({
          CallExpression(callPath) {
            const args = callPath.get('arguments');

            if (args.length === 1 && generateCode(args[0].node) === proxyPattern) {
              const callee = callPath.get('callee');
              if (callee.isIdentifier()) {
                functionToDeleteName = callee.node.name;
                console.log(`[CLEANUP] Found wrapper call. Function to delete: ${functionToDeleteName}`);
                callPath.stop();
              }
            }
          },
        });

        if (!functionToDeleteName) {
            console.warn("[CLEANUP] Could not find the wrapper function call to delete. Will still proceed with object replacement.");
        }

        console.log("[CLEANUP] PASS 3: Performing modifications...");
        if (functionToDeleteName) {
            console.log(`[CLEANUP] Searching for declaration of function "${functionToDeleteName}" to remove it.`);
            const binding = path.scope.getBinding(functionToDeleteName);
            if (binding) {
                console.log(`[CLEANUP] Found binding for "${functionToDeleteName}". Removing its declaration path.`);
                binding.path.getStatementParent().remove();
            } else {
                console.warn(`[CLEANUP] Could not find binding for "${functionToDeleteName}" to remove. It might be a global or already removed.`);
            }
        }

        if (rootObjectName) {
            console.log(`[CLEANUP] Searching for declaration of root object "${rootObjectName}".`);
            const binding = path.scope.getBinding(rootObjectName);
            if (binding) {
                console.log(`[CLEANUP] Found binding for "${rootObjectName}". Replacing its ${binding.referencePaths.length} references with 'window'.`);
                binding.referencePaths.forEach(refPath => {
                    refPath.replaceWith(t.identifier('window'));
                });
                console.log(`[CLEANUP] Removing the declaration of the now-unused object "${rootObjectName}".`);
                binding.path.getStatementParent().remove();
            } else {
                console.warn(`[CLEANUP] Could not find binding for root object "${rootObjectName}" to replace.`);
            }
        }
        
        console.log("[CLEANUP] Final cleanup visitor finished.");
      },
    },

    "IfStatement|ConditionalExpression": {
      exit(path) {
        if (path.removed) return;
        const testPath = path.get("test");
        const evaluation = testPath.evaluateTruthy();
        if (evaluation !== undefined) {
          if (evaluation) {
            path.replaceWithMultiple(
              t.isBlockStatement(path.node.consequent) ?
              path.node.consequent.body :
              [path.node.consequent]
            );
          } else {
            if (path.node.alternate) {
              path.replaceWithMultiple(
                t.isBlockStatement(path.node.alternate) ?
                path.node.alternate.body :
                [path.node.alternate]
              );
            } else {
              path.remove();
            }
          }
        }
      }
    },
    VariableDeclaration: {
      exit(path) {
        if (path.node.declarations.length === 0) {
          path.remove();
        }
      }
    }
  }
};