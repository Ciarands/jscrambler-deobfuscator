import * as t from '@babel/types';

function isWrapperFunction(node) {
  if (!t.isFunctionExpression(node) || node.body.body.length !== 1 || !t.isReturnStatement(node.body.body[0])) {
    return null;
  }
  const returnArg = node.body.body[0].argument;
  if (!t.isConditionalExpression(returnArg)) {
    return null;
  }

  const { test, consequent, alternate } = returnArg;
  if (!t.isBinaryExpression(test, { operator: '===' }) ||
      !t.isUnaryExpression(test.left, { operator: 'typeof' }) ||
      !t.isStringLiteral(test.right, { value: 'function' })) {
    return null;
  }

  const targetExpression = test.left.argument;
  if (!t.isMemberExpression(targetExpression)) {
    return null;
  }

  if (!t.isNodesEquivalent(alternate, targetExpression)) {
    return null;
  }

  if (!t.isCallExpression(consequent)) {
    return null;
  }

  if (!t.isMemberExpression(consequent.callee) || !t.isIdentifier(consequent.callee.property, { name: 'apply' })) {
    return null;
  }

  if (!t.isNodesEquivalent(consequent.callee.object, targetExpression)) {
    return null;
  }

  const applyArgs = consequent.arguments;
  if (applyArgs.length !== 2) return null;
  if (!t.isNodesEquivalent(applyArgs[0], targetExpression.object)) {
    return null;
  }

  if (!t.isIdentifier(applyArgs[1], { name: 'arguments' })) {
    return null;
  }
  
  return targetExpression;
}

function getMemberKey(node) {
    if (node.computed && (t.isNumericLiteral(node.property) || t.isStringLiteral(node.property))) {
      return node.property.value;
    }
    if (!node.computed && t.isIdentifier(node.property)) {
      return node.property.name;
    }
    return null;
}


export const inlineWrapperFunctions = {
  visitor: {
    Program(path) {
      const candidateFrequencies = new Map();
      path.traverse({
        AssignmentExpression(discoveryPath) {
          const { left, right } = discoveryPath.node;
          if (t.isMemberExpression(left) && t.isIdentifier(left.object) && isWrapperFunction(right)) {
            const objectName = left.object.name;
            candidateFrequencies.set(objectName, (candidateFrequencies.get(objectName) || 0) + 1);
          }
        }
      });
      
      if (candidateFrequencies.size === 0) {
        console.log('[INLINE-PROXY] No wrapper functions found. Halting.');
        return;
      }
      
      const baseObjectName = [...candidateFrequencies.entries()].reduce((a, b) => b[1] > a[1] ? b : a)[0];
      console.log(`[INLINE-PROXY] Discovery complete. Base Object is "${baseObjectName}".`);

      const baseObjectAliases = new Set([baseObjectName]);
      const wrapperMap = new Map();
      
      path.traverse({
        VariableDeclarator(path) {
          const { id, init } = path.node;
          if (t.isIdentifier(id) && t.isIdentifier(init) && baseObjectAliases.has(init.name)) {
            baseObjectAliases.add(id.name);
          }
        },
        AssignmentExpression: {
          exit(path) {
            const { left, right } = path.node;
            if (!t.isMemberExpression(left) || !t.isIdentifier(left.object) || !baseObjectAliases.has(left.object.name)) {
              return;
            }
            const targetMemberExpr = isWrapperFunction(right);
            if (targetMemberExpr) {
              const wrapperKey = getMemberKey(left);
              if (wrapperKey !== null) {
                wrapperMap.set(wrapperKey, targetMemberExpr);
                path.remove();
              }
            }
          }
        },
        CallExpression: {
            exit(path) {
                const callee = path.node.callee;
                if (!t.isMemberExpression(callee) || !t.isIdentifier(callee.object) || !baseObjectAliases.has(callee.object.name)) {
                    return;
                }
                const wrapperKey = getMemberKey(callee);
                if (wrapperKey !== null && wrapperMap.has(wrapperKey)) {
                    const targetMemberExpr = wrapperMap.get(wrapperKey);
                    // console.log(`[INLINE-PROXY] Inlining call to "${callee.object.name}[${wrapperKey}]"`);
                    path.replaceWith(t.callExpression(targetMemberExpr, path.node.arguments));
                }
            }
        }
      });
      console.log('[INLINE-PROXY] Inlining complete.');
    }
  }
};