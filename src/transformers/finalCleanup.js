import * as t from '@babel/types';

export const finalCleanup = {
  visitor: {
    "IfStatement|ConditionalExpression": {
      exit(path) {
        const testPath = path.get("test");
        const evaluation = testPath.evaluateTruthy();

        if (evaluation !== undefined) {
          if (evaluation) {
            path.replaceWithMultiple(
              t.isBlockStatement(path.node.consequent) ?
              path.node.consequent.body :
              path.node.consequent
            );
          } else {
            if (path.node.alternate) {
              path.replaceWithMultiple(
                t.isBlockStatement(path.node.alternate) ?
                path.node.alternate.body :
                path.node.alternate
              );
            } else {
              path.remove();
            }
          }
        }
      }
    },

    ExpressionStatement: {
      exit(path) {
        if (path.get("expression").isPure()) {
          path.remove();
        }
      }
    },

    Scopable: {
      exit(path) {
        path.scope.crawl();

        for (const bindingName in path.scope.bindings) {
          const binding = path.scope.bindings[bindingName];
          if (binding.referenced || !binding.constant) {
            continue;
          }

          const bindingPath = binding.path;
          if (bindingPath.isVariableDeclarator()) {
            const initPath = bindingPath.get("init");
            if (initPath.node && !initPath.isPure()) {
              continue;
            }
          }
          else if (!bindingPath.isFunctionDeclaration()) {
            continue;
          }

          bindingPath.remove();
        }
      }
    },

    TryStatement: {
      exit(path) {
        const tryBlock = path.get("block");
        if (tryBlock.node.body.length === 0) {
          if (path.node.finalizer) {
            path.replaceWith(path.node.finalizer);
          } else {
            path.remove();
          }
        }
      }
    },

    BlockStatement: {
      exit(path) {
        if (
          path.node.body.length === 1 &&
          (path.parentPath.isIfStatement() || path.parentPath.isBlockStatement() || path.parentPath.isForStatement())
        ) {
          path.replaceWith(path.node.body[0]);
        }
      }
    },

    EmptyStatement: {
      exit(path) {
        path.remove();
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