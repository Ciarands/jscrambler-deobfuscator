import * as t from '@babel/types';


function isSetupCallPattern(node) {
  const args = node.arguments;

  if (args.length !== 4 && args.length !== 5) {
    return false;
  }

  return (
    t.isIdentifier(args[0]) &&
    t.isStringLiteral(args[1]) &&
    t.isNumericLiteral(args[2]) &&
    t.isStringLiteral(args[3])
  );
}

export const inlineSetupFunctions = {
  visitor: {
    Program: {
      enter(path) {
        const potentialWrappers = new Map();

        path.traverse({
          CallExpression(callPath) {
            const { callee } = callPath.node;
            if (t.isIdentifier(callee) && isSetupCallPattern(callPath.node)) {
              if (!potentialWrappers.has(callee.name)) {
                potentialWrappers.set(callee.name, []);
              }
              potentialWrappers.get(callee.name).push(callPath);
            }
          },
        });

        let wrapperName = null;
        let setupCallPaths = [];
        for (const [name, paths] of potentialWrappers.entries()) {
          if (paths.length > setupCallPaths.length) {
            wrapperName = name;
            setupCallPaths = paths;
          }
        }

        if (!wrapperName) {
          console.log("Deobfuscation: No setup function found to inline.");
          return;
        }

        const renames = {};
        for (const callPath of setupCallPaths) {
          const args = callPath.node.arguments;
          const originalName = args[1].value;
          const newName = args[3].value;
          renames[newName] = originalName;
        }

        const renamerVisitor = {
          MemberExpression(memberPath) {
            const property = memberPath.get('property');
            if (
              !memberPath.node.computed &&
              property.isIdentifier() &&
              renames.hasOwnProperty(property.node.name)
            ) {
              property.replaceWith(t.identifier(renames[property.node.name]));
            }
          },
          Identifier(idPath) {
            if (
              renames.hasOwnProperty(idPath.node.name) &&
              idPath.isReferenced() &&
              !(idPath.parentPath.isMemberExpression() && idPath.key === 'property')
            ) {
              idPath.replaceWith(t.identifier(renames[idPath.node.name]));
            }
          },
        };

        path.traverse(renamerVisitor);

        for (const callPath of setupCallPaths) {
          if (callPath.parentPath.isExpressionStatement()) {
            callPath.parentPath.remove();
          }
        }

        const wrapperBinding = path.scope.getBinding(wrapperName);
        if (wrapperBinding) {
          const declarationPath = wrapperBinding.path.getStatementParent();
          if (declarationPath) {
            declarationPath.remove();
          }
        }
      },
    },
  },
};