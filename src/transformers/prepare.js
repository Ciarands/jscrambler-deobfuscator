import * as t from '@babel/types';

export const normalize = {
    priority: 0,
    visitor: {
    //   "UnaryExpression|BinaryExpression|MemberExpression": {
    //       exit(path) {
    //           const evaluation = path.evaluate();
  
    //           if (evaluation.confident) {
    //               const newNode = t.valueToNode(evaluation.value);
    //               if (t.isLiteral(newNode) || t.isIdentifier({ name: "undefined" })) {
    //                   path.replaceWith(newNode);
    //               }
    //           }
    //       }
    //   },
  
      StringLiteral(path) {
          const { extra } = path.node;
  
          if (extra && extra.raw) {
              const standardRepresentation = `'${path.node.value}'`;
              if (extra.raw !== standardRepresentation) {
                  path.replaceWith(t.stringLiteral(path.node.value));
              }
          }
      }
    }
}