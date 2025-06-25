import * as t from "@babel/types";
import generate from "@babel/generator";
const gen = (node) => {
  return generate.default(node, {
    compact: true
  }).code;
};

function safeValueToNode(value) {
  if (value === undefined) {
    return t.identifier("undefined");
  }
  try {
    return t.valueToNode(value);
  } catch (e) {
    return null;
  }
}

export const inlineStringArray = {
  visitor: {
    Program(path) {
      console.log("[INLINE-STR] Starting inlining pass...");

      let arrayInfo = null;
      let arrayDefinitionPath = null;

      path.traverse({

        AssignmentExpression(assignmentPath) {
          if (arrayInfo) return;
          const right = assignmentPath.get("right");
          if (!right.isCallExpression() || !right.get("callee").isFunctionExpression()) {
            return;
          }

          const iifePath = right.get("callee");
          iifePath.traverse({
            ArrayExpression(arrayPath) {
              const parentMemberExpr = arrayPath.parentPath;
              if (!parentMemberExpr.isMemberExpression({
                  object: arrayPath.node
                })) return;
              const grandParentReturn = parentMemberExpr.parentPath;
              if (!grandParentReturn.isReturnStatement({
                  argument: parentMemberExpr.node,
                })) return;
              const accessorFunc = grandParentReturn.findParent((p) => p.isFunctionExpression());
              if (!accessorFunc) return;
              const objectProp = accessorFunc.findParent((p) => p.isObjectProperty({
                value: accessorFunc.node
              }));
              if (!objectProp) return;
              const evalResults = arrayPath.get("elements").map((el) => el.evaluate());
              if (!evalResults.every((r) => r.confident)) {
                return;
              }
              const theArray = evalResults.map((r) => r.value);
              const objectName = gen(assignmentPath.node.left);
              const accessorName = objectProp.get("key").isIdentifier() ? objectProp.get("key").node.name : objectProp.get("key").node.value;
              arrayInfo = {
                objectName,
                accessorName,
                theArray
              };
              arrayDefinitionPath = assignmentPath.getStatementParent();
              console.log(`\n[INLINE-STR] Successfully parsed literal array!`);
              console.log(`[INLINE-STR] - Object Name: '${objectName}'`);
              console.log(`[INLINE-STR] - Accessor Name: '${accessorName}'`);
              console.log(`[INLINE-STR] - Array Size:${theArray.length}\n`);
              arrayPath.stop();
            },
          });
          if (arrayInfo) {
            assignmentPath.stop();
          }
        },
      });

      if (!arrayInfo) {
        console.log("[INLINE-STR] No target array definition found. Exiting.");
        return;
      }

      let replacementsMade = 0;

      path.traverse({
        CallExpression(callPath) {
          const callee = callPath.get("callee");
          if (!callee.isMemberExpression()) return;
          const {
            objectName,
            accessorName,
            theArray
          } = arrayInfo;
          if (gen(callee.node.object) === objectName && callee.get("property").isIdentifier({
              name: accessorName
            })) {
            const evaluation = callPath.get("arguments.0").evaluate();
            if (evaluation.confident && typeof evaluation.value === "number") {
              const index = evaluation.value;
              if (index >= 0 && index < theArray.length) {
                const resolvedValue = theArray[index];
                const replacementNode = safeValueToNode(resolvedValue);
                if (replacementNode) {
                  // console.log(`[INLINE-STR] Inlining ${gen(callPath.node)} -> ${gen(replacementNode)}`);
                  callPath.replaceWith(replacementNode);
                  replacementsMade++;
                } else {
                  console.warn(`[INLINE-STR] Could not create a literal node for value at index ${index}.`);
                }
              } else {
                console.warn(`[INLINE-STR] Index ${index} is out of bounds for call: ${gen(callPath.node)}`);
              }
            } else {
              console.warn(`[INLINE-STR] Could not statically resolve index for call: ${gen(callPath.node)}`);
            }
          }
        },
      });

      console.log(`[INLINE-STR] Made ${replacementsMade} replacements.`);
      if (arrayDefinitionPath && !arrayDefinitionPath.removed && replacementsMade > 0) {
        try {
          arrayDefinitionPath.remove();
          console.log("[INLINE-STR] Cleanup: Removed original array definition.");
        } catch (e) {
          console.error("[INLINE-STR] Cleanup failed.", e);
        }
      }

      path.skip();
    },
  },
};