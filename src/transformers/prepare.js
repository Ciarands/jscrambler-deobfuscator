import * as t from '@babel/types';

export const normalize = {
    priority: 0,
    visitor: {
        StringLiteral(path) {
            const { extra } = path.node;

            if (extra && extra.raw) {
                const standardRepresentation = `'${path.node.value}'`;
                if (extra.raw !== standardRepresentation) {
                    path.replaceWith(t.stringLiteral(path.node.value));
                }
            }
        },

        AssignmentExpression(path) {
            const { left, right } = path.node;
            if (!t.isMemberExpression(left) || !t.isIdentifier(left.object)) return;
            if (!t.isCallExpression(right)) return;
            const callee = right.callee;
            if (!t.isFunctionExpression(callee) && !t.isArrowFunctionExpression(callee)) return;

            console.log(
                ` |-> Found candidate AssignmentExpression "${left.object.name}", attempting to validate and retrieve global getter obj`
            );
            let isGlobalGetter = false;
            path.get('right.callee').traverse({
                CallExpression(callPath) {
                    if (isGlobalGetter) return;
                    const callee = callPath.get('callee');
                    if (
                        !callee.isMemberExpression() ||
                        !callee.get('object').isIdentifier({ name: 'Object' })
                    )
                        return;

                    const prop = callee.get('property');
                    const isDefineProperty =
                        prop.isIdentifier({ name: 'defineProperty' }) ||
                        prop.isStringLiteral({ value: 'defineProperty' });
                    if (!isDefineProperty) return;

                    const descriptor = callPath.get('arguments.2');
                    if (!descriptor || !descriptor.isObjectExpression()) return;

                    const getProperty = descriptor
                        .get('properties')
                        .find(
                            (p) =>
                                p.isObjectProperty() &&
                                (t.isIdentifier(p.node.key, { name: 'get' }) ||
                                    t.isStringLiteral(p.node.key, { value: 'get' }))
                        );
                    if (!getProperty || !getProperty.get('value').isFunctionExpression()) return;

                    const getterBody = getProperty.get('value.body.body');
                    if (
                        getterBody.length === 1 &&
                        getterBody[0].isReturnStatement() &&
                        getterBody[0].get('argument').isThisExpression()
                    ) {
                        isGlobalGetter = true;
                        callPath.stop();
                    }
                },
            });
            if (!isGlobalGetter) return;
            const proxyIdentifier = left.object;
            const proxyName = proxyIdentifier.name;
            const aliasMemberExpressionNode = left;

            console.log(` |-> Found global object proxy: '${proxyName}' (via ${callee.type}).`);

            const programPath = path.scope.getProgramParent().path;
            const binding = programPath.scope.getBinding(proxyName);
            if (!binding) return;

            if (!programPath.node.injectedGlobal) {
                const globalIdentifier = programPath.scope.generateUidIdentifier('global');
                programPath.unshiftContainer(
                    'body',
                    t.variableDeclaration('const', [
                        t.variableDeclarator(globalIdentifier, t.identifier('globalThis')),
                    ])
                );
                programPath.node.injectedGlobal = globalIdentifier;
                console.log(` |-> Injected global variable: ${globalIdentifier.name}`);
            }
            const globalIdentifier = programPath.node.injectedGlobal;

            const refs = binding.referencePaths;
            for (let i = refs.length - 1; i >= 0; i--) {
                const refPath = refs[i];
                const parentMemberExpr = refPath.parentPath;
                if (
                    parentMemberExpr.isMemberExpression({ object: refPath.node }) &&
                    t.isNodesEquivalent(
                        parentMemberExpr.node.property,
                        aliasMemberExpressionNode.property
                    ) &&
                    parentMemberExpr.node.computed === aliasMemberExpressionNode.computed
                ) {
                    parentMemberExpr.replaceWith(globalIdentifier);
                } else {
                    refPath.replaceWith(globalIdentifier);
                }
            }
            console.log(
                ` |-> Replaced all ${refs.length} references to '${proxyName}' and its alias.`
            );
            if (binding.path.isVariableDeclarator()) {
                binding.path.remove();
                console.log(` |-> Removed original proxy declaration.`);
            }

            if (path.parentPath.isSequenceExpression()) {
                path.remove();
                console.log(` |-> Removed assignment from parent SequenceExpression.`);
            } else if (path.parentPath.isExpressionStatement()) {
                path.parentPath.remove();
                console.log(` |-> Removed redundant ExpressionStatement.`);
            } else {
                // in a structure we don't recognise
                console.warn(
                    ` |-> Assignment found in an unexpected parent container: ${path.parentPath.type}. Cleanup skipped.`
                );
            }

            programPath.scope.crawl();
            path.stop();
        },
    },
};
