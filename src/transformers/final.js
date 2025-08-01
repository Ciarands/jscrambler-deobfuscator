import * as t from '@babel/types';

export const prepare = {
    priority: 99999999,
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
    },
};
