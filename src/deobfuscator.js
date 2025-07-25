import fs from 'fs';
import path from 'path';
import * as babel from '@babel/core';
import traverse from '@babel/traverse';
import { fileURLToPath } from 'url';
import { pathToFileURL } from 'url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const transformersDir = path.join(__dirname, 'transformers');

async function getTransformers() {
    const files = fs.readdirSync(transformersDir)
        .filter(f => f.endsWith('.js'))
        .sort();
    const transformers = await Promise.all(files.map(async filename => {
        const modulePath = pathToFileURL(path.join(transformersDir, filename)).href;
        const mod = await import(modulePath);
        let visitor, priority;
        for (const key of Object.keys(mod)) {
            if (mod[key] && typeof mod[key] === 'object' && 'visitor' in mod[key]) {
                visitor = mod[key].visitor;
                priority = mod[key].priority;
                break;
            }
        }
        if (!visitor) {
            throw new Error(`Transformer ${filename} does not export a .visitor property`);
        }
        if (typeof priority !== 'number') {
            throw new Error(`Transformer ${filename} does not export a numeric .priority property`);
        }
        return { name: filename, visitor, priority };
    }));
    transformers.sort((a, b) => a.priority - b.priority);
    return transformers;
}

export async function processSample(samplePath, outputPath) {
    try {
        const inputCode = fs.readFileSync(samplePath, 'utf-8');
        const ast = babel.parseSync(inputCode, {
            sourceType: "script"
        });

        const transformers = await getTransformers();
        for (const { name, visitor, priority } of transformers) {
            if (priority < 0) {
                console.warn(`${path.basename(samplePath)}: Skipping disabled transformer: (${name})`);
                continue;
            };
            console.log(`${path.basename(samplePath)}: --- Applying Transformer: ${name} ---`);
            traverse.default(ast, visitor);
        }

        console.log(`${path.basename(samplePath)}: --- Generating Final Code ---`);
        const finalCode = babel.transformFromAstSync(ast, null, {
            sourceType: "script",
            code: true
        });

        if (!finalCode || !finalCode.code) {
            throw new Error("Failed to generate final code from AST.");
        }
        
        fs.writeFileSync(outputPath, finalCode.code, 'utf-8');
        console.log(`${path.basename(samplePath)}: Code generation complete. Output saved to ${outputPath}`);
        return true;
    } catch (err) {
        console.error(`\n${path.basename(samplePath)}: An error occurred during deobfuscation:`, err);
        return false;
    }
}