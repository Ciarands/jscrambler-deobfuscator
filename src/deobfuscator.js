import fs from 'fs';
import path from 'path';
import * as babel from '@babel/core';
import traverse from '@babel/traverse';
import { normalizeLiterals } from './transformers/normalizeLiterals.js';
import { controlFlowUnflattener } from './transformers/controlFlowUnflattener.js';
import { inlineArrayBuilder } from './transformers/inlineArrayBuilder.js';
import { inlineWrapperFunctions } from './transformers/inlineProxiedFunctions.js';
import { solveStringArray } from './transformers/solveStringArray.js';
import { solveStateMachine } from './transformers/solveStateMachine.js';
import { inlineStringArray } from './transformers/inlineStringArray.js';
import { inlineSetupFunctions } from './transformers/inlineSetupFunctions.js';
import { finalCleanup } from './transformers/finalCleanup.js';

export function processSample(samplePath, outputPath) {
    try {
        console.log(`\n=== Processing ${path.basename(samplePath)} ===`);
        
        const inputCode = fs.readFileSync(samplePath, 'utf-8');
        const ast = babel.parseSync(inputCode, {
            sourceType: "script"
        });

        
        // Pass 1: Unflatten control flow
        console.log("--- Starting Pass 1: Unflattening Control Flow ---");
        traverse.default(ast, controlFlowUnflattener.visitor);
        console.log("Pass 1 complete.");
        
        // Pass 2: Normalize literals
        console.log("--- Starting Pass 2: Normalizing Literals ---");
        traverse.default(ast, normalizeLiterals.visitor);
        console.log("Pass 2 complete.");

        // Pass 3: Inline array builder
        console.log("--- Starting Pass 3: Inlining Array Builder ---");
        traverse.default(ast, inlineArrayBuilder.visitor);
        console.log("Pass 3 complete.");

        // Pass 4: Inline wrapper functions
        console.log("--- Starting Pass 4: Inlining Wrapper Functions ---");
        traverse.default(ast, inlineWrapperFunctions.visitor);
        console.log("Pass 4 complete.");

        // Pass 5: Inline setup functions
        console.log("--- Starting Pass 5: Inlining Setup Functions ---");
        traverse.default(ast, inlineSetupFunctions.visitor);
        console.log("Pass 5 complete.");

        // Pass 6: Solve string array
        console.log("--- Starting Pass 6: Solving String Array ---");
        traverse.default(ast, solveStringArray.visitor);
        console.log("Pass 6 complete.");

        // Pass 7: Solve state machine
        console.log("--- Starting Pass 7: Solving State Machine ---");
        traverse.default(ast, solveStateMachine.visitor);
        console.log("Pass 7 complete.");

        // Pass 8: Inline string array
        console.log("--- Starting Pass 8: Inlining String Array ---");
        traverse.default(ast, inlineStringArray.visitor);
        console.log("Pass 8 complete.");

        // Pass 9: Final cleanup
        console.log("--- Strating Pass 9: Final Cleanup ---")
        traverse.default(ast, finalCleanup.visitor);
        console.log("Pass 9 complete.")

        // Generate final code
        console.log("--- Generating Final Code ---");
        const finalCode = babel.transformFromAstSync(ast, null, {
            sourceType: "script",
            code: true
        });

        if (!finalCode || !finalCode.code) {
            throw new Error("Failed to generate final code from AST.");
        }
        
        // Save the final result
        fs.writeFileSync(outputPath, finalCode.code, 'utf-8');
        console.log(`Code generation complete. Output saved to ${outputPath}`);
        
        return true;
    } catch (err) {
        console.error(`\nAn error occurred during deobfuscation of ${path.basename(samplePath)}:`, err);
        return false;
    }
}