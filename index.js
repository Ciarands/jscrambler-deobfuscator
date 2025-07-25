import fs from 'fs';
import path from 'path';
import { processSample } from './src/deobfuscator.js';

try {
    const samplesDir = './samples';
    const outputDir = './output';
    
    if (!fs.existsSync(outputDir)) {
        fs.mkdirSync(outputDir, { recursive: true });
    }
    
    const sampleFiles = fs.readdirSync(samplesDir)
        .filter(file => file.endsWith('.js'))
        .map(file => path.join(samplesDir, file));
    
    if (sampleFiles.length === 0) {
        console.log("No .js files found in ./samples directory");
        process.exit(0);
    }
    
    console.log(`Found ${sampleFiles.length} sample files to process:`);
    sampleFiles.forEach(file => console.log(`  - ${path.basename(file)}`));
    
    
    for (const sampleFile of sampleFiles) {
        const outputFile = path.join(outputDir, path.basename(sampleFile));
        processSample(sampleFile, outputFile);
    }
    
} catch (err) {
    console.error("\nAn error occurred during batch processing:", err);
}