/** @type {import('jest').Config} */
module.exports = {
    preset: "ts-jest",
    testEnvironment: "node",
    roots: ["<rootDir>"],
    testMatch: ["**/*.test.ts"],
    moduleFileExtensions: ["ts", "tsx", "js", "jsx", "json", "node"],
    transform: {
        "^.+\\.(ts|tsx)$": ["ts-jest", { tsconfig: "tsconfig.jest.json", useESM: false, diagnostics: { ignoreCodes: [151002] } }],
    },
    moduleNameMapper: {
        "^(\\.{1,2}/.*)\\.js$": "$1",
    },
    collectCoverageFrom: ["src/**/*.ts", "!src/**/*.d.ts"],
};
