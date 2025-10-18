import type { Logger, LogLevel } from "./types.js";

export const createLogger = (level: LogLevel = "info"): Logger => {
    const levels: Record<LogLevel, number> = {
        silent: 0,
        error: 1,
        warn: 2,
        info: 3,
        debug: 4,
    };

    const currentLevel = levels[level];

    return {
        error: (message: string, ...args: any[]) => {
            if (currentLevel >= levels.error) {
                console.error(message, ...args);
            }
        },
        warn: (message: string, ...args: any[]) => {
            if (currentLevel >= levels.warn) {
                console.warn(message, ...args);
            }
        },
        info: (message: string, ...args: any[]) => {
            if (currentLevel >= levels.info) {
                console.log(message, ...args);
            }
        },
        debug: (message: string, ...args: any[]) => {
            if (currentLevel >= levels.debug) {
                console.log(message, ...args);
            }
        },
    };
};

export const silentLogger: Logger = createLogger("silent");
export const defaultLogger: Logger = createLogger("info");
