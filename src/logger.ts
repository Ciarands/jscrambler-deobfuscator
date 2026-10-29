export type LogLevel = "silent" | "error" | "warn" | "info" | "debug";

export interface Logger {
    error(message: string): void;
    warn(message: string): void;
    info(message: string): void;
    debug(message: string): void;
}

const LEVELS: Record<LogLevel, number> = {
    silent: 0,
    error: 1,
    warn: 2,
    info: 3,
    debug: 4,
};

/** Logger that drops everything. The library default: it never writes to the console on its own. */
export const silentLogger: Logger = {
    error: () => {},
    warn: () => {},
    info: () => {},
    debug: () => {},
};

/** Logger that writes every message at or above `level` to `write` (one line per call). */
export const createLogger = (level: LogLevel, write: (line: string) => void): Logger => {
    const threshold = LEVELS[level];
    const at = (messageLevel: Exclude<LogLevel, "silent">) => (message: string) => {
        if (threshold >= LEVELS[messageLevel]) write(message);
    };
    return {
        error: at("error"),
        warn: at("warn"),
        info: at("info"),
        debug: at("debug"),
    };
};
