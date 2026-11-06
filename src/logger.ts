export type LogLevel = "silent" | "error" | "warn" | "info" | "debug";

export interface Logger {
    error(message: string): void;
    warn(message: string): void;
    info(message: string): void;
    debug(message: string): void;
    /** Lets callers skip building messages. Assumed true when missing. */
    enabled?(level: Exclude<LogLevel, "silent">): boolean;
}

const LEVELS: Record<LogLevel, number> = {
    silent: 0,
    error: 1,
    warn: 2,
    info: 3,
    debug: 4,
};

/** The library default: it never writes to the console on its own. */
export const silentLogger: Logger = {
    error: () => {},
    warn: () => {},
    info: () => {},
    debug: () => {},
    enabled: () => false,
};

const MAX_LINE = 4096;
/** C0 but `\t`, DEL, C1, format (bidi, zero-width, ...) and line/paragraph separators, lone surrogates. */
// oxlint-disable-next-line no-control-regex -- matching control characters is the point
const UNSAFE = /[\0-\x08\x0a-\x1f\x7f-\x9f\p{Cf}\p{Zl}\p{Zp}\p{Cs}]/gu;
/** `UNSAFE` but line breaks: for whole texts (code) shown on a terminal. */
// oxlint-disable-next-line no-control-regex -- matching control characters is the point
const UNSAFE_IN_TEXT = /[\0-\x08\x0b\x0c\x0e-\x1f\x7f-\x9f\p{Cf}\p{Zl}\p{Zp}\p{Cs}]/gu;

const visible = (char: string): string => {
    const code = char.codePointAt(0) as number;
    return code <= 0xff ? `\\x${code.toString(16).toUpperCase().padStart(2, "0")}` : `\\u{${code.toString(16).toUpperCase()}}`;
};

/**
 * One log line as it may reach a terminal: characters a terminal acts on (escape sequences, line breaks that forge
 * lines, bidi controls) are written as `\xHH`/`\u{H}`, and the line is cut at 4 KiB with `…`.
 */
export const sanitizeLine = (text: string): string => {
    const cut = text.length > MAX_LINE;
    const clean = (cut ? text.slice(0, MAX_LINE) : text).replace(UNSAFE, visible);
    return cut || clean.length > MAX_LINE ? `${clean.slice(0, MAX_LINE - 1)}…` : clean;
};

/** A text (output code) for a terminal: as `sanitizeLine`, keeping line breaks and tabs, uncut. */
export const sanitizeText = (text: string): string => text.replace(UNSAFE_IN_TEXT, visible);

/** `write` gets each message as one sanitized line (`sanitizeLine`). */
export const createLogger = (level: LogLevel, write: (line: string) => void): Logger => {
    const threshold = LEVELS[level];
    const enabled = (messageLevel: Exclude<LogLevel, "silent">): boolean => threshold >= LEVELS[messageLevel];
    const at = (messageLevel: Exclude<LogLevel, "silent">) => (message: string) => {
        if (enabled(messageLevel)) write(sanitizeLine(message));
    };
    return {
        error: at("error"),
        warn: at("warn"),
        info: at("info"),
        debug: at("debug"),
        enabled,
    };
};
