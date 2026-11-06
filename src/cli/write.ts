import { randomBytes } from "node:crypto";
import fs from "node:fs";
import path from "node:path";

/** Why `target` can't be written; `undefined` when it can. A symbolic link is never written through, even with `force`. */
export const blockedTarget = (target: string, force: boolean): string | undefined => {
    const existing = fs.lstatSync(target, { throwIfNoEntry: false });
    if (existing === undefined) return undefined;
    if (existing.isSymbolicLink()) return "is a symbolic link";
    if (!existing.isFile()) return "exists and is not a file";
    return force ? undefined : "already exists, use --force to overwrite";
};

const NO_HARD_LINKS: Record<string, true> = { EPERM: true, ENOTSUP: true, ENOSYS: true, EXDEV: true, EINVAL: true };

/**
 * Writes `content` to a new file next to `target`, then moves it into place: a run that fails leaves no partial
 * output. Without `force` the move fails when anything exists at `target` by then (a link, not a rename).
 */
export const writeOutput = (target: string, content: string, force: boolean, label: string): void => {
    const blocked = blockedTarget(target, force);
    if (blocked !== undefined) throw new Error(`${JSON.stringify(label)} ${blocked}`);
    fs.mkdirSync(path.dirname(target), { recursive: true });
    const temp = path.join(path.dirname(target), `.${path.basename(target)}.${process.pid}.${randomBytes(6).toString("hex")}.tmp`);
    try {
        fs.writeFileSync(temp, content, { flag: "wx" });
        if (force) {
            fs.renameSync(temp, target);
            return;
        }
        try {
            fs.linkSync(temp, target);
        } catch (error) {
            if (NO_HARD_LINKS[(error as NodeJS.ErrnoException).code ?? ""] !== true) throw error;
            fs.writeFileSync(target, content, { flag: "wx" });
        }
        fs.unlinkSync(temp);
    } catch (error) {
        fs.rmSync(temp, { force: true });
        if ((error as NodeJS.ErrnoException).code === "EEXIST") throw new Error(`${JSON.stringify(label)} already exists, use --force to overwrite`, { cause: error });
        throw error;
    }
};
