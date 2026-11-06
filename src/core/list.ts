// Spread-free list edits: `list.splice(i, n, ...items)` and `list.push(...items)` pass every item as an argument,
// which throws a RangeError past ~10^5 items.

/** `list.splice(start, deleteCount, ...items)` in place, in one pass over the tail. */
export const spliceList = <T>(list: T[], start: number, deleteCount: number, items: readonly T[]): void => {
    const removed = Math.min(deleteCount, list.length - start);
    const tail = list.length - start - removed;
    const shift = items.length - removed;
    if (shift > 0) {
        for (let i = tail - 1; i >= 0; i--) list[start + items.length + i] = list[start + removed + i] as T;
    } else if (shift < 0) {
        for (let i = 0; i < tail; i++) list[start + items.length + i] = list[start + removed + i] as T;
        list.length += shift;
    }
    for (let i = 0; i < items.length; i++) list[start + i] = items[i] as T;
};

export const pushAll = <T>(list: T[], items: Iterable<T>): void => {
    for (const item of items) list.push(item);
};

/** Same length, and `===` item by item. */
export const sameItems = <T>(a: readonly T[], b: readonly T[]): boolean => a.length === b.length && a.every((item, i) => item === b[i]);
