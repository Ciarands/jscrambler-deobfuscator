import type { Argument, CallExpression, Expression, MemberExpression, Node } from "../core/ast.js";
import { isIdentifierName, propertyKey } from "../core/ast.js";
import { callOf, identifier, member, memberChain } from "../core/build.js";
import type { ScopeInfo } from "../core/scope.js";
import { traverse } from "../core/traverse.js";
import type { Pass, PassContext, PassResult } from "../pipeline/pass.js";
import type { CallAlias } from "./emulate/model.js";
import { RUNTIME } from "./emulate/model.js";
import { storageAnalysis } from "./emulate/effects.js";

type Rewrite = { readonly ok: true; readonly expression: Expression } | { readonly ok: false; readonly reason: string };

const refused = (reason: string): Rewrite => ({ ok: false, reason });

/** Whether `parent` deletes its operand. */
const isDeleted = (parent: Node | null | undefined): boolean => parent?.type === "UnaryExpression" && parent.operator === "delete";

/**
 * The builtin a call alias stands for (`String.prototype.split`, `String`), written at the reference `site`: the
 * global name it starts from must not be shadowed there.
 */
const builtin = (alias: CallAlias, scopes: ScopeInfo, site: Node, origin: Node): Rewrite => {
    const [first, ...rest] = [...alias.owner, alias.original];
    if (first === undefined || !isIdentifierName(first)) return refused(`${first ?? "the global object"} can't be named`);
    const bound = scopes.nameBoundAt(site, first);
    if (bound === undefined) return refused("call site is not in the analysed program");
    if (bound) return refused(`${first} is shadowed here`);
    return { ok: true, expression: memberChain(identifier(first, origin), rest, origin) };
};

/** `G.alias(...)` as the builtin call it stands for. `site` is the reference to `G`. */
const rewriteCall = (call: CallExpression, alias: CallAlias, scopes: ScopeInfo, site: Node): Rewrite => {
    const args = call.arguments;
    if (args.length === 0) return builtin(alias, scopes, site, call);
    if (alias.style !== "method") {
        const target = builtin(alias, scopes, site, call.callee);
        if (!target.ok) return target;
        // "static": Owner.original(...args); "call": Owner.original.call(receiver, ...rest).
        return { ok: true, expression: callOf(alias.style === "static" ? target.expression : member(target.expression, "call", call.callee), args, call) };
    }
    const [receiver, ...rest] = args as [Argument, ...Argument[]];
    if (receiver.type === "SpreadElement") return refused("receiver is a spread");
    if ((receiver.type === "Literal" && receiver.value === null) || (receiver.type === "Identifier" && receiver.name === "undefined")) {
        return refused("receiver is null or undefined");
    }
    return { ok: true, expression: callOf(member(receiver, alias.original, call.callee), rest, call) };
};

/**
 * Aliases: undo the builtin aliases the prelude's setup function created (recorded by `emulate`).
 *
 * - Global aliases, `S` -> `String` (also values: `I` -> `Infinity`).
 * - Builtin-owned property aliases, `s.p("%")` -> `s.split("%")`, `S.q(...)` -> `String.fromCharCode(...)`;
 *   only for alias names that stand for exactly one builtin property.
 * - Call aliases on the storage object (newer setup variant): `G.a(s, "%")` -> `s.split("%")`,
 *   `G.b(72)` -> `String.fromCharCode(72)`, `G.c()` -> `Array.prototype.unshift`.
 * - Host aliases, global accessors forwarding to a host object: `D` -> `document`, `A(x)` -> `atob(x)`, reads,
 *   writes and calls (model 10: the host globals the script uses exist, so the bare name reads what the getter did).
 *
 * Other writes are never rewritten, and a global name is only introduced where no local of that name is in scope. The
 * setup call and function are left for cleanup, which can check that no alias use remains.
 */
export const aliases: Pass = {
    name: "aliases",
    description: "Replace the prelude's builtin aliases with the builtins they stand for",
    run({ program, log, facts, scope }: PassContext): PassResult {
        const runtime = facts.get(RUNTIME);
        if (runtime === undefined || (runtime.aliases.length === 0 && runtime.callAliases.size === 0 && runtime.hostAliases.size === 0)) {
            log.info("no aliases known, nothing to do");
            return { changed: 0 };
        }
        const scopes = scope();
        const { matcher, effects } = storageAnalysis(program, runtime, scopes, log);
        const { isStorage } = matcher;

        const globals = new Map<string, string>();
        const candidates = new Map<string, Set<string>>();
        for (const { owner, alias, original } of runtime.aliases) {
            if (owner.length === 0) {
                if (isIdentifierName(original)) globals.set(alias, original);
                continue;
            }
            const set = candidates.get(alias) ?? new Set<string>();
            set.add(original);
            candidates.set(alias, set);
        }
        const properties = new Map<string, string>();
        for (const [alias, originals] of candidates) {
            const [only] = originals;
            if (originals.size === 1 && only !== undefined) properties.set(alias, only);
            else log.warn(`alias .${alias} stands for ${[...originals].join(" and ")}, left as is`);
        }

        const counts = { globals: 0, properties: 0, calls: 0, hosts: 0, refused: 0 };
        const refuse = (reason: string, node: Node) => {
            counts.refused++;
            log.debug(`kept: ${reason}`, node);
        };
        /**
         * Host aliases the program may delete or redefine: a `delete` of the name or of a property by that name, or the
         * name as a string (`Object.defineProperty(window, "D", ...)`), outside the setup calls that define them.
         * Their uses stay as they are.
         */
        const tampered = new Set<string>();
        if (runtime.hostAliases.size > 0) {
            traverse(program, {
                enter(path) {
                    if (runtime.setup.has(path.node)) path.skip();
                },
                UnaryExpression(path) {
                    const argument = path.node.argument;
                    if (path.node.operator !== "delete") return;
                    const name = argument.type === "Identifier" ? argument.name : argument.type === "MemberExpression" ? propertyKey(argument) : undefined;
                    if (name !== undefined && runtime.hostAliases.has(name)) tampered.add(name);
                },
                Literal(path) {
                    const value = path.node.value;
                    if (typeof value === "string" && runtime.hostAliases.has(value)) tampered.add(value);
                },
            });
        }

        traverse(program, {
            CallExpression(path) {
                const call = path.node;
                const callee = call.callee;
                if (callee.type !== "MemberExpression" || !isStorage(callee.object)) return;
                const key = propertyKey(callee);
                const alias = key === undefined ? undefined : runtime.callAliases.get(key);
                if (alias === undefined || key === undefined) return;
                const stale = effects.staleAt(callee.object, [key]);
                if (stale !== undefined) return refuse(stale.reason, stale.node);
                const result = rewriteCall(call, alias, scopes, callee.object);
                if (!result.ok) return refuse(result.reason, call);
                path.replace(result.expression);
                counts.calls++;
            },
            MemberExpression(path) {
                const node = path.node as MemberExpression;
                const key = propertyKey(node);
                const host = key === undefined ? undefined : runtime.hostAliases.get(key);
                if (host !== undefined && node.object.type === "Identifier" && node.object.name === "globalThis" && scopes.isGlobalReference(node.object)) {
                    if (key !== undefined && tampered.has(key)) return refuse("the program deletes the alias or names it as a string (it may redefine it)", node);
                    if (isDeleted(path.parent)) return refuse("deleting the alias isn't deleting what it stands for", node);
                    path.replace(member(node.object, host, node));
                    counts.hosts++;
                    return;
                }
                const original = key === undefined ? undefined : properties.get(key);
                if (original === undefined || path.isWriteTarget()) return;
                path.replace(member(node.object, original, node));
                counts.properties++;
            },
            Identifier(path) {
                const node = path.node;
                const host = runtime.hostAliases.get(node.name);
                if (host !== undefined && scopes.isGlobalReference(node)) {
                    if (tampered.has(node.name)) return refuse("the program deletes the alias or names it as a string (it may redefine it)", node);
                    if (isDeleted(path.parent)) return refuse("deleting the alias isn't deleting what it stands for", node);
                    if (!isIdentifierName(host)) return refuse(`${host} can't be written as a name`, node);
                    if (scopes.nameBoundAt(node, host) !== false) return refuse(`${host} is shadowed here`, node);
                    path.replace(identifier(host, node));
                    counts.hosts++;
                    return;
                }
                const original = globals.get(node.name);
                if (original === undefined || !scopes.isGlobalReference(node) || path.isWriteTarget()) return;
                if (scopes.nameBoundAt(node, original) !== false) return refuse(`${original} is shadowed here`, node);
                path.replace(identifier(original, node));
                counts.globals++;
            },
        });

        log.info(`replaced ${counts.globals} global alias(es), ${counts.properties} property alias(es), ${counts.calls} call alias(es), ${counts.hosts} host alias(es); kept ${counts.refused}`);
        // The rewrites only remove references and add ones to globals no local binds here (checked above), so the scope
        // analysis stays valid for every binding.
        return { changed: counts.globals + counts.properties + counts.calls + counts.hosts, bindingsChanged: false, stats: counts };
    },
};
