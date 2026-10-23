// Untrusted name lookup: declaration identity is independent of source modules.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
export class AmbiguousNameError extends Error {
  readonly identifier: string;
  readonly candidates: readonly string[];
  constructor(identifier: string, candidates: readonly string[]) {
    super(`ambiguous name ${identifier}; qualify one of: ${candidates.join(", ")}`);
    this.name = "AmbiguousNameError";
    this.identifier = identifier; this.candidates = candidates;
  }
}

interface CachedCandidates { revision: number; names: readonly string[] }
// A name's dotted prefixes, longest first, computed once per distinct name:
// owner lookups run for every resolution candidate, and slicing the string
// each time was most of their cost.
const prefixChains = new Map<string, readonly string[]>();
function prefixChain(name: string): readonly string[] {
  let chain = prefixChains.get(name);
  if (!chain) {
    const parts: string[] = [];
    for (let current = name; current;) {
      parts.push(current);
      const dot = current.lastIndexOf(".");
      if (dot < 0) break;
      current = current.slice(0, dot);
    }
    chain = parts;
    if (prefixChains.size > 262_144) prefixChains.clear();
    prefixChains.set(name, chain);
  }
  return chain;
}

/** A namespace segment `arityN` holding a declaration overloaded at that arity in its module. */
const OVERLOAD_NAMESPACE = /\.arity\d+$/u;

export class NameResolutionIndex {
  private roots = new Set<string>();
  private suffixPrefixes = new Map<string, Set<string>>();
  /**
   * The prefixes ending in an overload namespace `arityN`, by suffix: a
   * declaration under `Module.arity1` answers to its name wherever `Module`
   * is open, so a name declared twice at different arities resolves by arity.
   */
  private overloadPrefixes = new Map<string, Set<string>>();
  private openSets = new WeakMap<readonly string[], ReadonlySet<string>>();
  private revisions = new Map<string, number>();
  private serial = 0;
  private openKeys = new WeakMap<readonly string[], string>();
  private lexicalPrefixes = new WeakMap<readonly string[], readonly string[]>();
  private plans = new Map<string, Map<string, CachedCandidates>>();
  readonly owners = new Map<string, string>();
  readonly namespaceOwners = new Map<string, Set<string>>();
  // The owner of a name is asked for every visibility test of every
  // resolution candidate; an answer stands until a name is registered, which
  // the serial records, so a burst of lookups between registrations is served
  // from here.
  private ownerCache = new Map<string, { serial: number; owner: string | undefined }>();

  fork(): NameResolutionIndex {
    const copy = new NameResolutionIndex();
    copy.roots = new Set(this.roots);
    for (const [suffix, prefixes] of this.suffixPrefixes) copy.suffixPrefixes.set(suffix, new Set(prefixes));
    for (const [suffix, prefixes] of this.overloadPrefixes) copy.overloadPrefixes.set(suffix, new Set(prefixes));
    copy.revisions = new Map(this.revisions);
    copy.serial = this.serial;
    for (const [name, owner] of this.owners) copy.owners.set(name, owner);
    for (const [name, owners] of this.namespaceOwners) copy.namespaceOwners.set(name, new Set(owners));
    return copy;
  }

  private indexSuffixes(name: string): void {
    for (let dot = name.indexOf("."); dot >= 0; dot = name.indexOf(".", dot + 1)) {
      const suffix = name.slice(dot + 1);
      const prefix = name.slice(0, dot);
      let prefixes = this.suffixPrefixes.get(suffix);
      if (!prefixes) { prefixes = new Set(); this.suffixPrefixes.set(suffix, prefixes); }
      prefixes.add(prefix);
      if (OVERLOAD_NAMESPACE.test(prefix)) {
        let overloads = this.overloadPrefixes.get(suffix);
        if (!overloads) { overloads = new Set(); this.overloadPrefixes.set(suffix, overloads); }
        overloads.add(prefix);
      }
    }
  }

  register(name: string, module?: string): void {
    if (this.roots.has(name)) return;
    this.roots.add(name);
    this.indexSuffixes(name);
    if (module) this.owners.set(name, module);
    const revision = ++this.serial;
    // A cached Foo.equation lookup also depends on registrations of Foo.
    for (let start = 0;;) {
      this.revisions.set(name.slice(start), revision);
      const next = name.indexOf(".", start);
      if (next < 0) break;
      start = next + 1;
    }
    for (let end = name.indexOf("."); end >= 0; end = name.indexOf(".", end + 1))
      this.registerNamespace(name.slice(0, end), module);
  }

  registerNamespace(name: string, module?: string): void {
    for (let current = name; current;) {
      const owners = this.namespaceOwners.get(current) ?? new Set<string>();
      if (!this.namespaceOwners.has(current)) {
        this.indexSuffixes(current);
        const revision = ++this.serial;
        for (let start = 0;;) {
          this.revisions.set(current.slice(start), revision);
          const next = current.indexOf(".", start);
          if (next < 0) break;
          start = next + 1;
        }
      }
      owners.add(module ?? "");
      this.namespaceOwners.set(current, owners);
      const dot = current.lastIndexOf(".");
      if (dot < 0) break;
      current = current.slice(0, dot);
    }
  }

  /** The declarations of a name under the overload namespaces `arityN` of a namespace. */
  private overloadSiblings(parent: string, name: string): string[] {
    const result: string[] = [];
    for (const prefix of this.overloadPrefixes.get(name) ?? []) {
      if (prefix.slice(0, prefix.lastIndexOf(".")) === parent) result.push(prefix + "." + name);
    }
    return result;
  }

  owner(name: string): string | undefined {
    const cached = this.ownerCache.get(name);
    if (cached !== undefined && cached.serial === this.serial) return cached.owner;
    let owner: string | undefined;
    for (const prefix of prefixChain(name)) {
      if (this.roots.has(prefix)) { owner = this.owners.get(prefix); break; }
    }
    if (cached) { cached.serial = this.serial; cached.owner = owner; }
    else {
      if (this.ownerCache.size > 65_536) this.ownerCache.clear();
      this.ownerCache.set(name, { serial: this.serial, owner });
    }
    return owner;
  }

  private known(name: string): boolean {
    if (this.namespaceOwners.has(name)) return true;
    for (let current = name; current;) {
      if (this.roots.has(current)) return true;
      const dot = current.lastIndexOf(".");
      if (dot < 0) break;
      current = current.slice(0, dot);
    }
    return false;
  }

  private revision(name: string): number {
    let result = this.revisions.get(name) ?? 0;
    for (let end = name.indexOf("."); end >= 0; end = name.indexOf(".", end + 1))
      result = Math.max(result, this.revisions.get(name.slice(0, end)) ?? 0);
    return result;
  }

  private openedCandidates(name: string, opens: readonly string[]): readonly string[] {
    let key = this.openKeys.get(opens);
    if (key === undefined) { key = opens.join("\u0000"); this.openKeys.set(opens, key); }
    let plan = this.plans.get(key);
    if (!plan) {
      if (this.plans.size >= 256) this.plans.delete(this.plans.keys().next().value!);
      plan = new Map(); this.plans.set(key, plan);
    }
    const revision = this.revision(name);
    const cached = plan.get(name);
    if (cached?.revision === revision) return cached.names;
    let openSet = this.openSets.get(opens);
    if (!openSet) { openSet = new Set(opens); this.openSets.set(opens, openSet); }
    const matched = new Set<string>();
    // Generated properties inherit their declaration root, e.g. fn.equation.
    for (let end = name.length;;) {
      const prefixes = this.suffixPrefixes.get(name.slice(0, end));
      if (prefixes) {
        const smaller = prefixes.size < openSet.size ? prefixes : openSet;
        const larger = smaller === prefixes ? openSet : prefixes;
        for (const prefix of smaller) if (larger.has(prefix)) matched.add(prefix + "." + name);
      }
      // An overload namespace is open wherever its module is.
      for (const prefix of this.overloadPrefixes.get(name.slice(0, end)) ?? []) {
        if (openSet.has(prefix.slice(0, prefix.lastIndexOf(".")))) matched.add(prefix + "." + name);
      }
      end = name.lastIndexOf(".", end - 1);
      if (end < 0) break;
    }
    // An opened module namespace also answers to its own last segment, so
    // that `Multigraph.EulerTrail` finds Grace.Cumulus.GraphTheory.Multigraph.EulerTrail
    // once that module is open, as a reader of `import GraphTheory` expects.
    let names = [...matched].filter(candidate => this.known(candidate));
    if (names.length === 0) {
      const qualified = new Set<string>();
      for (const open of openSet) {
        const last = open.slice(open.lastIndexOf(".") + 1);
        if (name.length > last.length + 1 && name.startsWith(`${last}.`)) qualified.add(`${open}.${name.slice(last.length + 1)}`);
      }
      names = [...qualified].filter(candidate => this.known(candidate));
    }
    if (plan.size >= 2048) plan.delete(plan.keys().next().value!);
    plan.set(name, { revision, names });
    return names;
  }

  resolve(name: string, namespaces: readonly string[], opens: readonly string[],
    exists: (name: string) => boolean, visible?: (name: string) => boolean): string | undefined {
    const present = (candidate: string) => (!visible || visible(candidate)) && exists(candidate);
    if (name.startsWith("_root_.")) {
      const absolute = name.slice(7);
      return present(absolute) ? absolute : undefined;
    }
    let prefixes = this.lexicalPrefixes.get(namespaces);
    if (!prefixes) {
      prefixes = namespaces.map((_, index) => namespaces.slice(0, index + 1).join(".") + ".").reverse();
      this.lexicalPrefixes.set(namespaces, prefixes);
    }
    for (const prefix of prefixes) {
      const candidate = prefix + name;
      // A declaration overloaded at another arity in the same namespace
      // rivals the lexical candidate; the caller's filter decides by arity,
      // and the ambiguity that remains is settled by the goal.
      const siblings = this.overloadSiblings(prefix.slice(0, -1), name).filter(present);
      if (present(candidate)) {
        if (siblings.length) throw new AmbiguousNameError(name, [candidate, ...siblings].sort());
        return candidate;
      }
      if (siblings.length > 1) throw new AmbiguousNameError(name, siblings.sort());
      if (siblings.length === 1) return siblings[0];
    }
    const candidates = this.openedCandidates(name, opens).filter(present);
    if (candidates.length > 1) throw new AmbiguousNameError(name, candidates.sort());
    if (candidates.length === 1) return candidates[0];
    return present(name) ? name : undefined;
  }
}
