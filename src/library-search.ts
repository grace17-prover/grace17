// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Incremental local declaration search, shared by the Workbench search
// worker (through workbench/library-search.js) and the machine interface.
// Retrieval never establishes a proof.

const normalize = (value: string): string => value.normalize("NFKC").toLocaleLowerCase("en");
const grams = (text: string): Set<string> => new Set(Array.from({ length: Math.max(0, text.length - 2) }, (_, i) => text.slice(i, i + 3)));
const tokens = (text: string): string[] => text.match(/\?[\p{L}_][\p{L}\p{N}_.]*|[\p{L}\p{N}_][\p{L}\p{N}_.]*|[^\s]/gu) || [];
const declaration = /^(?:(?:noncomputable|transfinite|foundation|well-founded)\s+)*(defgraph|defchoose|defunique|def|define|predicate|class|datatype|structure|theorem|lemma|instance)\s+([^\s({:]+)/u;

/** One source declaration as the search index records it. */
export interface SearchDeclaration {
  /** The namespace-qualified name as written, without the module prefix. */
  readonly name: string;
  readonly short: string;
  readonly kind: string;
  readonly file: string;
  readonly module: string;
  readonly line: number;
  /** The declaration header up to its proof, one line per source line. */
  readonly signature: string;
  /** The `shows` clause, or the whole signature for a declaration without one. */
  readonly conclusion: string;
  /** The comment lines immediately above the declaration. */
  readonly documentation: string;
  /** Section variables and hypotheses in scope at the declaration. */
  readonly context: string;
}

export interface SearchCriterion {
  readonly field: "text" | "name" | "module" | "kind" | "symbol" | "conclusion" | "pattern";
  readonly value: string;
  readonly exclude: boolean;
}

export interface SearchResult {
  readonly total: number;
  readonly indexed: number;
  readonly candidates: number;
  readonly cached: boolean;
  readonly milliseconds: number;
  readonly results: readonly SearchDeclaration[];
}

export interface SearchBudget { remaining: number }

interface SearchRecord extends SearchDeclaration {
  readonly text: string;
  readonly trigrams: Set<string>;
  /** The normalized tokens of the conclusion, for pattern criteria. */
  readonly conclusionTokens: Set<string>;
}

/**
 * The qualified module a workbench file declares. A bare `module Name` under
 * the library takes its qualification from the file's path, as the checker
 * does: lib/Grace/Cumulus/Real/FiniteSum.g17 is Grace.Cumulus.Real.FiniteSum.
 */
export function moduleNameOf(source: string, file = ""): string | undefined {
  const declared = /^\s*module\s+(\S+)/m.exec(source)?.[1];
  if (!declared || declared.includes(".")) return declared;
  const under = /(?:^|\/)lib\/(.+)\.g17$/.exec(String(file).replaceAll("\\", "/"));
  if (!under) return declared;
  const segments = under[1]!.split("/");
  return segments[segments.length - 1] === declared ? segments.join(".") : declared;
}

export function scanSearchDeclarations(file: string, source: string): SearchDeclaration[] {
  const lines = source.split(/\r?\n/), found: SearchDeclaration[] = [], scopes: [number, number][] = [], namespaces: string[] = [], context: string[] = [];
  const module = moduleNameOf(source, file) || file;
  let comments: string[] = [];
  for (let i = 0; i < lines.length; i++) {
    const raw = lines[i]!.trim(), line = raw.replace(/--.*$/, "").trim();
    if (raw.startsWith("--")) { comments.push(raw.replace(/^--\s?/, "")); continue; }
    const ns = /^namespace\s+(\S+)/.exec(line);
    if (ns || /^section(?:\s|$)/.test(line)) {
      scopes.push([namespaces.length, context.length]);
      if (ns) namespaces.push(...ns[1]!.split("."));
      comments = []; continue;
    }
    if (/^end(?:\s|$)/.test(line)) {
      const [n, c] = scopes.pop() || [0, 0]; namespaces.length = n; context.length = c;
      comments = []; continue;
    }
    if (/^(variable|hypothesis|notation ring)\s/.test(line)) context.push(line);
    const match = declaration.exec(line);
    if (!match) { if (line) comments = []; continue; }
    const header = [line];
    let j = i + 1;
    while (j < lines.length && (/^\s+\S/.test(lines[j]!) || !lines[j]!.trim())) {
      const next = lines[j]!.trim();
      if (/^(proof|uniqueness|termination|typeproof)\b/.test(next)) break;
      if (next && !next.startsWith("--")) {
        const piece = next.replace(/--.*$/, "").trim();
        // A binder list wrapped onto the lines beneath the header is one line of the signature.
        if (header.length === 1 && openParentheses(header[0]!) > 0) header[0] = `${header[0]} ${piece}`;
        else header.push(piece);
      }
      j++;
    }
    const signature = header.join("\n"), statement = /\bshows\s+([\s\S]*)/.exec(signature)?.[1] || signature;
    found.push({ name: [...namespaces, match[2]!].join("."), short: match[2]!, kind: match[1]!,
      file, module, line: i + 1, signature, conclusion: statement,
      documentation: comments.join("\n"), context: context.join("\n") });
    comments = [];
  }
  return found;
}

/** One parameter of a declaration header, as written. */
export interface HeaderParameter {
  readonly name: string;
  readonly type: string;
  /** `explicit` for `(x : T)`, `implicit` for `{x : T}`. */
  readonly binder: "explicit" | "implicit";
  /** `section` for a `variable` of an enclosing section, `declaration` for the header's own. */
  readonly source: "section" | "declaration";
}

/** One premise of a declaration header: a section `hypothesis` or a `requires` clause. */
export interface HeaderPremise {
  readonly name?: string;
  readonly formula: string;
  readonly source: "section" | "declaration";
}

/**
 * A declaration header read from its source text: the parameters in the
 * order the elaborated statement quantifies them (section variables first),
 * the premises in the order an `at`/`with` list supplies them (section
 * hypotheses first, then `requires` clauses), and the conclusion.
 */
export interface DeclarationHeader {
  readonly kind: string;
  readonly name: string;
  readonly parameters: readonly HeaderParameter[];
  readonly premises: readonly HeaderPremise[];
  readonly conclusion: string;
  /** The `notation ring` scopes in force at the declaration. */
  readonly rings: readonly string[];
}

/** The binder groups at the start of a header, and the text that follows them. */
export function parseHeaderBinders(text: string, source: HeaderParameter["source"]): { readonly parameters: HeaderParameter[]; readonly rest: string } {
  const parameters: HeaderParameter[] = [];
  let offset = 0;
  while (offset < text.length) {
    while (/\s/.test(text[offset] ?? "")) offset += 1;
    const open = text[offset];
    if (open !== "(" && open !== "{") break;
    const close = open === "(" ? ")" : "}";
    let depth = 0, end = -1;
    for (let index = offset; index < text.length; index += 1) {
      if (text[index] === open) depth += 1;
      else if (text[index] === close) depth -= 1;
      if (depth === 0) { end = index; break; }
    }
    if (end < 0) break;
    // A group holds comma-separated segments, each `names : Type` or the
    // bounded `names ∈ Bound`, as the elaborator reads `(x : Set, n : Nat)`.
    for (const segment of splitTopLevelCommas(text.slice(offset + 1, end))) {
      const bounded = /^\s*([^:]+?)\s+(?:∈|in)\s+(.+?)\s*$/u.exec(segment);
      const typed = bounded ? null : /^\s*(.+?)\s*:\s*(.+?)\s*$/u.exec(segment);
      const names = ((bounded ?? typed)?.[1] ?? segment).trim().split(/\s+/).filter(Boolean);
      const type = bounded ? `∈ ${bounded[2]!.trim()}` : typed ? typed[2]!.trim() : "Set";
      for (const name of names) parameters.push({ name, type, binder: open === "{" ? "implicit" : "explicit", source });
    }
    offset = end + 1;
  }
  return { parameters, rest: text.slice(offset).trim() };
}

function splitTopLevelCommas(text: string): string[] {
  const parts: string[] = [];
  let depth = 0, start = 0;
  for (let index = 0; index < text.length; index += 1) {
    const character = text[index]!;
    if ("([{⟨".includes(character)) depth += 1;
    else if (")]}⟩".includes(character)) depth = Math.max(0, depth - 1);
    else if (character === "," && depth === 0) { parts.push(text.slice(start, index)); start = index + 1; }
  }
  parts.push(text.slice(start));
  return parts.filter(part => part.trim());
}

export function parseDeclarationHeader(record: Pick<SearchDeclaration, "kind" | "short" | "signature" | "context">): DeclarationHeader {
  const parameters: HeaderParameter[] = [];
  const premises: HeaderPremise[] = [];
  const rings: string[] = [];
  for (const line of record.context.split("\n").filter(Boolean)) {
    const variable = /^variable\s+(.*)$/.exec(line);
    const hypothesis = /^hypothesis\s+([^\s:]+)\s*:\s*(.*)$/.exec(line);
    const ring = /^notation ring\s+(\S+)/.exec(line);
    if (variable) parameters.push(...parseHeaderBinders(variable[1]!, "section").parameters);
    else if (hypothesis) premises.push({ name: hypothesis[1]!, formula: hypothesis[2]!, source: "section" });
    else if (ring) rings.push(ring[1]!);
  }
  // Clauses may continue over indented lines; the scanner trimmed them.
  const clauses: string[] = [];
  for (const line of record.signature.split("\n")) {
    if (clauses.length === 0 || /^(requires|shows)\b/.test(line)) clauses.push(line);
    else clauses[clauses.length - 1] += ` ${line}`;
  }
  const header = /^(?:(?:noncomputable|transfinite|foundation|well-founded)\s+)*\S+\s+\S+\s*(.*)$/.exec(clauses[0]!);
  const own = parseHeaderBinders(header?.[1] ?? "", "declaration");
  parameters.push(...own.parameters);
  let conclusion = own.rest;
  for (const clause of clauses.slice(1)) {
    const requirement = /^requires\s+(?:([\p{L}_][\p{L}\p{M}\p{N}_]*)\s*:\s*)?(.+)$/u.exec(clause);
    const shows = /^shows\s+(.*)$/.exec(clause);
    if (requirement) premises.push({ ...(requirement[1] ? { name: requirement[1] } : {}), formula: requirement[2]!.trim(), source: "declaration" });
    else if (shows) conclusion = shows[1]!.trim();
  }
  return { kind: record.kind, name: record.short, parameters, premises, conclusion, rings };
}

/** A filter token starting at the cursor: `name:`, `-module:`, and so on. */
const nextFilter = /^-?(?:name|module|kind|symbol|conclusion|pattern):/u;

/** The wildcard tokens of a pattern: `_` and `?x`. */
const isWildcard = (token: string): boolean => token === "_" || token.startsWith("?");

/** The pieces of a written name: `mul_eq_zero` is `mul`, `eq`, `zero`; a dotted name is one piece. */
const namePieces = (value: string): string[] => value.split(/[_\s]+/u).filter(Boolean);

/** Whether a name holds every piece, in order: `mul.eq_zero_iff` holds `mul`, `eq`, `zero`. */
function holdsPieces(name: string, pieces: readonly string[]): boolean {
  let from = 0;
  for (const piece of pieces) {
    const at = name.indexOf(piece, from);
    if (at < 0) return false;
    from = at + piece.length;
  }
  return true;
}

/**
 * The token shape of a conclusion, with one enclosing pair of parentheses
 * removed, so `(A ⊆ C)` and `A ⊆ C` have the same shape.
 */
function conclusionShape(text: string): string {
  let parts = tokens(normalize(text));
  if (parts.length >= 2 && parts[0] === "(" && parts[parts.length - 1] === ")") {
    let depth = 0, enclosing = true;
    for (let index = 0; index < parts.length - 1 && enclosing; index += 1) {
      if (parts[index] === "(") depth += 1;
      else if (parts[index] === ")") depth -= 1;
      if (depth === 0) enclosing = false;
    }
    if (enclosing) parts = parts.slice(1, -1);
  }
  return parts.join(" ");
}

export function parseSearchQuery(query: string): SearchCriterion[] {
  if (query.length > 1024) throw new Error("Search queries are limited to 1,024 characters.");
  const criteria: SearchCriterion[] = [];
  let pos = 0;
  while (pos < query.length) {
    if (/\s/.test(query[pos]!)) { pos++; continue; }
    let exclude = false;
    if (query[pos] === "-") { exclude = true; pos++; }
    const fieldMatch = /^(name|module|kind|symbol|conclusion|pattern):/u.exec(query.slice(pos));
    let field: SearchCriterion["field"] = "text";
    let spaced = false;
    if (fieldMatch) {
      field = fieldMatch[1] as SearchCriterion["field"]; pos += fieldMatch[0].length;
      // A value may follow its field after whitespace; a formula field's
      // value then runs to the next filter, so `conclusion: _ = 0 ∨ _ = 0`
      // is one conclusion criterion.
      while (pos < query.length && /\s/.test(query[pos]!)) { pos++; spaced = true; }
    }
    else if (/^\w+:/u.test(query.slice(pos))) throw new Error("Unknown filter. Use name:, module:, kind:, symbol:, conclusion:, or pattern:.");
    let value = "";
    if (query[pos] === '"') {
      pos++;
      while (pos < query.length && query[pos] !== '"') {
        if (query[pos] === "\\" && ['"', "\\"].includes(query[pos + 1]!)) pos++;
        value += query[pos++];
      }
      if (query[pos] !== '"') throw new Error("Close the quoted search phrase.");
      pos++;
    } else if (spaced && (field === "conclusion" || field === "pattern")) {
      while (pos < query.length && !nextFilter.test(query.slice(pos))) value += query[pos++];
      value = value.trim();
    } else {
      while (pos < query.length && !/\s/.test(query[pos]!)) value += query[pos++];
    }
    if (!value) throw new Error("Give each filter a value.");
    criteria.push({ field, value: normalize(value), exclude });
  }
  if (criteria.length > 24) throw new Error("Use at most 24 search criteria.");
  return criteria;
}

// Patterns match source tokens; there is no elaborated or type-directed
// unification. Wildcards
// bind nonempty balanced token spans; ?x repeats must bind identical spans.
export function matchesSourcePattern(text: string, pattern: string, budget: SearchBudget = { remaining: 20000 }): boolean {
  const hay = tokens(normalize(text)), needle = tokens(normalize(pattern));
  if (needle.length > 128) throw new Error("Patterns are limited to 128 tokens. Use a shorter pattern and another filter.");
  if (!needle.length) return false;
  const walk = (i: number, j: number, bindings: Map<string, string[]>): boolean => {
    if (--budget.remaining < 0) throw new Error("Pattern search budget reached. Add a name:, module:, or symbol: filter.");
    if (j === needle.length) return true;
    if (i === hay.length) return false;
    const part = needle[j]!;
    if (part !== "_" && !part.startsWith("?")) return hay[i] === part && walk(i + 1, j + 1, bindings);
    const previous = bindings.get(part);
    if (previous) return previous.every((t, k) => hay[i + k] === t) && walk(i + previous.length, j + 1, bindings);
    const stack: string[] = [];
    for (let end = i; end < Math.min(hay.length, i + 64); end++) {
      const t = hay[end]!, closing = ({ ")": "(", "]": "[", "}": "{", "⟩": "⟨" } as Record<string, string>)[t];
      if (closing) { if (stack.pop() !== closing) break; }
      else if (["(", "[", "{", "⟨"].includes(t)) stack.push(t);
      if (stack.length) continue;
      const next = new Map(bindings);
      if (part !== "_") next.set(part, hay.slice(i, end + 1));
      if (walk(end + 1, j + 1, next)) return true;
    }
    return false;
  };
  for (let i = 0; i < hay.length; i++) if (walk(i, 0, new Map())) return true;
  return false;
}

export class LibrarySearchIndex {
  files = new Map<string, { source: string; ids: number[] }>();
  records = new Map<number, SearchRecord>();
  postings = new Map<string, Set<number>>();
  cache = new Map<string, SearchResult>();
  nextId = 0;
  updateFile(file: string, source: string): boolean {
    if (this.files.get(file)?.source === source) return false;
    this.removeFile(file);
    const ids: number[] = [];
    for (const item of scanSearchDeclarations(file, source)) {
      const id = this.nextId++, text = normalize([item.name, item.module, item.kind, item.signature, item.context, item.documentation].join("\n"));
      const trigrams = grams(text);
      this.records.set(id, { ...item, text, trigrams, conclusionTokens: new Set(tokens(normalize(item.conclusion))) }); ids.push(id);
      for (const gram of trigrams) { if (!this.postings.has(gram)) this.postings.set(gram, new Set()); this.postings.get(gram)!.add(id); }
    }
    this.files.set(file, { source, ids }); this.cache.clear(); return true;
  }
  removeFile(file: string): void {
    const old = this.files.get(file); if (!old) return;
    for (const id of old.ids) {
      for (const gram of this.records.get(id)!.trigrams) {
        const set = this.postings.get(gram)!; set.delete(id); if (!set.size) this.postings.delete(gram);
      }
      this.records.delete(id);
    }
    this.files.delete(file); this.cache.clear();
  }
  search(query: string, limit = 60): SearchResult {
    const started = globalThis.performance.now(), criteria = parseSearchQuery(query), key = JSON.stringify([query, limit]);
    if (this.cache.has(key)) return { ...this.cache.get(key)!, cached: true, milliseconds: globalThis.performance.now() - started };
    const lists: Set<number>[] = [];
    // A conclusion criterion with wildcards is a pattern over the conclusion;
    // a name criterion matches its pieces, so `mul_eq_zero` finds `mul.eq_zero_iff`.
    const patterned = (c: SearchCriterion): boolean => c.field === "pattern" || (c.field === "conclusion" && tokens(c.value).some(isWildcard));
    for (const c of criteria) {
      if (c.exclude) continue;
      const anchors = patterned(c) ? tokens(c.value).filter(t => !isWildcard(t)) : c.field === "name" ? namePieces(c.value) : [c.value];
      for (const value of anchors) for (const gram of grams(value)) lists.push(this.postings.get(gram) || new Set());
    }
    lists.sort((a, b) => a.size - b.size);
    const candidates = lists.length ? [...lists[0]!].filter(id => lists.every(set => set.has(id))) : [...this.records.keys()];
    const budget = { remaining: 150000 }, hits: { r: SearchRecord; score: number }[] = [];
    const shapes = new Map<string, string>();
    const shapeOf = (c: SearchCriterion): string => { if (!shapes.has(c.value)) shapes.set(c.value, conclusionShape(c.value)); return shapes.get(c.value)!; };
    for (const id of candidates) {
      const r = this.records.get(id)!;
      let matches = true, score = 0;
      for (const c of criteria) {
        const value = c.field === "conclusion" || c.field === "pattern" ? r.conclusion : c.field === "symbol" ? r.signature : c.field === "text" ? r.text : r[c.field];
        let found: boolean;
        if (patterned(c)) {
          // Every literal token of the pattern must occur before the matcher
          // spends its budget on the record.
          found = tokens(c.value).every(t => isWildcard(t) || r.conclusionTokens.has(t)) && matchesSourcePattern(value, c.value, budget);
        }
        else if (c.field === "kind") found = normalize(value) === c.value;
        else if (c.field === "symbol") found = tokens(normalize(value)).some(t => t === c.value || t.endsWith("." + c.value));
        else if (c.field === "name") found = normalize(value).includes(c.value) || holdsPieces(normalize(value), namePieces(c.value));
        else found = normalize(value).includes(c.value);
        if (found === c.exclude) { matches = false; break; }
        if (c.exclude) continue;
        if (c.field === "conclusion" || c.field === "pattern") {
          // An exact conclusion shape ranks above a conclusion that merely
          // contains the phrase; among those, the shorter conclusion first.
          const shape = conclusionShape(r.conclusion);
          const needle = tokens(c.value).length, hay = Math.max(1, tokens(shape).length);
          score += shape === shapeOf(c) ? 100 : 1 + Math.round(40 * Math.min(needle, hay) / hay);
        }
        else if (c.field === "name") {
          const name = normalize(r.name);
          score += normalize(r.short) === c.value ? 100 : name.includes(c.value) ? 20 : name.endsWith(c.value) ? 15 : 5;
        }
        else score += normalize(r.short) === c.value ? 100 : normalize(r.name).includes(c.value) ? 20 : 1;
      }
      if (matches) hits.push({ r, score });
    }
    hits.sort((a, b) => b.score - a.score || a.r.name.localeCompare(b.r.name) || a.r.file.localeCompare(b.r.file));
    const result: SearchResult = { total: hits.length, indexed: this.records.size, candidates: candidates.length, cached: false,
      milliseconds: globalThis.performance.now() - started, results: hits.slice(0, Math.max(1, Math.min(200, limit))).map(({ r }) => {
        const { text, trigrams, conclusionTokens, ...item } = r; return item;
      }) };
    this.cache.set(key, result); if (this.cache.size > 32) this.cache.delete(this.cache.keys().next().value!);
    return result;
  }
}

export class LibrarySearchWorkspace {
  index = new LibrarySearchIndex(); overlays = new Map<string, string>();
  readonly standardLibrary: ReadonlyMap<string, string>;
  constructor(standardLibrary: ReadonlyMap<string, string>) {
    this.standardLibrary = standardLibrary;
    for (const [file, source] of standardLibrary) this.index.updateFile(file, source);
  }
  sync(files: readonly { readonly name: string; readonly source: string }[]): void {
      const incoming = new Map(files.map(f => [f.name, f.source]));
      for (const name of this.overlays.keys()) if (!incoming.has(name)) {
        this.index.removeFile(name);
        if (this.standardLibrary.has(name)) this.index.updateFile(name, this.standardLibrary.get(name)!);
      }
      // Open documents may use a different path for the same library module.
      const modules = new Set([...incoming].map(([name, text]) => moduleNameOf(text, name)).filter(Boolean));
      for (const [file, source] of this.standardLibrary) {
        const module = moduleNameOf(source, file);
        if (!incoming.has(file) && modules.has(module)) this.index.removeFile(file);
        else if (!incoming.has(file)) this.index.updateFile(file, source);
      }
      this.overlays.clear();
      for (const [name, source] of incoming) { this.overlays.set(name, source); this.index.updateFile(name, source); }
  }
}

/** A module's identity as the Workbench reads it from a source file: its name, its `module` line, and its header comment. */
export interface ModuleDocument {
  readonly file: string;
  readonly name: string;
  readonly module: string;
  readonly source: string;
  readonly line: number;
  readonly header: string;
}

export function moduleDocument(file: string, source: string): ModuleDocument | undefined {
  const match = /^[ \t]*module[ \t]+([^\s]+)[ \t]*(?:--[^\n]*)?\r?$/m.exec(source);
  if (!match) return undefined;
  const line = source.slice(0, match.index).split("\n").length;
  const header = source.slice(0, match.index).split("\n")
    .filter(line => /^--/.test(line) && !/^--\s*(?:Copyright|Released under|Authors:|Part of)/.test(line))
    .map(line => line.replace(/^--[!|]?\s?/, "")).join("\n").trim();
  return { file, name: file, module: match[1]!, source, line, header };
}

export function indexModuleDocuments(entries: Iterable<readonly [string, string]>): Map<string, ModuleDocument[]> {
  const index = new Map<string, ModuleDocument[]>();
  for (const [file, source] of entries) {
    const doc = moduleDocument(file, source);
    if (doc) {
      const candidates = index.get(doc.module) || [];
      candidates.push(doc);
      index.set(doc.module, candidates);
    }
  }
  return index;
}

/** How many parentheses a header line opens without closing: a positive count means the binder list wraps onto the next line. */
export function openParentheses(text: string): number {
  let depth = 0;
  for (const character of text) {
    if (character === "(") depth += 1;
    else if (character === ")") depth -= 1;
  }
  return depth;
}
