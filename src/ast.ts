// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { pairInternKey, type InternKey } from "./intern-key.ts";

export type Term =
  | { readonly tag: "var"; readonly name: string }
  | { readonly tag: "nat"; readonly value: string }
  | { readonly tag: "app"; readonly fn: string; readonly args: readonly Term[] };

export type Formula =
  | { readonly tag: "bottom" }
  | { readonly tag: "eq"; readonly left: Term; readonly right: Term }
  | { readonly tag: "pred"; readonly pred: string; readonly args: readonly Term[] }
  | { readonly tag: "imp"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "forall"; readonly variable: string; readonly body: Formula }
  | { readonly tag: "and"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "or"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "iff"; readonly left: Formula; readonly right: Formula }
  | { readonly tag: "exists"; readonly variable: string; readonly body: Formula };

let nextAstId = 1;
const astIds = new WeakMap<object, number>();

class AstNode { constructor(target: object) { return target; } }
class Identified extends AstNode {
  #id: number;
  constructor(target: object, id: number) { super(target); this.#id = id; }
  static of(target: object): number | undefined { return #id in target ? target.#id : undefined; }
}
function astId(value: object): number {
  const known = Identified.of(value);
  if (known !== undefined) return known;
  let id = astIds.get(value);
  if (id === undefined) {
    id = nextAstId++;
    try { new Identified(value, id); } catch { astIds.set(value, id); }
  }
  return id;
}

const maximumInternEntries = 32_768;
// Map.keys().next() repeatedly scans deleted slots under sustained eviction.
// Keep the same bounded FIFO policy with an explicit circular queue.
// A queue is shared by every table of one node kind (`group`), so the bound
// holds across the per-symbol tables of applications, predicates, and binders.
interface InternEntry { readonly table: Map<InternKey, object>; readonly key: InternKey }
const internQueues = new WeakMap<object, { entries: InternEntry[]; next: number }>();
function intern<T extends object>(table: Map<InternKey, T>, key: InternKey, create: () => T, group: object = table): T {
  const previous = table.get(key);
  if (previous) return previous;
  const value = create();
  table.set(key, value);
  let queue = internQueues.get(group);
  if (!queue) { queue = { entries: [], next: 0 }; internQueues.set(group, queue); }
  const entry: InternEntry = { table, key };
  if (queue.entries.length < maximumInternEntries) queue.entries.push(entry);
  else {
    const evicted = queue.entries[queue.next]!;
    evicted.table.delete(evicted.key);
    queue.entries[queue.next] = entry;
    queue.next = (queue.next + 1) % maximumInternEntries;
  }
  astId(value);
  return value;
}

const variables = new Map<InternKey, Term>();
const naturals = new Map<InternKey, Term>();
const equalities = new Map<InternKey, Formula>();
const implications = new Map<InternKey, Formula>();
const conjunctions = new Map<InternKey, Formula>();
const disjunctions = new Map<InternKey, Formula>();
const equivalences = new Map<InternKey, Formula>();
// Applications, predicates, and binders are interned per symbol and arity,
// so their keys are the children's ids rather than text built per node.
const applications = new Map<string, Map<InternKey, Term>[]>();
const predicates = new Map<string, Map<InternKey, Formula>[]>();
const universals = new Map<string, Map<InternKey, Formula>>();
const existentials = new Map<string, Map<InternKey, Formula>>();

function argumentTable<T>(tables: Map<string, Map<InternKey, T>[]>, symbol: string, arity: number): Map<InternKey, T> {
  let byArity = tables.get(symbol);
  if (!byArity) { byArity = []; tables.set(symbol, byArity); }
  return byArity[arity] ??= new Map();
}
function binderTable<T>(tables: Map<string, Map<InternKey, T>>, variable: string): Map<InternKey, T> {
  let table = tables.get(variable);
  if (!table) { table = new Map(); tables.set(variable, table); }
  return table;
}
function argumentsKey(args: readonly Term[]): InternKey {
  switch (args.length) {
    case 0: return 0;
    case 1: return astId(args[0]!);
    case 2: return pairInternKey(astId(args[0]!), astId(args[1]!));
    default: return args.map(astId).join(",");
  }
}

export const v = (name: string): Term => intern(variables, name,
  () => Object.freeze({ tag: "var" as const, name }));
export const app = (fn: string, ...args: Term[]): Term => intern(argumentTable(applications, fn, args.length), argumentsKey(args),
  () => Object.freeze({ tag: "app" as const, fn, args: Object.freeze(args) }), applications);
export const nat = (value: bigint | number | string): Term => {
  const text = String(value);
  if (!/^(?:0|[1-9]\d*)$/.test(text)) throw new Error(`Invalid natural literal: ${text}`);
  return intern(naturals, text, () => Object.freeze({ tag: "nat" as const, value: text }));
};
export const bottom: Formula = Object.freeze({ tag: "bottom" });
astId(bottom);
export const eq = (left: Term, right: Term): Formula => intern(equalities, pairInternKey(astId(left), astId(right)),
  () => Object.freeze({ tag: "eq" as const, left, right }));
export const pred = (name: string, ...args: Term[]): Formula => intern(argumentTable(predicates, name, args.length), argumentsKey(args),
  () => Object.freeze({ tag: "pred" as const, pred: name, args: Object.freeze(args) }), predicates);
export const imp = (left: Formula, right: Formula): Formula => intern(implications, pairInternKey(astId(left), astId(right)),
  () => Object.freeze({ tag: "imp" as const, left, right }));
export const forall = (variable: string, body: Formula): Formula => intern(binderTable(universals, variable), astId(body),
  () => Object.freeze({ tag: "forall" as const, variable, body }), universals);
export const not = (p: Formula): Formula => imp(p, bottom);
export const and = (left: Formula, right: Formula): Formula => intern(conjunctions, pairInternKey(astId(left), astId(right)),
  () => Object.freeze({ tag: "and" as const, left, right }));
export const or = (left: Formula, right: Formula): Formula => intern(disjunctions, pairInternKey(astId(left), astId(right)),
  () => Object.freeze({ tag: "or" as const, left, right }));
export const iff = (left: Formula, right: Formula): Formula => intern(equivalences, pairInternKey(astId(left), astId(right)),
  () => Object.freeze({ tag: "iff" as const, left, right }));
export const exists = (variable: string, body: Formula): Formula => intern(binderTable(existentials, variable), astId(body),
  () => Object.freeze({ tag: "exists" as const, variable, body }), existentials);

export function foralls(variables: readonly string[], body: Formula): Formula {
  return variables.reduceRight((result, variable) => forall(variable, result), body);
}

export function formulaEquals(left: Formula, right: Formula): boolean {
  if (left === right) return true;
  const leftBinders: string[] = [];
  const rightBinders: string[] = [];
  const boundIndex = (name: string, binders: readonly string[]): number => {
    for (let index = binders.length - 1; index >= 0; index -= 1) {
      if (binders[index] === name) return binders.length - index - 1;
    }
    return -1;
  };
  const sameTerm = (a: Term, b: Term): boolean => {
    if (couldBeNatural(a) || couldBeNatural(b)) {
      const aNat = naturalValue(a);
      const bNat = naturalValue(b);
      if (aNat !== undefined || bNat !== undefined) return aNat !== undefined && aNat === bNat;
    }
    if (a.tag !== b.tag) return false;
    if (a.tag === "var" && b.tag === "var") {
      const aBound = boundIndex(a.name, leftBinders);
      const bBound = boundIndex(b.name, rightBinders);
      return aBound < 0 && bBound < 0 ? a.name === b.name : aBound === bBound;
    }
    if (a.tag !== "app" || b.tag !== "app" || a.fn !== b.fn || a.args.length !== b.args.length) return false;
    return a.args.every((item, index) => sameTerm(item, b.args[index]!));
  };
  const sameFormula = (a: Formula, b: Formula): boolean => {
    if (a.tag !== b.tag) return false;
    switch (a.tag) {
      case "bottom": return true;
      case "eq": return b.tag === "eq" && sameTerm(a.left, b.left) && sameTerm(a.right, b.right);
      case "pred": return b.tag === "pred" && a.pred === b.pred && a.args.length === b.args.length &&
        a.args.every((item, index) => sameTerm(item, b.args[index]!));
      case "imp": return b.tag === "imp" && sameFormula(a.left, b.left) && sameFormula(a.right, b.right);
      case "and": return b.tag === "and" && sameFormula(a.left, b.left) && sameFormula(a.right, b.right);
      case "or": return b.tag === "or" && sameFormula(a.left, b.left) && sameFormula(a.right, b.right);
      case "iff": return b.tag === "iff" && sameFormula(a.left, b.left) && sameFormula(a.right, b.right);
      case "forall":
      case "exists": {
        if (b.tag !== a.tag) return false;
        leftBinders.push(a.variable);
        rightBinders.push(b.variable);
        const result = sameFormula(a.body, b.body);
        leftBinders.pop();
        rightBinders.pop();
        return result;
      }
    }
  };
  return sameFormula(left, right);
}

/** Exact term equality without allocating a serialized representation. */
export function termEquals(left: Term, right: Term): boolean {
  if (left === right) return true;
  if (couldBeNatural(left) || couldBeNatural(right)) {
    const leftNat = naturalValue(left);
    const rightNat = naturalValue(right);
    if (leftNat !== undefined || rightNat !== undefined) return leftNat !== undefined && leftNat === rightNat;
  }
  if (left.tag !== right.tag) return false;
  if (left.tag === "var" && right.tag === "var") return left.name === right.name;
  if (left.tag !== "app" || right.tag !== "app" || left.fn !== right.fn || left.args.length !== right.args.length) return false;
  return left.args.every((item, index) => termEquals(item, right.args[index]!));
}

function boundIndex(name: string, binders: readonly string[]): number {
  for (let index = binders.length - 1; index >= 0; index -= 1) {
    if (binders[index] === name) return binders.length - index - 1;
  }
  return -1;
}

/** Emit the canonical term bytes directly in elaborator hot paths. */
function encodeCanonicalTerm(term: Term, binders: readonly string[]): string {
  if (couldBeNatural(term)) {
    const numeral = naturalValue(term);
    if (numeral !== undefined) return `{"tag":"nat","value":${JSON.stringify(numeral.toString())}}`;
  }
  if (term.tag === "var") {
    const index = boundIndex(term.name, binders);
    return index < 0
      ? `{"name":${JSON.stringify(term.name)},"tag":"free"}`
      : `{"index":${index},"tag":"bound"}`;
  }
  if (term.tag === "nat") return `{"tag":"nat","value":${JSON.stringify(term.value)}}`;
  return `{"args":[${term.args.map(arg => encodeCanonicalTerm(arg, binders)).join(",")}],"fn":${JSON.stringify(term.fn)},"tag":"app"}`;
}

function encodeCanonicalFormula(formula: Formula, binders: readonly string[]): string {
  switch (formula.tag) {
    case "bottom": return `{"tag":"bottom"}`;
    case "eq": return `{"left":${encodeCanonicalTerm(formula.left, binders)},"right":${encodeCanonicalTerm(formula.right, binders)},"tag":"eq"}`;
    case "pred": return `{"args":[${formula.args.map(arg => encodeCanonicalTerm(arg, binders)).join(",")}],"pred":${JSON.stringify(formula.pred)},"tag":"pred"}`;
    case "imp": return `{"left":${encodeCanonicalFormula(formula.left, binders)},"right":${encodeCanonicalFormula(formula.right, binders)},"tag":"imp"}`;
    case "forall": return `{"body":${encodeCanonicalFormula(formula.body, [...binders, formula.variable])},"tag":"forall"}`;
    case "and":
    case "or":
    case "iff": return `{"left":${encodeCanonicalFormula(formula.left, binders)},"right":${encodeCanonicalFormula(formula.right, binders)},"tag":${JSON.stringify(formula.tag)}}`;
    case "exists": return `{"body":${encodeCanonicalFormula(formula.body, [...binders, formula.variable])},"tag":"exists"}`;
  }
}

const formulaCanonicalCache = new WeakMap<Formula, string>();
const termCanonicalCache = new WeakMap<Term, string>();

export function formulaCanonical(formula: Formula): string {
  const known = formulaCanonicalCache.get(formula);
  if (known !== undefined) return known;
  const encoded = encodeCanonicalFormula(formula, []);
  formulaCanonicalCache.set(formula, encoded);
  return encoded;
}

export function termCanonical(term: Term): string {
  const known = termCanonicalCache.get(term);
  if (known !== undefined) return known;
  const encoded = encodeCanonicalTerm(term, []);
  termCanonicalCache.set(term, encoded);
  return encoded;
}

export function canonical(value: unknown): string {
  if (value === null || typeof value !== "object") return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(canonical).join(",")}]`;
  const record = value as Record<string, unknown>;
  return `{${Object.keys(record).sort().map(key => `${JSON.stringify(key)}:${canonical(record[key])}`).join(",")}}`;
}

export function freeTermVariables(term: Term, into = new Set<string>()): Set<string> {
  if (term.tag === "var") into.add(term.name);
  else if (term.tag === "app") term.args.forEach(arg => freeTermVariables(arg, into));
  return into;
}

export function freeFormulaVariables(formula: Formula, into = new Set<string>()): Set<string> {
  const visitTerm = (term: Term, bound: ReadonlySet<string>): void => {
    if (term.tag === "var") {
      if (!bound.has(term.name)) into.add(term.name);
      return;
    }
    if (term.tag === "app") term.args.forEach(argument => visitTerm(argument, bound));
  };
  const visitFormula = (value: Formula, bound: ReadonlySet<string>): void => {
    switch (value.tag) {
      case "bottom": return;
      case "eq":
        visitTerm(value.left, bound);
        visitTerm(value.right, bound);
        return;
      case "pred":
        value.args.forEach(argument => visitTerm(argument, bound));
        return;
      case "imp":
      case "and":
      case "or":
      case "iff":
        visitFormula(value.left, bound);
        visitFormula(value.right, bound);
        return;
      case "forall":
      case "exists": {
        const nested = new Set(bound);
        nested.add(value.variable);
        visitFormula(value.body, nested);
      }
    }
  };
  visitFormula(formula, new Set());
  return into;
}

// Which variable names occur anywhere in a node, as a 32-bit set of name
// hashes kept in a private field of the node: a name whose bit is absent
// certainly does not occur, so a substitution for it is the identity and
// returns the node itself without a walk, which is what the walk would have
// returned. A present bit proves nothing and takes the walk. The field is
// private, so canonical encodings, freezing, and enumeration never see it,
// and a node built elsewhere, as from a compiled artifact, gets its mask the
// first time it is asked.
const nameBits = new Map<string, number>();
function nameBit(name: string): number {
  let bit = nameBits.get(name);
  if (bit === undefined) {
    let hash = 2166136261;
    for (let index = 0; index < name.length; index += 1) hash = Math.imul(hash ^ name.charCodeAt(index), 16777619);
    bit = 1 << (hash >>> 27);
    if (nameBits.size > 65_536) nameBits.clear();
    nameBits.set(name, bit);
  }
  return bit;
}
class Node { constructor(target: object) { return target; } }
class Occurrences extends Node {
  #names: number;
  constructor(target: object, names: number) { super(target); this.#names = names; }
  static of(target: object): number | undefined { return #names in target ? target.#names : undefined; }
}
function occurrences(node: Term | Formula): number {
  const known = Occurrences.of(node);
  if (known !== undefined) return known;
  let names = 0;
  switch (node.tag) {
    case "var": names = nameBit(node.name); break;
    case "nat": case "bottom": break;
    case "app": for (const arg of node.args) names |= occurrences(arg); break;
    case "pred": for (const arg of node.args) names |= occurrences(arg); break;
    case "eq": names = occurrences(node.left) | occurrences(node.right); break;
    case "imp": case "and": case "or": case "iff": names = occurrences(node.left) | occurrences(node.right); break;
    case "forall": case "exists": names = nameBit(node.variable) | occurrences(node.body); break;
  }
  try { new Occurrences(node, names); } catch { /* an exotic node is walked again next time */ }
  return names;
}

export function substituteTerm(term: Term, variable: string, replacement: Term): Term {
  return substituteTermFor(term, variable, nameBit(variable), replacement);
}

function substituteTermFor(term: Term, variable: string, bit: number, replacement: Term): Term {
  if ((occurrences(term) & bit) === 0) return term;
  if (term.tag === "var") return term.name === variable ? replacement : term;
  if (term.tag === "nat" || term.args.length === 0) return term;
  const args = term.args.map(arg => substituteTermFor(arg, variable, bit, replacement));
  return args.every((arg, index) => arg === term.args[index]) ? term : app(term.fn, ...args);
}

function fresh(base: string, forbidden: ReadonlySet<string>): string {
  if (!forbidden.has(base)) return base;
  for (let index = 1; ; index += 1) {
    const candidate = `${base}_${index}`;
    if (!forbidden.has(candidate)) return candidate;
  }
}

function termContainsVariable(term: Term, variable: string): boolean {
  if ((occurrences(term) & nameBit(variable)) === 0) return false;
  return term.tag === "var" ? term.name === variable
    : term.tag === "app" && term.args.some(argument => termContainsVariable(argument, variable));
}

export function substituteFormula(formula: Formula, variable: string, replacement: Term): Formula {
  return substituteFormulaFor(formula, variable, nameBit(variable), replacement);
}

function substituteFormulaFor(formula: Formula, variable: string, bit: number, replacement: Term): Formula {
  if ((occurrences(formula) & bit) === 0) return formula;
  switch (formula.tag) {
    case "bottom": return formula;
    case "eq": {
      const left = substituteTermFor(formula.left, variable, bit, replacement);
      const right = substituteTermFor(formula.right, variable, bit, replacement);
      return left === formula.left && right === formula.right ? formula : eq(left, right);
    }
    case "pred": {
      const args = formula.args.map(arg => substituteTermFor(arg, variable, bit, replacement));
      return args.every((arg, index) => arg === formula.args[index]) ? formula : pred(formula.pred, ...args);
    }
    case "imp": {
      const left = substituteFormulaFor(formula.left, variable, bit, replacement);
      const right = substituteFormulaFor(formula.right, variable, bit, replacement);
      return left === formula.left && right === formula.right ? formula : imp(left, right);
    }
    case "forall": {
      if (formula.variable === variable) return formula;
      if (!termContainsVariable(replacement, formula.variable)) {
        const body = substituteFormulaFor(formula.body, variable, bit, replacement);
        return body === formula.body ? formula : forall(formula.variable, body);
      }
      if (!freeFormulaVariables(formula.body).has(variable)) return formula;
      const replacementVars = freeTermVariables(replacement);
      const forbidden = freeFormulaVariables(formula.body);
      replacementVars.forEach(name => forbidden.add(name));
      forbidden.add(variable);
      const renamed = fresh(formula.variable, forbidden);
      const body = substituteFormula(formula.body, formula.variable, v(renamed));
      return forall(renamed, substituteFormula(body, variable, replacement));
    }
    case "and":
    case "or":
    case "iff": {
      const left = substituteFormulaFor(formula.left, variable, bit, replacement);
      const right = substituteFormulaFor(formula.right, variable, bit, replacement);
      if (left === formula.left && right === formula.right) return formula;
      return formula.tag === "and" ? and(left, right) : formula.tag === "or" ? or(left, right) : iff(left, right);
    }
    case "exists": {
      if (formula.variable === variable) return formula;
      if (!termContainsVariable(replacement, formula.variable)) {
        const body = substituteFormulaFor(formula.body, variable, bit, replacement);
        return body === formula.body ? formula : exists(formula.variable, body);
      }
      if (!freeFormulaVariables(formula.body).has(variable)) return formula;
      const replacementVars = freeTermVariables(replacement);
      const forbidden = freeFormulaVariables(formula.body);
      replacementVars.forEach(name => forbidden.add(name));
      forbidden.add(variable);
      const renamed = fresh(formula.variable, forbidden);
      const body = substituteFormula(formula.body, formula.variable, v(renamed));
      return exists(renamed, substituteFormula(body, variable, replacement));
    }
  }
}

export function containsFunction(term: Term, name: string): boolean {
  return term.tag === "app" && (term.fn === name || term.args.some(arg => containsFunction(arg, name)));
}

/** Read either a compact literal or a zero/succ constructor numeral. */
const naturalValueCache = new WeakMap<Term, bigint | null>();
function couldBeNatural(term: Term): boolean {
  return term.tag === "nat" || (term.tag === "app" &&
    ((term.fn === "zero" && term.args.length === 0) || (term.fn === "succ" && term.args.length === 1)));
}
export function naturalValue(term: Term): bigint | undefined {
  const cached = naturalValueCache.get(term);
  if (cached !== undefined) return cached === null ? undefined : cached;
  if (term.tag === "nat") {
    const result = /^(?:0|[1-9]\d*)$/.test(term.value) ? BigInt(term.value) : undefined;
    naturalValueCache.set(term, result ?? null);
    return result;
  }
  let value = 0n;
  let cursor = term;
  const successors: Term[] = [];
  while (cursor.tag === "app" && cursor.fn === "succ" && cursor.args.length === 1) {
    successors.push(cursor);
    value += 1n;
    cursor = cursor.args[0]!;
    const suffix = naturalValueCache.get(cursor);
    if (suffix !== undefined) {
      const result = suffix === null ? undefined : value + suffix;
      successors.forEach((item, index) => naturalValueCache.set(item,
        result === undefined ? null : result - BigInt(index)));
      return result;
    }
  }
  const result = cursor.tag === "nat" && /^(?:0|[1-9]\d*)$/.test(cursor.value)
    ? value + BigInt(cursor.value)
    : cursor.tag === "app" && cursor.fn === "zero" && cursor.args.length === 0 ? value : undefined;
  naturalValueCache.set(term, result ?? null);
  successors.forEach((item, index) => naturalValueCache.set(item,
    result === undefined ? null : result - BigInt(index)));
  return result;
}

export function formulaContainsSymbol(formula: Formula, name: string): boolean {
  switch (formula.tag) {
    case "bottom": return false;
    case "eq": return containsFunction(formula.left, name) || containsFunction(formula.right, name);
    case "pred": return formula.pred === name || formula.args.some(arg => containsFunction(arg, name));
    case "imp": return formulaContainsSymbol(formula.left, name) || formulaContainsSymbol(formula.right, name);
    case "forall": return formulaContainsSymbol(formula.body, name);
    case "and":
    case "or":
    case "iff": return formulaContainsSymbol(formula.left, name) || formulaContainsSymbol(formula.right, name);
    case "exists": return formulaContainsSymbol(formula.body, name);
  }
}
