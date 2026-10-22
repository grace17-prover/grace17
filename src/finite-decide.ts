// Ground decisions about finite sets, certified by a generated tactic script.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { app, naturalValue, termEquals, type Formula, type Term } from "./ast.ts";
import { formatTerm } from "./pretty.ts";

/**
 * `decide` evaluates a closed statement about finite sets (set literals,
 * numerals, ∪, ∩, ∖, 𝒫, insert, ∅) and, when it is true, writes a proof
 * script from the membership lemmas of Cumulus. The script is elaborated like
 * any other proof, so the kernel checks every step; evaluation only chooses
 * which lemmas to apply. Numerals are atoms here: `2 ∈ 5` is decided through
 * the natural-number lemmas, but a numeral is never unfolded into the set of
 * its predecessors, so `{0} = 1` is outside the fragment.
 */
export interface FiniteNames {
  readonly empty: string;
  readonly pair: string;
  readonly powerset: string;
  readonly succ: string;
  readonly singleton?: string;
  readonly union2?: string;
  readonly insert?: string;
  readonly intersection?: string;
  readonly difference?: string;
  /** The Subset predicate, when in scope. */
  readonly subset?: string;
  /** The cardinality function, when in scope. */
  readonly cardinality?: string;
}

export class FiniteDecideError extends Error {}

type HF = { readonly tag: "num"; readonly value: bigint } | { readonly tag: "set"; readonly elements: readonly HF[] };

const MAX_POWERSET_BASE = 10;

function compareHF(a: HF, b: HF): number {
  if (a.tag !== b.tag) return a.tag === "num" ? -1 : 1;
  if (a.tag === "num" && b.tag === "num") return a.value < b.value ? -1 : a.value > b.value ? 1 : 0;
  const left = (a as { elements: readonly HF[] }).elements;
  const right = (b as { elements: readonly HF[] }).elements;
  for (let index = 0; index < Math.min(left.length, right.length); index += 1) {
    const order = compareHF(left[index]!, right[index]!);
    if (order !== 0) return order;
  }
  return left.length - right.length;
}
const equalHF = (a: HF, b: HF): boolean => compareHF(a, b) === 0;
function makeSet(elements: readonly HF[]): HF {
  const sorted = [...elements].sort(compareHF);
  const unique: HF[] = [];
  for (const element of sorted) if (!unique.length || !equalHF(unique.at(-1)!, element)) unique.push(element);
  return { tag: "set", elements: unique };
}
function memberHF(x: HF, set: HF): boolean {
  if (set.tag === "num") return x.tag === "num" && x.value < set.value;
  return set.elements.some(element => equalHF(element, x));
}
function subsetHF(a: HF, b: HF): boolean {
  if (a.tag === "num") return b.tag === "num" ? a.value <= b.value : false;
  return a.elements.every(element => memberHF(element, b));
}

export function decideFiniteSet(goal: Formula, names: FiniteNames, taken: ReadonlySet<string>): string[] {
  const show = (term: Term): string => formatTerm(term);
  const unsupported = (what: string): never => { throw new FiniteDecideError(what); };
  const cache = new Map<Term, HF>();

  const evaluate = (term: Term): HF => {
    const cached = cache.get(term);
    if (cached) return cached;
    const numeral = naturalValue(term);
    let result: HF;
    if (numeral !== undefined) result = { tag: "num", value: numeral };
    else if (term.tag !== "app") result = unsupported(`${show(term)} is not a closed finite-set term`);
    else {
      const { fn, args } = term;
      if (fn === names.empty && args.length === 0) result = makeSet([]);
      else if (fn === names.succ && args.length === 1) {
        const inner = evaluate(args[0]!);
        result = inner.tag === "num" ? { tag: "num", value: inner.value + 1n } : unsupported(`${show(term)} is not a numeral`);
      } else if (fn === names.singleton && args.length === 1) result = makeSet([evaluate(args[0]!)]);
      else if (fn === names.pair && args.length === 2) result = makeSet([evaluate(args[0]!), evaluate(args[1]!)]);
      else if (fn === names.union2 && args.length === 2) {
        const [a, b] = [evaluate(args[0]!), evaluate(args[1]!)];
        if (a.tag !== "set" || b.tag !== "set") unsupported(`${show(term)} unites a numeral; numerals are not unfolded`);
        result = makeSet([...(a as { elements: readonly HF[] }).elements, ...(b as { elements: readonly HF[] }).elements]);
      } else if (fn === names.insert && args.length === 2) {
        const [x, a] = [evaluate(args[0]!), evaluate(args[1]!)];
        if (a.tag !== "set") unsupported(`${show(term)} inserts into a numeral`);
        result = makeSet([x, ...(a as { elements: readonly HF[] }).elements]);
      } else if (fn === names.intersection && args.length === 2) {
        const [a, b] = [evaluate(args[0]!), evaluate(args[1]!)];
        if (a.tag !== "set" || b.tag !== "set") unsupported(`${show(term)} intersects a numeral`);
        result = makeSet((a as { elements: readonly HF[] }).elements.filter(element => memberHF(element, b)));
      } else if (fn === names.difference && args.length === 2) {
        const [a, b] = [evaluate(args[0]!), evaluate(args[1]!)];
        if (a.tag !== "set" || b.tag !== "set") unsupported(`${show(term)} subtracts from a numeral`);
        result = makeSet((a as { elements: readonly HF[] }).elements.filter(element => !memberHF(element, b)));
      } else if (fn === names.powerset && args.length === 1) {
        const a = evaluate(args[0]!);
        if (a.tag !== "set") unsupported(`${show(term)} takes the powerset of a numeral`);
        const elements = (a as { elements: readonly HF[] }).elements;
        if (elements.length > MAX_POWERSET_BASE) unsupported(`${show(term)} has too many subsets to enumerate`);
        const subsets: HF[] = [];
        for (let mask = 0; mask < (1 << elements.length); mask += 1) {
          subsets.push(makeSet(elements.filter((_, index) => mask & (1 << index))));
        }
        result = makeSet(subsets);
      } else result = unsupported(`${show(term)} is not built from set literals, ∪, ∩, ∖, 𝒫, insert, ∅, and numerals`);
    }
    cache.set(term, result);
    return result;
  };

  // Syntactic representatives of the elements of a set term, for witnesses.
  const representatives = (term: Term): Term[] => {
    if (term.tag !== "app") return [];
    const { fn, args } = term;
    if (fn === names.singleton && args.length === 1) return [args[0]!];
    if (fn === names.pair && args.length === 2) return [args[0]!, args[1]!];
    if (fn === names.union2 && args.length === 2) return [...representatives(args[0]!), ...representatives(args[1]!)];
    if (fn === names.insert && args.length === 2) return [args[0]!, ...representatives(args[1]!)];
    if (fn === names.intersection && args.length === 2) {
      const right = evaluate(args[1]!);
      return representatives(args[0]!).filter(item => memberHF(evaluate(item), right));
    }
    if (fn === names.difference && args.length === 2) {
      const right = evaluate(args[1]!);
      return representatives(args[0]!).filter(item => !memberHF(evaluate(item), right));
    }
    return [];
  };
  const witnessIn = (x: Term, notIn: Term): Term | undefined => {
    const excluded = evaluate(notIn);
    return representatives(x).find(item => !memberHF(evaluate(item), excluded));
  };

  let counter = 0;
  const fresh = (prefix: string): string => {
    let name = `${prefix}${++counter}`;
    while (taken.has(name)) name = `${prefix}${++counter}`;
    return name;
  };
  const indent = (lines: readonly string[], by = 2): string[] => lines.map(line => `${" ".repeat(by)}${line}`);
  const bullet = (lines: readonly string[]): string[] => [`. ${lines[0]}`, ...indent(lines.slice(1))];
  const haveBlock = (name: string, statement: string, body: readonly string[]): string[] =>
    [`have ${name} : ${statement}`, ...indent(body)];
  const isNumeral = (term: Term): boolean => evaluate(term).tag === "num";
  const shape = (term: Term): { fn: string; args: readonly Term[] } | undefined =>
    term.tag === "app" && naturalValue(term) === undefined ? { fn: term.fn, args: term.args } : undefined;
  const need = (name: string | undefined, what: string): string => name ?? unsupported(`${what} is not in scope`);

  // A proof of x = a for terms with the same value.
  const equal = (x: Term, a: Term): string[] => {
    if (termEquals(x, a)) return ["rfl"];
    const [xv, av] = [evaluate(x), evaluate(a)];
    if (xv.tag === "num" && av.tag === "num") return ["compute"];
    if (xv.tag !== av.tag) return unsupported(`${show(x)} = ${show(a)} compares a numeral with a set literal`);
    return [`apply Subset.antisymmetric at ${show(x)}, ${show(a)}`, ...bullet(subset(x, a)), ...bullet(subset(a, x))];
  };

  // A proof of x ∈ T.
  const memberOf = (x: Term, T: Term): string[] => {
    const target = shape(T);
    if (!target) {
      if (isNumeral(T) && isNumeral(x)) return ["typecheck"];
      return unsupported(`${show(x)} ∈ ${show(T)} needs a numeral member of a numeral`);
    }
    const [X, S] = [show(x), show(T)];
    const { fn, args } = target;
    if (fn === names.singleton) {
      const e = fresh("e");
      return [...haveBlock(e, `${X} = ${show(args[0]!)}`, equal(x, args[0]!)),
        `exact singleton.membership.backward at ${X}, ${show(args[0]!)} with ${e}`];
    }
    if (fn === names.pair) {
      const [a, b] = [args[0]!, args[1]!];
      const left = equalHF(evaluate(x), evaluate(a));
      const chosen = left ? a : b;
      const lemma = left ? "pair.left" : "pair.right";
      if (termEquals(x, chosen)) return [`exact ${lemma} at ${show(a)}, ${show(b)}`];
      const e = fresh("e");
      return [...haveBlock(e, `${X} = ${show(chosen)}`, equal(x, chosen)), `rw ${e}`, `exact ${lemma} at ${show(a)}, ${show(b)}`];
    }
    if (fn === names.union2) {
      const [a, b] = [args[0]!, args[1]!];
      const left = memberHF(evaluate(x), evaluate(a));
      const h = fresh("h");
      return [...haveBlock(h, `${X} ∈ ${show(left ? a : b)}`, memberOf(x, left ? a : b)),
        `exact ${left ? "union2.left" : "union2.right"} at ${X}, ${show(a)}, ${show(b)} with ${h}`];
    }
    if (fn === names.insert) {
      const [y, a] = [args[0]!, args[1]!];
      const head = [`apply insert.membership.backward at ${X}, ${show(y)}, ${show(a)}`];
      if (equalHF(evaluate(x), evaluate(y))) return [...head, "left", ...equal(x, y)];
      return [...head, "right", ...memberOf(x, a)];
    }
    if (fn === names.intersection) {
      const [a, b] = [args[0]!, args[1]!];
      return [`apply intersection.membership.backward at ${show(a)}, ${show(b)}, ${X}`, "constructor",
        ...bullet(memberOf(x, a)), ...bullet(memberOf(x, b))];
    }
    if (fn === names.difference) {
      const [a, b] = [args[0]!, args[1]!];
      const h = fresh("h");
      return [`apply difference.membership.backward at ${show(a)}, ${show(b)}, ${X}`, "constructor",
        ...bullet(memberOf(x, a)), ...bullet([`intro ${h}`, ...refute(h, x, b)])];
    }
    if (fn === names.powerset) {
      return [`apply powerset.membership_iff.backward at ${X}, ${show(args[0]!)}`, ...subset(x, args[0]!)];
    }
    if (fn === names.empty) return unsupported(`${X} ∈ ∅ is false`);
    return unsupported(`${S} is not a finite-set term`);
  };

  // From h : x ∈ T, with x not a member of T, derive ⊥.
  const refute = (h: string, x: Term, T: Term): string[] => {
    const target = shape(T);
    const X = show(x);
    if (!target) {
      if (isNumeral(T) && isNumeral(x)) {
        const [lt, bad, cycle] = [fresh("lt"), fresh("bad"), fresh("cycle")];
        return [`have ${lt} := Less.of_membership at ${X}, ${show(T)} with *`, `have ${bad} := ${lt} with ${h}`,
          ...haveBlock(cycle, `${X} < ${X}`, ["arith"]), `exact Less.irreflexive at ${X} with *, ${cycle}`];
      }
      return unsupported(`${X} ∈ ${show(T)} cannot be refuted here`);
    }
    const { fn, args } = target;
    if (fn === names.empty) return [`exact set.empty at ${X} with ${h}`];
    if (fn === names.singleton) {
      const e = fresh("e");
      return [`have ${e} := singleton.membership.forward at ${X}, ${show(args[0]!)} with ${h}`, ...refuteEqual(e, x, args[0]!)];
    }
    if (fn === names.pair) {
      const [p, c, e1, e2] = [fresh("p"), fresh("c"), fresh("e"), fresh("e")];
      return [`have ${p} := pair.membership with ${show(args[0]!)}, ${show(args[1]!)}, ${X}`, `have ${c} := ${p}.forward with ${h}`,
        `cases ${c} with ${e1} | ${e2}`, ...bullet(refuteEqual(e1, x, args[0]!)), ...bullet(refuteEqual(e2, x, args[1]!))];
    }
    if (fn === names.union2) {
      const [d, l, r] = [fresh("d"), fresh("l"), fresh("r")];
      return [`have ${d} := union2.membership.forward at ${X}, ${show(args[0]!)}, ${show(args[1]!)} with ${h}`,
        `cases ${d} with ${l} | ${r}`, ...bullet(refute(l, x, args[0]!)), ...bullet(refute(r, x, args[1]!))];
    }
    if (fn === names.insert) {
      const [d, e, r] = [fresh("d"), fresh("e"), fresh("r")];
      return [`have ${d} := insert.membership.forward at ${X}, ${show(args[0]!)}, ${show(args[1]!)} with ${h}`,
        `cases ${d} with ${e} | ${r}`, ...bullet(refuteEqual(e, x, args[0]!)), ...bullet(refute(r, x, args[1]!))];
    }
    if (fn === names.intersection || fn === names.difference) {
      const [a, b] = [args[0]!, args[1]!];
      const [d, l, r] = [fresh("d"), fresh("l"), fresh("r")];
      const lemma = fn === names.intersection ? "intersection.membership" : "difference.membership";
      const head = [`have ${d} := ${lemma}.forward at ${X}, ${show(a)}, ${show(b)} with ${h}`, `rcases ${d} with ⟨${l}, ${r}⟩`];
      if (!memberHF(evaluate(x), evaluate(a))) return [...head, ...refute(l, x, a)];
      if (fn === names.intersection) return [...head, ...refute(r, x, b)];
      const m = fresh("m");
      return [...head, ...haveBlock(m, `${X} ∈ ${show(b)}`, memberOf(x, b)), `exact ${r} with ${m}`];
    }
    if (fn === names.powerset) {
      const a = args[0]!;
      const witness = witnessIn(x, a) ?? unsupported(`${X} ⊆ ${show(a)} has no syntactic counterexample`);
      const [s, m, bad] = [fresh("s"), fresh("m"), fresh("bad")];
      return [`have ${s} := powerset.membership_iff.forward at ${X}, ${show(a)} with ${h}`, `unfold Subset at ${s}`,
        ...haveBlock(m, `${show(witness)} ∈ ${X}`, memberOf(witness, x)),
        `have ${bad} := ${s} with ${show(witness)}, ${m}`, ...refute(bad, witness, a)];
    }
    return unsupported(`${show(T)} is not a finite-set term`);
  };

  // From e : x = a, with different values, derive ⊥.
  const refuteEqual = (e: string, x: Term, a: Term): string[] => {
    const [xv, av] = [evaluate(x), evaluate(a)];
    if (xv.tag === "num" && av.tag === "num") {
      const bad = fresh("bad");
      const settle = "settle with Naturals.disjoint.zero.succ, Naturals.injective.succ";
      if (xv.value < av.value) return [...haveBlock(bad, `${show(x)} ≠ ${show(a)}`, [settle]), `exact ${bad} with ${e}`];
      return [`symm at ${e}`, ...haveBlock(bad, `${show(a)} ≠ ${show(x)}`, [settle]), `exact ${bad} with ${e}`];
    }
    if (xv.tag !== av.tag) return unsupported(`${show(x)} = ${show(a)} compares a numeral with a set literal`);
    const m = fresh("m");
    const inX = witnessIn(x, a);
    if (inX) return [...haveBlock(m, `${show(inX)} ∈ ${show(x)}`, memberOf(inX, x)), `rw ${e} at ${m}`, ...refute(m, inX, a)];
    const inA = witnessIn(a, x) ?? unsupported(`${show(x)} ≠ ${show(a)} has no syntactic witness`);
    return [...haveBlock(m, `${show(inA)} ∈ ${show(a)}`, memberOf(inA, a)), `rw ← ${e} at ${m}`, ...refute(m, inA, x)];
  };

  // From h : z ∈ A for a variable z, run `continue` on each possible value of z.
  const eliminate = (h: string, z: string, A: Term, next: (candidate: Term, equation: string) => string[]): string[] => {
    const target = shape(A);
    if (!target) return unsupported(`${z} ∈ ${show(A)} cannot be enumerated; numerals are not unfolded`);
    const { fn, args } = target;
    if (fn === names.empty) return ["exfalso", `exact set.empty at ${z} with ${h}`];
    if (fn === names.singleton) {
      const e = fresh("e");
      return [`have ${e} := singleton.membership.forward at ${z}, ${show(args[0]!)} with ${h}`, `rw ${e}`, ...next(args[0]!, e)];
    }
    if (fn === names.pair) {
      const [p, c, e1, e2] = [fresh("p"), fresh("c"), fresh("e"), fresh("e")];
      return [`have ${p} := pair.membership with ${show(args[0]!)}, ${show(args[1]!)}, ${z}`, `have ${c} := ${p}.forward with ${h}`,
        `cases ${c} with ${e1} | ${e2}`, ...bullet([`rw ${e1}`, ...next(args[0]!, e1)]), ...bullet([`rw ${e2}`, ...next(args[1]!, e2)])];
    }
    if (fn === names.union2) {
      const [d, l, r] = [fresh("d"), fresh("l"), fresh("r")];
      return [`have ${d} := union2.membership.forward at ${z}, ${show(args[0]!)}, ${show(args[1]!)} with ${h}`,
        `cases ${d} with ${l} | ${r}`, ...bullet(eliminate(l, z, args[0]!, next)), ...bullet(eliminate(r, z, args[1]!, next))];
    }
    if (fn === names.insert) {
      const [d, e, r] = [fresh("d"), fresh("e"), fresh("r")];
      return [`have ${d} := insert.membership.forward at ${z}, ${show(args[0]!)}, ${show(args[1]!)} with ${h}`,
        `cases ${d} with ${e} | ${r}`, ...bullet([`rw ${e}`, ...next(args[0]!, e)]), ...bullet(eliminate(r, z, args[1]!, next))];
    }
    if (fn === names.intersection) {
      const [a, b] = [args[0]!, args[1]!];
      const [d, l, r] = [fresh("d"), fresh("l"), fresh("r")];
      const right = evaluate(b);
      return [`have ${d} := intersection.membership.forward at ${show(a)}, ${show(b)}, ${z} with ${h}`, `rcases ${d} with ⟨${l}, ${r}⟩`,
        ...eliminate(l, z, a, (candidate, equation) => memberHF(evaluate(candidate), right)
          ? next(candidate, equation)
          : [`rw ${equation} at ${r}`, "exfalso", ...refute(r, candidate, b)])];
    }
    if (fn === names.difference) {
      const [a, b] = [args[0]!, args[1]!];
      const [d, l, r] = [fresh("d"), fresh("l"), fresh("r")];
      const right = evaluate(b);
      return [`have ${d} := difference.membership.forward at ${show(a)}, ${show(b)}, ${z} with ${h}`, `rcases ${d} with ⟨${l}, ${r}⟩`,
        ...eliminate(l, z, a, (candidate, equation) => memberHF(evaluate(candidate), right)
          ? [`rw ${equation} at ${r}`, "exfalso", `apply ${r}`, ...memberOf(candidate, b)]
          : next(candidate, equation))];
    }
    if (fn === names.powerset) return unsupported(`a powerset on the left of ⊆ or = is not enumerated`);
    return unsupported(`${show(A)} is not a finite-set term`);
  };

  // A proof of A ⊆ B.
  const subset = (A: Term, B: Term): string[] => {
    const z = fresh("z");
    const hz = fresh("h");
    return ["unfold Subset", `intros ${z} ${hz}`, ...eliminate(hz, z, A, candidate => memberOf(candidate, B))];
  };

  const asMember = (formula: Formula): { x: Term; T: Term } | undefined =>
    formula.tag === "pred" && formula.pred === "in" && formula.args.length === 2 ? { x: formula.args[0]!, T: formula.args[1]! } : undefined;
  const asSubset = (formula: Formula): { A: Term; B: Term } | undefined =>
    formula.tag === "pred" && names.subset !== undefined && formula.pred === names.subset && formula.args.length === 2
      ? { A: formula.args[0]!, B: formula.args[1]! } : undefined;

  // cardinality(T) = n: rewrite T as a chain of fresh insertions into a
  // singleton, then count with cardinality.insert and cardinality.singleton.
  const counting = goal.tag === "eq" && goal.left.tag === "app" && names.cardinality !== undefined &&
    goal.left.fn === names.cardinality && goal.left.args.length === 1 && naturalValue(goal.right) !== undefined
    ? { T: goal.left.args[0]!, n: naturalValue(goal.right)! } : undefined;
  if (counting) {
    const value = evaluate(counting.T);
    if (value.tag !== "set") unsupported(`${show(counting.T)} is a numeral; its cardinality is cardinality.natural`);
    if (BigInt(value.elements.length) !== counting.n) unsupported(`${show(counting.T)} has ${value.elements.length} elements, not ${counting.n}`);
    const insertName = need(names.insert, "insert");
    const singletonName = need(names.singleton, "singleton");
    const distinct: Term[] = [];
    for (const item of representatives(counting.T)) if (!distinct.some(seen => equalHF(evaluate(seen), evaluate(item)))) distinct.push(item);
    if (distinct.length !== value.elements.length) unsupported(`${show(counting.T)} has elements without syntactic representatives`);
    if (distinct.length === 0) unsupported("the cardinality of ∅ is cardinality.natural at 0 after nat.zero");
    // chain[i] is insert(distinct[i], chain[i + 1]); the last link is a singleton.
    const chain: Term[] = new Array(distinct.length);
    chain[distinct.length - 1] = app(singletonName, distinct[distinct.length - 1]!);
    for (let index = distinct.length - 2; index >= 0; index -= 1) chain[index] = app(insertName, distinct[index]!, chain[index + 1]!);
    const lines: string[] = [];
    if (!termEquals(counting.T, chain[0]!)) {
      const shapeName = fresh("shape");
      lines.push(...haveBlock(shapeName, `${show(counting.T)} = ${show(chain[0]!)}`, equal(counting.T, chain[0]!)), `rw ${shapeName}`);
    }
    const finite: string[] = new Array(distinct.length);
    finite[distinct.length - 1] = fresh("finite");
    lines.push(`have ${finite[distinct.length - 1]} := Finite.singleton at ${show(distinct[distinct.length - 1]!)}`);
    for (let index = distinct.length - 2; index >= 1; index -= 1) {
      finite[index] = fresh("finite");
      lines.push(`have ${finite[index]} := Finite.insert at ${show(chain[index + 1]!)}, ${show(distinct[index]!)} with ${finite[index + 1]}`);
    }
    for (let index = 0; index < distinct.length - 1; index += 1) {
      const absent = fresh("absent");
      const step = fresh("step");
      const h = fresh("h");
      lines.push(...haveBlock(absent, `¬(${show(distinct[index]!)} ∈ ${show(chain[index + 1]!)})`, [`intro ${h}`, ...refute(h, distinct[index]!, chain[index + 1]!)]));
      lines.push(`have ${step} := cardinality.insert at ${show(chain[index + 1]!)}, ${show(distinct[index]!)} with ${finite[index + 1]}, ${absent}`);
      lines.push(`rw ${step}`);
    }
    const base = fresh("base");
    lines.push(`have ${base} := cardinality.singleton at ${show(distinct[distinct.length - 1]!)}`, `rw ${base}`, "compute");
    return lines;
  }

  const member = asMember(goal);
  if (member) {
    if (!memberHF(evaluate(member.x), evaluate(member.T))) unsupported(`${show(member.x)} ∈ ${show(member.T)} is false`);
    return memberOf(member.x, member.T);
  }
  const inclusion = asSubset(goal);
  if (inclusion) {
    if (!subsetHF(evaluate(inclusion.A), evaluate(inclusion.B))) unsupported(`${show(inclusion.A)} ⊆ ${show(inclusion.B)} is false`);
    return subset(inclusion.A, inclusion.B);
  }
  if (goal.tag === "eq") {
    if (!equalHF(evaluate(goal.left), evaluate(goal.right))) unsupported(`${show(goal.left)} = ${show(goal.right)} is false`);
    return equal(goal.left, goal.right);
  }
  if (goal.tag === "imp" && goal.right.tag === "bottom") {
    const denied = asMember(goal.left);
    if (denied) {
      if (memberHF(evaluate(denied.x), evaluate(denied.T))) unsupported(`${show(denied.x)} ∉ ${show(denied.T)} is false`);
      const h = fresh("h");
      return [`intro ${h}`, ...refute(h, denied.x, denied.T)];
    }
    if (goal.left.tag === "eq") {
      if (equalHF(evaluate(goal.left.left), evaluate(goal.left.right))) unsupported(`${show(goal.left.left)} ≠ ${show(goal.left.right)} is false`);
      const e = fresh("e");
      return [`intro ${e}`, ...refuteEqual(e, goal.left.left, goal.left.right)];
    }
    const deniedSubset = asSubset(goal.left);
    if (deniedSubset) {
      if (subsetHF(evaluate(deniedSubset.A), evaluate(deniedSubset.B))) unsupported(`the inclusion holds, so its negation is false`);
      const witness = witnessIn(deniedSubset.A, deniedSubset.B) ?? unsupported("no syntactic witness against the inclusion");
      const [s, m, bad] = [fresh("s"), fresh("m"), fresh("bad")];
      return [`intro ${s}`, `unfold Subset at ${s}`, ...haveBlock(m, `${show(witness)} ∈ ${show(deniedSubset.A)}`, memberOf(witness, deniedSubset.A)),
        `have ${bad} := ${s} with ${show(witness)}, ${m}`, ...refute(bad, witness, deniedSubset.B)];
    }
  }
  return unsupported("decide proves closed goals of the forms x ∈ A, x ∉ A, A ⊆ B, A = B, and A ≠ B over finite set literals");
}

export const finiteDecideSuffixes = {
  singleton: ".singleton", union2: ".union2", insert: ".insert", intersection: ".intersection", difference: ".difference", subset: ".Subset",
} as const;
export function needsName(names: FiniteNames): string | undefined {
  return [names.empty, names.pair, names.powerset, names.succ].some(name => !name) ? "the core set symbols" : undefined;
}
