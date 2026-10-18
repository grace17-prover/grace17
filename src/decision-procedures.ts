// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import {
  bottom, eq, formulaCanonical, formulaEquals, freeFormulaVariables, imp, not, or, pred, substituteFormula,
  termCanonical, termEquals, v, type Formula, type Term,
} from "./ast.ts";
import type { Kernel } from "./kernel.ts";
import { formatFormula } from "./pretty.ts";
import {
  andElimLeft, andElimRight, andIntro, assume, at, calc, congr, dne, eqElim, falseElim, forallElim,
  iffElimLeft, iffElimRight, iffIntro, impElim, impIntro, orElim, orIntroLeft,
  orIntroRight, refl, symm, type Proof,
} from "./proof.ts";

interface SignedProof {
  readonly truth: boolean;
  /** Proves the formula when true and its negation when false. */
  readonly proof: Proof;
}

/**
 * Complete classical propositional search. Predicate, equality, and quantified
 * formulas are atoms; all connective reasoning is reconstructed from primitive
 * natural-deduction proofs and checked by the kernel before it is returned.
 */
export function proveTautology(
  kernel: Kernel,
  goal: Formula,
  assumptions: readonly Formula[] = [],
  factProofs: readonly Proof[] = [],
  fuel = 65_536,
): Proof {
  const facts = uniqueFacts(kernel, assumptions, factProofs);
  const frequencies = new Map<string, { formula: Formula; count: number }>();
  for (const formula of [...facts.map(item => item.formula), goal]) collectPropositionalAtoms(formula, frequencies);
  const atoms = [...frequencies.values()]
    .sort((left, right) => right.count - left.count || formulaCanonical(left.formula).localeCompare(formulaCanonical(right.formula)))
    .map(item => item.formula);
  const valuation = new Map<string, SignedProof>();
  const budget = { remaining: fuel };

  const search = (index: number): Proof => {
    if (budget.remaining-- <= 0) throw new Error("tauto exhausted its search fuel");
    for (const fact of facts) {
      const value = evaluateFormula(fact.formula, valuation);
      if (value?.truth === false) return falseElim(goal, impElim(value.proof, fact.proof));
    }
    const result = evaluateFormula(goal, valuation);
    if (result?.truth === true) return result.proof;
    if (index >= atoms.length) {
      const counterexample = atoms.map(atom =>
        `${formatAtom(atom)}=${valuation.get(formulaCanonical(atom))?.truth ? "true" : "false"}`).join(", ");
      throw new Error(`tauto found a counterexample${counterexample ? `: ${counterexample}` : ""}`);
    }
    const atom = atoms[index]!;
    const key = formulaCanonical(atom);
    valuation.set(key, { truth: true, proof: assume(atom) });
    const positive = search(index + 1);
    valuation.set(key, { truth: false, proof: assume(not(atom)) });
    const negative = search(index + 1);
    valuation.delete(key);
    return orElim(excludedMiddle(atom), positive, negative);
  };

  const proof = search(0);
  if (!formulaEquals(kernel.checkProof(proof, assumptions), goal)) throw new Error("tauto produced a proof of the wrong goal");
  return proof;
}

export interface GroundOptions {
  /** Search nodes for the classical branching. */
  readonly fuel?: number;
  /** Universal lemmas and facts instantiated by matching the problem's atoms. */
  readonly rules?: readonly Proof[];
  /** Upper bound on instantiated facts. */
  readonly instanceLimit?: number;
}

/**
 * Ground classical reasoning with equality: the propositional search of
 * `proveTautology` whose leaves are closed by congruence closure, over facts
 * saturated with instances of universal lemmas and hypotheses. A membership
 * lemma such as `∀ x A B, x ∈ A ∪ B ↔ x ∈ A ∨ x ∈ B` is instantiated for
 * each atom `t ∈ a ∪ b` of the problem, so membership in compound sets is
 * decided from the characterizations without naming them; a universal
 * hypothesis such as an unfolded subset is instantiated at the problem's
 * terms. Everything is reconstructed from primitive natural-deduction
 * proofs, and the kernel checks the result.
 */
export function proveGround(
  kernel: Kernel,
  goal: Formula,
  assumptions: readonly Formula[] = [],
  factProofs: readonly Proof[] = [],
  options: GroundOptions = {},
): Proof {
  const fuel = options.fuel ?? 4_096;
  const instanceLimit = options.instanceLimit ?? 96;
  const facts = uniqueFacts(kernel, assumptions, factProofs);
  const known = new Set(facts.map(item => formulaCanonical(item.formula)));
  const hypothesisCount = facts.length;
  const addFact = (formula: Formula, proof: Proof): boolean => {
    const key = formulaCanonical(formula);
    if (known.has(key)) return false;
    known.add(key);
    facts.push({ formula, proof });
    if (formula.tag === "and") {
      addFact(formula.left, andElimLeft(proof));
      addFact(formula.right, andElimRight(proof));
    }
    return true;
  };

  // Universal rules and facts, with their quantifier prefix and body.
  interface Universal { readonly variables: readonly string[]; readonly body: Formula; readonly proof: Proof; readonly key: string }
  const universals: Universal[] = [];
  const seenUniversal = new Set<string>();
  const addUniversal = (formula: Formula, proof: Proof): void => {
    if (formula.tag !== "forall") return;
    const key = formulaCanonical(formula);
    if (seenUniversal.has(key)) return;
    seenUniversal.add(key);
    const variables: string[] = [];
    let body: Formula = formula;
    while (body.tag === "forall") { variables.push(body.variable); body = body.body; }
    universals.push({ variables, body, proof, key });
  };
  const lemmaKeys = new Set<string>();
  for (const rule of options.rules ?? []) {
    const statement = kernel.checkProof(rule, assumptions);
    lemmaKeys.add(formulaCanonical(statement));
    addUniversal(statement, rule);
  }

  // Ground terms of the problem, the pool for instantiating hypotheses.
  const pool = new Map<string, Term>();
  const addTerm = (term: Term): void => {
    if (term.tag === "var" && term.name.startsWith("__")) return;
    const key = termCanonical(term);
    if (!pool.has(key)) pool.set(key, term);
  };
  const atomsOf = (formula: Formula, into: Formula[] = []): Formula[] => {
    switch (formula.tag) {
      case "eq": case "pred": into.push(formula); break;
      case "and": case "or": case "imp": case "iff": atomsOf(formula.left, into); atomsOf(formula.right, into); break;
      default: break;
    }
    return into;
  };
  // The pool holds element-like terms: variables, the first argument of a
  // binary predicate such as membership, and the sides of equalities. Every
  // subterm would make instantiation explode on nested set constructions.
  const addProblemTerms = (formula: Formula): void => {
    for (const atom of atomsOf(formula)) {
      if (atom.tag === "eq") { addTerm(atom.left); addTerm(atom.right); }
      else if (atom.tag === "pred") {
        if (atom.args.length === 2) addTerm(atom.args[0]!);
        for (const argument of atom.args) if (argument.tag === "var") addTerm(argument);
      }
    }
  };

  const matchTerm = (pattern: Term, term: Term, variables: ReadonlySet<string>, substitution: Map<string, Term>): boolean => {
    if (pattern.tag === "var" && variables.has(pattern.name)) {
      const previous = substitution.get(pattern.name);
      if (previous) return termEquals(previous, term);
      substitution.set(pattern.name, term);
      return true;
    }
    if (pattern.tag !== term.tag) return false;
    if (pattern.tag === "var" && term.tag === "var") return pattern.name === term.name;
    if (pattern.tag === "nat" && term.tag === "nat") return pattern.value === term.value;
    return pattern.tag === "app" && term.tag === "app" && pattern.fn === term.fn &&
      pattern.args.length === term.args.length && pattern.args.every((argument, index) => matchTerm(argument, term.args[index]!, variables, substitution));
  };
  const matchAtom = (pattern: Formula, atom: Formula, variables: ReadonlySet<string>, substitution: Map<string, Term>): boolean => {
    if (pattern.tag === "pred" && atom.tag === "pred") {
      return pattern.pred === atom.pred && pattern.args.length === atom.args.length &&
        pattern.args.every((argument, index) => matchTerm(argument, atom.args[index]!, variables, substitution));
    }
    if (pattern.tag === "eq" && atom.tag === "eq") {
      return matchTerm(pattern.left, atom.left, variables, substitution) && matchTerm(pattern.right, atom.right, variables, substitution);
    }
    return false;
  };
  // Simultaneous substitution: a lemma variable may be replaced by a term
  // that mentions another lemma variable's name, so go through placeholders.
  const substituteAll = (formula: Formula, variables: readonly string[], substitution: ReadonlyMap<string, Term>): Formula => {
    const placeholders = variables.map((_, index) => `__ground_${index}`);
    let current = variables.reduce((result, variable, index) => substituteFormula(result, variable, v(placeholders[index]!)), formula);
    variables.forEach((variable, index) => {
      const value = substitution.get(variable);
      current = substituteFormula(current, placeholders[index]!, value ?? v(variable));
    });
    return current;
  };

  // Saturation: a universal whose body is an equivalence or implication with
  // an atomic side is instantiated wherever that side matches a problem atom;
  // a universal with no such trigger is instantiated at the pool's terms when
  // it has one variable. An equivalence to a universal body yields the
  // instances `S → φ(t)` for the pool's terms.
  let instances = 0;
  const atomPool = new Map<string, Formula>();
  const collectAtoms = (formula: Formula): void => {
    for (const atom of atomsOf(formula)) atomPool.set(formulaCanonical(atom), atom);
    addProblemTerms(formula);
  };
  collectAtoms(goal);
  facts.forEach(item => collectAtoms(item.formula));
  for (const item of facts) addUniversal(item.formula, item.proof);
  // A lemma is triggered by an atomic side of its equivalence, by its atomic
  // conclusion, or, for a negation such as `¬ x ∈ ∅`, by the negated atom.
  // A side whose arguments are all bare quantified variables, such as the
  // `x ∈ A` of `{x} ⊆ A ↔ x ∈ A`, would select every atom of its predicate;
  // it only triggers when no side of the equivalence has structure.
  const specific = (side: Formula, variables: ReadonlySet<string>): boolean => {
    const args = side.tag === "pred" ? side.args : side.tag === "eq" ? [side.left, side.right] : [];
    return args.some(term => term.tag !== "var" || !variables.has(term.name));
  };
  const triggerOf = (body: Formula, variables: ReadonlySet<string> = new Set()): Formula[] => {
    if (body.tag === "iff") {
      const sides = [body.left, body.right].filter(side => side.tag === "pred" || side.tag === "eq");
      const structured = sides.filter(side => specific(side, variables));
      return structured.length ? structured : sides;
    }
    let current = body;
    const conditions: Formula[] = [];
    while (current.tag === "imp") { conditions.push(current.left); current = current.right; }
    if (current.tag === "pred" || current.tag === "eq") return [current];
    if (current.tag === "bottom" && conditions.length && (conditions[0]!.tag === "pred" || conditions[0]!.tag === "eq")) return [conditions[0]!];
    return [];
  };
  // The atoms of a universal body that can select its instances: the
  // premises of an implication chain and its conclusion.
  const bodyTriggers = (body: Formula): Formula[] => {
    const found: Formula[] = [];
    let current = body;
    while (current.tag === "imp") {
      if (current.left.tag === "pred" || current.left.tag === "eq") found.push(current.left);
      current = current.right;
    }
    if (current.tag === "pred" || current.tag === "eq") found.push(current);
    return found;
  };
  const tried = new Set<string>();
  const atomKey = (atom: Formula): string => atom.tag === "pred" ? `pred:${atom.pred}/${atom.args.length}` : atom.tag;
  for (let round = 0; round < 4 && instances < instanceLimit; round++) {
    let changed = false;
    // Atoms indexed by predicate, so only lemmas about an occurring predicate are matched.
    const atomsByKey = new Map<string, Formula[]>();
    for (const atom of atomPool.values()) {
      const key = atomKey(atom);
      const bucket = atomsByKey.get(key);
      if (bucket) bucket.push(atom); else atomsByKey.set(key, [atom]);
    }
    const terms = [...pool.values()];
    for (const universal of universals) {
      if (instances >= instanceLimit) break;
      const variables = new Set(universal.variables);
      const isLemma = lemmaKeys.has(universal.key);
      // A hypothesis also fires forward, at the terms its premises mention.
      const triggers = isLemma ? triggerOf(universal.body, variables) : [...triggerOf(universal.body), ...bodyTriggers(universal.body)];
      const candidates: Map<string, Term>[] = [];
      for (const trigger of triggers) for (const atom of atomsByKey.get(atomKey(trigger)) ?? []) {
        const substitution = new Map<string, Term>();
        if (matchAtom(trigger, atom, variables, substitution) && universal.variables.every(name => substitution.has(name))) candidates.push(substitution);
      }
      if (candidates.length === 0 && universal.variables.length === 1 && !isLemma) {
        // A hypothesis nothing selects is instantiated at the pool's terms;
        // a lemma is left alone, so a proof depends only on lemmas its
        // atoms called for.
        for (const term of terms) candidates.push(new Map([[universal.variables[0]!, term]]));
      }
      for (const substitution of candidates) {
        const key = `${formulaCanonical(universal.body)}|${universal.variables.map(name => termCanonical(substitution.get(name)!)).join(",")}`;
        if (tried.has(key)) continue;
        tried.add(key);
        if (instances >= instanceLimit) break;
        const instance = substituteAll(universal.body, universal.variables, substitution);
        const proof = at(universal.proof, ...universal.variables.map(name => substitution.get(name)!));
        instances += 1;
        if (addFact(instance, proof)) { collectAtoms(instance); changed = true; }
        // S ↔ ∀ z, φ(z): the instances S → φ(t), at the terms t where an
        // atom of φ(t) already occurs (its premise or conclusion), or at the
        // pool's terms when φ has no such atom.
        if (instance.tag === "iff") {
          for (const [side, other, project] of [[instance.left, instance.right, iffElimLeft], [instance.right, instance.left, iffElimRight]] as const) {
            if (other.tag !== "forall") continue;
            const patterns = bodyTriggers(other.body);
            const bound = new Set([other.variable]);
            const matched: Term[] = [];
            const seen = new Set<string>();
            for (const pattern of patterns) for (const atom of atomsByKey.get(atomKey(pattern)) ?? []) {
              const substitution = new Map<string, Term>();
              if (!matchAtom(pattern, atom, bound, substitution)) continue;
              const term = substitution.get(other.variable);
              if (!term || seen.has(termCanonical(term))) continue;
              seen.add(termCanonical(term));
              matched.push(term);
            }
            for (const term of patterns.length ? matched : terms) {
              const body = substituteFormula(other.body, other.variable, term);
              const implication = imp(side, body);
              const implicationProof = impIntro(side, forallElim(impElim(project(proof), assume(side)), term));
              if (addFact(implication, implicationProof)) { collectAtoms(implication); changed = true; }
            }
          }
        }
        if (instance.tag === "forall") addUniversal(instance, proof);
      }
    }
    if (!changed) break;
  }

  // Classical search with congruence at the leaves. Branching is confined
  // to the atoms of facts whose value the valuation leaves open, taking a
  // fact with the fewest open atoms first: a fact with one open atom then
  // behaves as a unit clause, and atoms that occur in no open fact are
  // never split on.
  const frequencies = new Map<string, { formula: Formula; count: number }>();
  for (const formula of [...facts.map(item => item.formula), goal]) collectPropositionalAtoms(formula, frequencies);
  if (frequencies.size > 128) throw new Error(`ground reasoning stopped: ${frequencies.size} atoms exceed its 128-atom limit`);
  const atomsIn = new Map<Formula, Formula[]>();
  const propositionalAtoms = (formula: Formula): Formula[] => {
    let cached = atomsIn.get(formula);
    if (!cached) {
      const local = new Map<string, { formula: Formula; count: number }>();
      collectPropositionalAtoms(formula, local);
      cached = [...local.values()]
        .sort((left, right) => (frequencies.get(formulaCanonical(right.formula))?.count ?? 0) - (frequencies.get(formulaCanonical(left.formula))?.count ?? 0))
        .map(item => item.formula);
      atomsIn.set(formula, cached);
    }
    return cached;
  };
  // Atoms connected to the goal through the facts they share: branching is
  // tried on those first, so lemma instances about unrelated terms cannot
  // multiply the search; the whole atom set is the fallback. A goal of ⊥
  // starts from the hypotheses instead.
  const factAtoms = facts.map(item => propositionalAtoms(item.formula).map(formulaCanonical));
  const connected = (seeds: readonly Formula[]): Set<string> => {
    const relevant = new Set(seeds.map(formulaCanonical));
    const absorbed = new Set<number>();
    let changed = true;
    while (changed) {
      changed = false;
      factAtoms.forEach((keys, index) => {
        if (absorbed.has(index) || !keys.some(key => relevant.has(key))) return;
        absorbed.add(index);
        for (const key of keys) if (!relevant.has(key)) { relevant.add(key); changed = true; }
      });
    }
    return relevant;
  };
  const budget = { remaining: fuel };
  const runSearch = (relevant: ReadonlySet<string> | undefined): Proof => {
    const valuation = new Map<string, SignedProof>();
    const isOpen = (atom: Formula): boolean => {
      const key = formulaCanonical(atom);
      return !valuation.has(key) && (relevant === undefined || relevant.has(key));
    };
    const search = (): Proof => {
      if (budget.remaining-- <= 0) throw new Error("ground reasoning exhausted its search fuel");
      let choice: { atom: Formula; open: number } | undefined;
      const consider = (formula: Formula): void => {
        const open = propositionalAtoms(formula).filter(isOpen);
        if (open.length && (!choice || open.length < choice.open)) choice = { atom: open[0]!, open: open.length };
      };
      for (const fact of facts) {
        const value = evaluateFormula(fact.formula, valuation);
        if (value?.truth === false) return falseElim(goal, impElim(value.proof, fact.proof));
        if (value === undefined) consider(fact.formula);
      }
      const result = evaluateFormula(goal, valuation);
      if (result?.truth === true) return result.proof;
      if (result === undefined) consider(goal);
      const literals = [...valuation.entries()].map(([key, signed]) => {
        const atom = frequencies.get(key)!.formula;
        return { formula: signed.truth ? atom : not(atom), proof: signed.proof };
      });
      if (congruenceConflict([...factFormulas, ...literals.map(item => item.formula)], result === undefined ? goal : undefined)) {
        const context = [...assumptions, ...literals.map(item => item.formula)];
        const known = [...facts, ...literals];
        if (result === undefined && (goal.tag === "eq" || goal.tag === "pred")) {
          try { return proveCongruence(kernel, goal, context, [], known); }
          catch (error) { if (!(error instanceof Error) || !error.message.includes("cc found no congruence")) throw error; }
        }
        return falseElim(goal, proveCongruence(kernel, bottom, context, [], known));
      }
      if (!choice) {
        const counterexample = literals.map(item => formatAtom(item.formula)).join(", ");
        throw new Error(`ground reasoning found a counterexample${counterexample ? `: ${counterexample}` : ""}`);
      }
      const atom = (choice as { atom: Formula }).atom;
      const key = formulaCanonical(atom);
      valuation.set(key, { truth: true, proof: assume(atom) });
      const positive = search();
      valuation.set(key, { truth: false, proof: assume(not(atom)) });
      const negative = search();
      valuation.delete(key);
      return orElim(excludedMiddle(atom), positive, negative);
    };
    return search();
  };
  const seeds = goal.tag === "bottom"
    ? facts.slice(0, hypothesisCount).flatMap(item => propositionalAtoms(item.formula))
    : propositionalAtoms(goal);
  const relevant = connected(seeds);
  const debug = (globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env?.G17_GROUND_DEBUG;
  // Decide first, without proofs: the same search over a boolean valuation
  // with a proof-free congruence check at the leaves. Only a refutation it
  // finds is then rebuilt with proofs, along the same decisions.
  const factFormulas = facts.map(item => item.formula);
  const decide = (restriction: ReadonlySet<string> | undefined): string | undefined => {
    const valuation = new Map<string, boolean>();
    const isOpen = (atom: Formula): boolean => {
      const key = formulaCanonical(atom);
      return !valuation.has(key) && (restriction === undefined || restriction.has(key));
    };
    const search = (): string | undefined => {
      if (budget.remaining-- <= 0) return "ground reasoning exhausted its search fuel";
      let choice: { atom: Formula; open: number } | undefined;
      const consider = (formula: Formula): void => {
        const open = propositionalAtoms(formula).filter(isOpen);
        if (open.length && (!choice || open.length < choice.open)) choice = { atom: open[0]!, open: open.length };
      };
      for (const fact of factFormulas) {
        const value = evaluateBoolean(fact, valuation);
        if (value === false) return undefined;
        if (value === undefined) consider(fact);
      }
      const result = evaluateBoolean(goal, valuation);
      if (result === true) return undefined;
      if (result === undefined) consider(goal);
      // Congruence closes a node before the remaining open facts are split
      // on: the facts and the literals so far may already be contradictory,
      // or already entail an atomic goal.
      const literals = [...valuation.entries()].map(([key, truth]) => truth ? frequencies.get(key)!.formula : not(frequencies.get(key)!.formula));
      if (congruenceConflict([...factFormulas, ...literals], result === undefined ? goal : undefined)) return undefined;
      if (!choice) {
        const counterexample = literals.map(formatAtom).join(", ");
        return `ground reasoning found a counterexample${counterexample ? `: ${counterexample}` : ""}`;
      }
      const key = formulaCanonical((choice as { atom: Formula }).atom);
      valuation.set(key, true);
      const positive = search();
      if (positive) return positive;
      valuation.set(key, false);
      const negative = search();
      valuation.delete(key);
      return negative;
    };
    return search();
  };
  let restriction: ReadonlySet<string> | undefined = relevant;
  let verdict = decide(relevant);
  if (verdict?.includes("counterexample")) { restriction = undefined; verdict = decide(undefined); }
  if (verdict) {
    if (debug) {
      console.error(`ground detail: ${facts.length} facts (${hypothesisCount} hypotheses), ${(options.rules ?? []).length} rules, ${instances} instances, ${frequencies.size} atoms, ${relevant.size} connected, fuel left ${budget.remaining}`);
      for (const fact of facts) if (propositionalAtoms(fact.formula).some(atom => relevant.has(formulaCanonical(atom)))) console.error(`  connected fact: ${formatFormula(fact.formula)}`);
    }
    throw new Error(verdict);
  }
  budget.remaining = fuel;
  const proof = runSearch(restriction);
  if (debug === "2") {
    const seen = new Set<object>();
    const count = (node: unknown): number => {
      if (!node || typeof node !== "object" || seen.has(node)) return 0;
      seen.add(node);
      return 1 + Object.values(node as Record<string, unknown>).reduce<number>((sum, child) => sum + (Array.isArray(child) ? child.reduce<number>((inner, item) => inner + count(item), 0) : count(child)), 0);
    };
    console.error(`ground proof: ${count(proof)} nodes for ${formatAtom(goal)} (${fuel - budget.remaining} search nodes)`);
  }
  if (!formulaEquals(kernel.checkProof(proof, assumptions), goal)) throw new Error("ground reasoning produced a proof of the wrong goal");
  return proof;
}

/** `P ∨ ¬P` by classical double-negation elimination; `tauto` and `by_cases` split on it. */
export function excludedMiddle(formula: Formula): Proof {
  const choice = or(formula, not(formula));
  const denied = assume(not(choice));
  const negative = impIntro(formula, impElim(denied, orIntroLeft(assume(formula), not(formula))));
  const absurdity = impElim(denied, orIntroRight(formula, negative));
  return dne(choice, impIntro(not(choice), absurdity));
}

function evaluateFormula(formula: Formula, valuation: ReadonlyMap<string, SignedProof>): SignedProof | undefined {
  switch (formula.tag) {
    case "bottom": return { truth: false, proof: impIntro(bottom, assume(bottom)) };
    case "eq":
    case "pred":
    case "forall":
    case "exists": return valuation.get(formulaCanonical(formula));
    case "and": {
      const left = evaluateFormula(formula.left, valuation);
      const right = evaluateFormula(formula.right, valuation);
      if (left?.truth && right?.truth) return { truth: true, proof: andIntro(left.proof, right.proof) };
      if (left?.truth === false) return {
        truth: false,
        proof: impIntro(formula, impElim(left.proof, andElimLeft(assume(formula)))),
      };
      if (right?.truth === false) return {
        truth: false,
        proof: impIntro(formula, impElim(right.proof, andElimRight(assume(formula)))),
      };
      return undefined;
    }
    case "or": {
      const left = evaluateFormula(formula.left, valuation);
      const right = evaluateFormula(formula.right, valuation);
      if (left?.truth) return { truth: true, proof: orIntroLeft(left.proof, formula.right) };
      if (right?.truth) return { truth: true, proof: orIntroRight(formula.left, right.proof) };
      if (left?.truth === false && right?.truth === false) return {
        truth: false,
        proof: impIntro(formula, orElim(
          assume(formula), impElim(left.proof, assume(formula.left)), impElim(right.proof, assume(formula.right)),
        )),
      };
      return undefined;
    }
    case "imp": {
      const left = evaluateFormula(formula.left, valuation);
      const right = evaluateFormula(formula.right, valuation);
      if (left?.truth === false) return {
        truth: true,
        proof: impIntro(formula.left, falseElim(formula.right, impElim(left.proof, assume(formula.left)))),
      };
      if (right?.truth) return { truth: true, proof: impIntro(formula.left, right.proof) };
      if (left?.truth && right?.truth === false) return {
        truth: false,
        proof: impIntro(formula, impElim(right.proof, impElim(assume(formula), left.proof))),
      };
      return undefined;
    }
    case "iff": {
      const left = evaluateFormula(formula.left, valuation);
      const right = evaluateFormula(formula.right, valuation);
      if (!left || !right) return undefined;
      if (left.truth && right.truth) return {
        truth: true,
        proof: iffIntro(impIntro(formula.left, right.proof), impIntro(formula.right, left.proof)),
      };
      if (!left.truth && !right.truth) return {
        truth: true,
        proof: iffIntro(
          impIntro(formula.left, falseElim(formula.right, impElim(left.proof, assume(formula.left)))),
          impIntro(formula.right, falseElim(formula.left, impElim(right.proof, assume(formula.right)))),
        ),
      };
      if (left.truth) return {
        truth: false,
        proof: impIntro(formula, impElim(right.proof, impElim(iffElimLeft(assume(formula)), left.proof))),
      };
      return {
        truth: false,
        proof: impIntro(formula, impElim(left.proof, impElim(iffElimRight(assume(formula)), right.proof))),
      };
    }
  }
}

/** Truth of a formula under a partial boolean valuation of its atoms. */
function evaluateBoolean(formula: Formula, valuation: ReadonlyMap<string, boolean>): boolean | undefined {
  switch (formula.tag) {
    case "bottom": return false;
    case "eq": case "pred": case "forall": case "exists": return valuation.get(formulaCanonical(formula));
    case "and": {
      const left = evaluateBoolean(formula.left, valuation);
      if (left === false) return false;
      const right = evaluateBoolean(formula.right, valuation);
      if (right === false) return false;
      return left && right ? true : undefined;
    }
    case "or": {
      const left = evaluateBoolean(formula.left, valuation);
      if (left === true) return true;
      const right = evaluateBoolean(formula.right, valuation);
      if (right === true) return true;
      return left === false && right === false ? false : undefined;
    }
    case "imp": {
      const left = evaluateBoolean(formula.left, valuation);
      if (left === false) return true;
      const right = evaluateBoolean(formula.right, valuation);
      if (right === true) return true;
      return left === true && right === false ? false : undefined;
    }
    case "iff": {
      const left = evaluateBoolean(formula.left, valuation);
      const right = evaluateBoolean(formula.right, valuation);
      if (left === undefined || right === undefined) return undefined;
      return left === right;
    }
  }
}

/**
 * Whether ground facts are contradictory under congruence closure: an
 * equality chain refuting a disequality, or a predicate holding of terms
 * congruent to those it is denied of. A decision only; proveCongruence
 * produces the proof afterwards.
 */
function congruenceConflict(facts: readonly Formula[], goal?: Formula): boolean {
  const terms = new Map<string, Term>();
  const addTerm = (term: Term): void => {
    const key = termCanonical(term);
    if (terms.has(key)) return;
    terms.set(key, term);
    if (term.tag === "app") term.args.forEach(addTerm);
  };
  const equalities: Extract<Formula, { tag: "eq" }>[] = [];
  const disequalities: Extract<Formula, { tag: "eq" }>[] = [];
  const positive: Extract<Formula, { tag: "pred" }>[] = [];
  const negative: Extract<Formula, { tag: "pred" }>[] = [];
  for (const fact of facts) {
    if (fact.tag === "eq") { equalities.push(fact); addTerm(fact.left); addTerm(fact.right); }
    else if (fact.tag === "pred") { positive.push(fact); fact.args.forEach(addTerm); }
    else if (fact.tag === "imp" && fact.right.tag === "bottom") {
      if (fact.left.tag === "eq") { disequalities.push(fact.left); addTerm(fact.left.left); addTerm(fact.left.right); }
      else if (fact.left.tag === "pred") { negative.push(fact.left); fact.left.args.forEach(addTerm); }
    }
  }
  // An atomic goal is entailed when it is refuted as a negative fact would be.
  if (goal?.tag === "eq") { disequalities.push(goal); addTerm(goal.left); addTerm(goal.right); }
  else if (goal?.tag === "pred") { negative.push(goal); goal.args.forEach(addTerm); }
  if (disequalities.length === 0 && negative.length === 0) return false;
  const parent = new Map<string, string>();
  for (const key of terms.keys()) parent.set(key, key);
  const find = (key: string): string => {
    let root = key;
    while (parent.get(root) !== root) root = parent.get(root)!;
    let current = key;
    while (current !== root) { const next = parent.get(current)!; parent.set(current, root); current = next; }
    return root;
  };
  const unite = (left: string, right: string): boolean => {
    const a = find(left);
    const b = find(right);
    if (a === b) return false;
    parent.set(a, b);
    return true;
  };
  for (const equality of equalities) unite(termCanonical(equality.left), termCanonical(equality.right));
  const applications = [...terms.values()].filter((term): term is Extract<Term, { tag: "app" }> => term.tag === "app");
  let changed = equalities.length > 0;
  while (changed) {
    changed = false;
    const signatures = new Map<string, string>();
    for (const term of applications) {
      const signature = `${term.fn}:${term.args.map(argument => find(termCanonical(argument))).join("|")}`;
      const key = termCanonical(term);
      const previous = signatures.get(signature);
      if (previous === undefined) { signatures.set(signature, key); continue; }
      if (unite(previous, key)) changed = true;
    }
  }
  for (const disequality of disequalities) {
    if (find(termCanonical(disequality.left)) === find(termCanonical(disequality.right))) return true;
  }
  if (negative.length === 0) return false;
  const positiveIndex = new Map<string, string[]>();
  for (const atom of positive) {
    const key = `${atom.pred}/${atom.args.length}`;
    const bucket = positiveIndex.get(key);
    const signature = atom.args.map(argument => find(termCanonical(argument))).join("|");
    if (bucket) bucket.push(signature); else positiveIndex.set(key, [signature]);
  }
  for (const atom of negative) {
    const signature = atom.args.map(argument => find(termCanonical(argument))).join("|");
    if (positiveIndex.get(`${atom.pred}/${atom.args.length}`)?.includes(signature)) return true;
  }
  return false;
}

function uniqueKnownFacts(known: readonly AvailableFact[]): AvailableFact[] {
  const result = new Map<string, AvailableFact>();
  const add = (fact: AvailableFact): void => {
    const key = formulaCanonical(fact.formula);
    if (!result.has(key)) result.set(key, fact);
    if (fact.formula.tag === "and") {
      add({ formula: fact.formula.left, proof: andElimLeft(fact.proof) });
      add({ formula: fact.formula.right, proof: andElimRight(fact.proof) });
    }
  };
  known.forEach(add);
  return [...result.values()];
}

function collectPropositionalAtoms(formula: Formula, atoms: Map<string, { formula: Formula; count: number }>): void {
  switch (formula.tag) {
    case "bottom": return;
    case "eq":
    case "pred":
    case "forall":
    case "exists": {
      const key = formulaCanonical(formula);
      const previous = atoms.get(key);
      atoms.set(key, { formula, count: (previous?.count ?? 0) + 1 });
      return;
    }
    case "imp":
    case "and":
    case "or":
    case "iff":
      collectPropositionalAtoms(formula.left, atoms);
      collectPropositionalAtoms(formula.right, atoms);
  }
}

function formatAtom(formula: Formula): string {
  const formatted = formatFormula(formula);
  return formatted.length <= 48 ? formatted : `${formatted.slice(0, 45)}...`;
}

interface AvailableFact { readonly formula: Formula; readonly proof: Proof }

function uniqueFacts(kernel: Kernel, assumptions: readonly Formula[], proofs: readonly Proof[]): AvailableFact[] {
  const result = new Map<string, AvailableFact>();
  const add = (fact: AvailableFact): void => {
    const key = formulaCanonical(fact.formula);
    if (!result.has(key)) result.set(key, fact);
    if (fact.formula.tag === "and") {
      add({ formula: fact.formula.left, proof: andElimLeft(fact.proof) });
      add({ formula: fact.formula.right, proof: andElimRight(fact.proof) });
    }
  };
  assumptions.forEach(formula => add({ formula, proof: assume(formula) }));
  proofs.forEach(proof => add({ formula: kernel.checkProof(proof, assumptions), proof }));
  return [...result.values()];
}

/**
 * Ground congruence closure with proof-producing union-find explanations.
 * Besides equality goals, it closes any goal from a congruent disequality or
 * positive/negative predicate conflict and transports congruent predicates.
 */
export function proveCongruence(
  kernel: Kernel,
  goal: Formula,
  assumptions: readonly Formula[] = [],
  factProofs: readonly Proof[] = [],
  knownFacts?: readonly AvailableFact[],
): Proof {
  const facts = knownFacts ? uniqueKnownFacts(knownFacts) : uniqueFacts(kernel, assumptions, factProofs);
  const terms = new Map<string, Term>();
  const addTerm = (term: Term): void => {
    const key = termCanonical(term);
    if (terms.has(key)) return;
    terms.set(key, term);
    if (term.tag === "app") term.args.forEach(addTerm);
  };
  const addFormulaTerms = (formula: Formula): void => {
    if (formula.tag === "eq") { addTerm(formula.left); addTerm(formula.right); }
    else if (formula.tag === "pred") formula.args.forEach(addTerm);
    else if (["imp", "and", "or", "iff"].includes(formula.tag)) {
      const binary = formula as Extract<Formula, { tag: "imp" | "and" | "or" | "iff" }>;
      addFormulaTerms(binary.left); addFormulaTerms(binary.right);
    }
  };
  facts.forEach(item => addFormulaTerms(item.formula));
  addFormulaTerms(goal);

  const parent = new Map<string, string>();
  const rank = new Map<string, number>();
  const proofToParent = new Map<string, Proof>();
  for (const key of terms.keys()) { parent.set(key, key); rank.set(key, 0); }

  const find = (key: string): { readonly root: string; readonly proof: Proof } => {
    const next = parent.get(key)!;
    if (next === key) return { root: key, proof: refl(terms.get(key)!) };
    const tail = find(next);
    const proof = calc(proofToParent.get(key)!, tail.proof);
    parent.set(key, tail.root);
    proofToParent.set(key, proof);
    return { root: tail.root, proof };
  };
  const explain = (left: Term, right: Term): Proof | undefined => {
    const a = find(termCanonical(left));
    const b = find(termCanonical(right));
    return a.root === b.root ? calc(a.proof, symm(b.proof)) : undefined;
  };
  const unite = (left: Term, right: Term, equality: Proof): boolean => {
    const leftKey = termCanonical(left);
    const rightKey = termCanonical(right);
    const a = find(leftKey);
    const b = find(rightKey);
    if (a.root === b.root) return false;
    const rootEquality = calc(symm(a.proof), equality, b.proof);
    const aRank = rank.get(a.root) ?? 0;
    const bRank = rank.get(b.root) ?? 0;
    if (aRank < bRank) {
      parent.set(a.root, b.root);
      proofToParent.set(a.root, rootEquality);
    } else {
      parent.set(b.root, a.root);
      proofToParent.set(b.root, symm(rootEquality));
      if (aRank === bRank) rank.set(a.root, aRank + 1);
    }
    return true;
  };

  for (const fact of facts) {
    if (fact.formula.tag === "eq") unite(fact.formula.left, fact.formula.right, fact.proof);
  }
  const depths = new Map<string, number>();
  const termDepth = (term: Term): number => {
    const key = termCanonical(term);
    const cached = depths.get(key);
    if (cached !== undefined) return cached;
    const depth = term.tag === "app" ? 1 + Math.max(0, ...term.args.map(termDepth)) : 0;
    depths.set(key, depth);
    return depth;
  };
  const applications = [...terms.values()]
    .filter((term): term is Extract<Term, { tag: "app" }> => term.tag === "app")
    .sort((left, right) => termDepth(left) - termDepth(right));
  let changed = true;
  while (changed) {
    changed = false;
    const signatures = new Map<string, Extract<Term, { tag: "app" }>>();
    for (const term of applications) {
      const signature = `${term.fn.length}:${term.fn}:${term.args.map(argument => find(termCanonical(argument)).root).join("|")}`;
      const previous = signatures.get(signature);
      if (!previous) { signatures.set(signature, term); continue; }
      if (find(termCanonical(previous)).root === find(termCanonical(term)).root) continue;
      const argumentProofs = previous.args.map((argument, index) => explain(argument, term.args[index]!)!);
      if (unite(previous, term, congr(term.fn, ...argumentProofs))) changed = true;
    }
  }

  const transportPredicate = (
    source: Extract<Formula, { tag: "pred" }>, target: Extract<Formula, { tag: "pred" }>, proof: Proof,
  ): Proof | undefined => {
    if (source.pred !== target.pred || source.args.length !== target.args.length) return undefined;
    let current = source;
    let result = proof;
    for (let index = 0; index < current.args.length; index += 1) {
      if (termEquals(current.args[index]!, target.args[index]!)) continue;
      const equality = explain(current.args[index]!, target.args[index]!);
      if (!equality) return undefined;
      let variable = "__ccTransport";
      const forbidden = freeFormulaVariables(current);
      while (forbidden.has(variable)) variable += "_";
      const args = [...current.args];
      args[index] = v(variable);
      result = eqElim(equality, variable, pred(current.pred, ...args), result);
      const nextArgs = [...current.args];
      nextArgs[index] = target.args[index]!;
      current = pred(current.pred, ...nextArgs);
    }
    return result;
  };

  if (goal.tag === "eq") {
    const equality = explain(goal.left, goal.right);
    if (equality) return checkedCongruenceResult(kernel, equality, goal, assumptions);
  }
  if (goal.tag === "pred") {
    for (const fact of facts) if (fact.formula.tag === "pred") {
      const proof = transportPredicate(fact.formula, goal, fact.proof);
      if (proof) return checkedCongruenceResult(kernel, proof, goal, assumptions);
    }
  }

  for (const fact of facts) {
    if (fact.formula.tag !== "imp" || fact.formula.right.tag !== "bottom") continue;
    if (fact.formula.left.tag === "eq") {
      const equality = explain(fact.formula.left.left, fact.formula.left.right);
      if (equality) return checkedCongruenceResult(kernel, falseElim(goal, impElim(fact.proof, equality)), goal, assumptions);
    }
    if (fact.formula.left.tag === "pred") {
      for (const positive of facts) if (positive.formula.tag === "pred") {
        const proof = transportPredicate(positive.formula, fact.formula.left, positive.proof);
        if (proof) return checkedCongruenceResult(kernel, falseElim(goal, impElim(fact.proof, proof)), goal, assumptions);
      }
    }
  }
  throw new Error("cc found no congruence consequence or contradiction");
}

function checkedCongruenceResult(
  kernel: Kernel, proof: Proof, goal: Formula, assumptions: readonly Formula[],
): Proof {
  if (!formulaEquals(kernel.checkProof(proof, assumptions), goal)) throw new Error("cc produced a proof of the wrong goal");
  return proof;
}
