// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Large cardinal hypotheses are predicates a module registers with
// `register largecardinal`: sentences such as TarskiGrothendieck(), and
// properties of a set such as Inaccessible(κ). Grace17 has no large
// cardinal axiom; a theorem that needs one takes it as a premise, and its
// certificate is a ZF(C) certificate of the implication.
//
// A premise P(κ) whose κ the conclusion does not mention says, in effect,
// "if some κ has P": the theorem relies on the hypothesis. A premise P(κ)
// whose κ the conclusion mentions makes the theorem a fact about such κ,
// true whether or not any exists. A theorem that uses a lemma about P(κ)
// without such a premise of its own has supplied P(t) some other way, which
// ZF(C) cannot do outright, so it relies on the hypothesis too. This module
// classifies one statement; the axiom audit closes the classification over
// a proof's dependencies.

import type { Formula, Term } from "./ast.ts";
import type { Kernel } from "./kernel.ts";
import { largeCardinalRegistrations } from "./surface.ts";

export interface LargeCardinalHypothesis {
  readonly predicate: string;
  /** What the hypothesis says, as its registration words it. */
  readonly label: string;
  readonly module?: string;
}

export interface LargeCardinalStatement {
  /** Hypotheses the statement relies on: a sentence or a property of something its conclusion does not mention, as a premise. */
  readonly reliesOn: readonly LargeCardinalHypothesis[];
  /** Hypotheses the statement is about: a premise property of something its conclusion mentions. */
  readonly about: readonly LargeCardinalHypothesis[];
  /** Hypotheses that occur only positively, as what the theorem proves. */
  readonly mentions: readonly LargeCardinalHypothesis[];
}

const EMPTY: LargeCardinalStatement = { reliesOn: [], about: [], mentions: [] };

function termVariables(term: Term, into: Set<string>): void {
  if (term.tag === "var") into.add(term.name);
  else if (term.tag === "app") for (const argument of term.args) termVariables(argument, into);
}

/** The free variables of a formula. */
function freeVariables(formula: Formula, bound: ReadonlySet<string> = new Set(), into = new Set<string>()): Set<string> {
  switch (formula.tag) {
    case "bottom": return into;
    case "eq": {
      const found = new Set<string>();
      termVariables(formula.left, found); termVariables(formula.right, found);
      for (const name of found) if (!bound.has(name)) into.add(name);
      return into;
    }
    case "pred": {
      const found = new Set<string>();
      for (const argument of formula.args) termVariables(argument, found);
      for (const name of found) if (!bound.has(name)) into.add(name);
      return into;
    }
    case "forall": case "exists": return freeVariables(formula.body, new Set([...bound, formula.variable]), into);
    default: freeVariables(formula.left, bound, into); return freeVariables(formula.right, bound, into);
  }
}

/** The registered large cardinal hypotheses in `statement`, classified as the module comment describes. */
export function largeCardinalOccurrences(kernel: Kernel, statement: Formula): LargeCardinalStatement {
  const registered = new Map(largeCardinalRegistrations(kernel).map(item => [item.predicate, item]));
  if (registered.size === 0) return EMPTY;
  const relies = new Set<string>();
  const about = new Set<string>();
  const positive = new Set<string>();
  const visit = (formula: Formula, polarity: boolean): void => {
    switch (formula.tag) {
      case "pred":
        if (registered.has(formula.pred)) (polarity ? positive : relies).add(formula.pred);
        return;
      case "imp": visit(formula.left, !polarity); visit(formula.right, polarity); return;
      // An equivalence rests on neither side; a proof that uses one of its
      // directions supplies the other side, and is classified by that.
      case "iff": visit(formula.left, true); visit(formula.right, true); return;
      case "and": case "or": visit(formula.left, polarity); visit(formula.right, polarity); return;
      case "forall": case "exists": visit(formula.body, polarity); return;
      default: return;
    }
  };
  // The statement's spine: ∀x̄, P₁ → … → Pₙ → C, a negation ¬P (P → ⊥)
  // being a conclusion.
  const premises: Formula[] = [];
  let conclusion = statement;
  while (conclusion.tag === "forall" || (conclusion.tag === "imp" && conclusion.right.tag !== "bottom")) {
    if (conclusion.tag === "imp") premises.push(conclusion.left);
    conclusion = conclusion.tag === "forall" ? conclusion.body : conclusion.right;
  }
  const concluded = freeVariables(conclusion);
  for (const premise of premises) {
    if (premise.tag === "pred" && registered.has(premise.pred)) {
      const mentioned = new Set<string>();
      for (const argument of premise.args) termVariables(argument, mentioned);
      (mentioned.size > 0 && [...mentioned].every(name => concluded.has(name)) ? about : relies).add(premise.pred);
    } else visit(premise, false);
  }
  visit(conclusion, true);
  const ordered = (names: Iterable<string>) => [...names].sort().map(name => registered.get(name)!);
  return {
    reliesOn: ordered(relies),
    about: ordered([...about].filter(name => !relies.has(name))),
    mentions: ordered([...positive].filter(name => !relies.has(name) && !about.has(name))),
  };
}

/**
 * The registered hypotheses `names` stand for, with those their definitions
 * use, transitively: ExistsInaccessible() is ∃κ, Inaccessible(κ), so a
 * statement that mentions the first mentions the second.
 */
export function throughDefinitions(kernel: Kernel, names: Iterable<string>): Set<string> {
  const registered = new Set(largeCardinalRegistrations(kernel).map(item => item.predicate));
  const result = new Set<string>();
  const pending = [...names];
  while (pending.length) {
    const name = pending.pop()!;
    if (result.has(name)) continue;
    result.add(name);
    const record = kernel.definitions.get(name);
    if (!record) continue;
    const found = new Set<string>();
    const collect = (formula: Formula): void => {
      switch (formula.tag) {
        case "pred": if (registered.has(formula.pred)) found.add(formula.pred); return;
        case "forall": case "exists": collect(formula.body); return;
        case "imp": case "and": case "or": case "iff": collect(formula.left); collect(formula.right); return;
        default: return;
      }
    };
    for (const property of record.properties.values()) collect(property);
    for (const item of found) if (!result.has(item)) pending.push(item);
  }
  return result;
}

/** The registered large cardinal hypotheses of a theorem's statement. */
export function theoremLargeCardinals(kernel: Kernel, theorem: string): LargeCardinalStatement {
  const statement = kernel.theorems.get(theorem);
  return statement ? largeCardinalOccurrences(kernel, statement) : EMPTY;
}
