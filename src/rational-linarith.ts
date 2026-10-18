// Linear arithmetic over the rationals, as a presentation of the real engine.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { app, bottom, eq, formulaEquals, pred, termEquals, v, freeTermVariables, type Formula, type Term } from "./ast.ts";
import { assume, eqElim, falseElim, orElim, refl, symm, type Proof } from "./proof.ts";
import { proveRealLinearArithmetic, type RealLinearArithmeticContext } from "./real-linarith.ts";

/**
 * The rationals carry a strict order only, so the Fourier-Motzkin engine
 * runs with equalities standing in for non-strict comparisons: an equality
 * fact enters as two non-strict constraints, sums of equalities are built by
 * substitution, and a strict total is transported along an equality rather
 * than composed with a non-strict law. Goals `s < t` and `s = t` are settled
 * by trichotomy, each remaining case refuted by the engine with that case
 * added to the facts.
 */
export interface RationalLinearArithmeticContext {
  readonly goal: Formula;
  readonly facts: readonly { readonly formula: Formula; readonly proof: Proof }[];
  readonly symbols: RealLinearArithmeticContext["symbols"];
  /** The strict order graph rationalLess, as a term. */
  readonly less: Term;
  /** Instantiate a named rational order lemma, discharge its Rational guards, and feed the premises. */
  readonly lemma: (name: string, terms: readonly Term[], premises: readonly Proof[]) => Proof | undefined;
  /** A closed library theorem, such as rationalZero.lt_one. */
  readonly theoremFact: (name: string) => Proof | undefined;
  readonly isRational: (term: Term) => boolean;
  readonly ringEquality: (left: Term, right: Term) => Proof | undefined;
  readonly check: (proof: Proof) => Formula;
  readonly extraAssumptions: Formula[];
  readonly constraintLimit?: number;
}

export function proveRationalLinearArithmetic(context: RationalLinearArithmeticContext): Proof | undefined {
  const { call2, addGraph } = context.symbols;
  if (!call2 || !addGraph) return undefined;
  const sum = (left: Term, right: Term): Term => app(call2, addGraph, left, right);
  const strict = (left: Term, right: Term): Formula => pred("relates", context.less, left, right);
  const fresh = (terms: readonly Term[]): string => {
    const forbidden = new Set(terms.flatMap(term => [...freeTermVariables(term)]));
    let variable = "__qlinarith";
    while (forbidden.has(variable)) variable += "_";
    return variable;
  };
  const parse = (formula: Formula): { strict: boolean; left: Term; right: Term } | undefined =>
    formula.tag === "pred" && formula.pred === "relates" && formula.args.length === 3 &&
    termEquals(formula.args[0]!, context.less)
      ? { strict: true, left: formula.args[1]!, right: formula.args[2]! }
      : undefined;

  // The engine's rule names, read over a strict order with equalities.
  const rule = (name: string, terms: readonly Term[], premises: readonly Proof[]): Proof | undefined => {
    try {
      switch (name) {
        case "realLe.reflexive": return refl(terms[0]!);
        case "realLe.add": {
          const [a, b, c, d] = terms as [Term, Term, Term, Term];
          const [ab, cd] = premises as [Proof, Proof];
          const x = fresh(terms);
          const shifted = eqElim(ab, x, eq(sum(a, c), sum(v(x), c)), refl(sum(a, c)));
          return eqElim(cd, x, eq(sum(a, c), sum(b, v(x))), shifted);
        }
        case "realLe.add_right": {
          const [a, , c] = terms as [Term, Term, Term];
          const x = fresh(terms);
          return eqElim(premises[0]!, x, eq(sum(a, c), sum(v(x), c)), refl(sum(a, c)));
        }
        case "realLe.add_left": {
          const [a, , c] = terms as [Term, Term, Term];
          const x = fresh(terms);
          return eqElim(premises[0]!, x, eq(sum(c, a), sum(c, v(x))), refl(sum(c, a)));
        }
        case "realLess.add": {
          const [a, b, c, d] = terms as [Term, Term, Term, Term];
          const [ab, cd] = premises as [Proof, Proof];
          const shifted = context.lemma("rationalLess.add_right", [a, b, c], [ab]);
          const raised = context.lemma("rationalLess.add_left", [c, d, b], [cd]);
          if (!shifted || !raised) return undefined;
          return context.lemma("rationalLess.transitive", [sum(a, c), sum(b, c), sum(b, d)], [shifted, raised]);
        }
        case "realLess.add_right": return context.lemma("rationalLess.add_right", terms, premises);
        case "realLess.add_left": return context.lemma("rationalLess.add_left", terms, premises);
        case "realLe.transitive_less": {
          // left = middle and middle < right give left < right.
          const [left, , right] = terms as [Term, Term, Term];
          const [equal, less] = premises as [Proof, Proof];
          const x = fresh(terms);
          return eqElim(symm(equal), x, strict(v(x), right), less);
        }
        case "realLess.transitive_le": {
          // left < middle and middle = right give left < right.
          const [left] = terms as [Term, Term, Term];
          const [less, equal] = premises as [Proof, Proof];
          const x = fresh(terms);
          return eqElim(equal, x, strict(left, v(x)), less);
        }
        case "realLess.not_self": return context.lemma("rationalLess.irreflexive", terms, premises);
        default: return undefined;
      }
    } catch { return undefined; }
  };
  const engine = (goal: Formula, extra: readonly { formula: Formula; proof: Proof }[]): Proof | undefined =>
    proveRealLinearArithmetic({
      goal,
      facts: [...context.facts, ...extra],
      symbols: context.symbols,
      comparison: {
        build: (isStrict, left, right) => isStrict ? strict(left, right) : eq(left, right),
        parse,
      },
      rule,
      theoremFact: name => name === "realZero.lt_one" ? context.theoremFact("rationalZero.lt_one") : undefined,
      isReal: context.isRational,
      ringEquality: context.ringEquality,
      check: context.check,
      extraAssumptions: context.extraAssumptions,
      ...(context.constraintLimit !== undefined ? { constraintLimit: context.constraintLimit } : {}),
    });

  const { goal } = context;
  if (goal.tag === "bottom") return engine(goal, []);
  if (goal.tag === "imp" && goal.right.tag === "bottom" && parse(goal.left)) return engine(goal, []);

  // s < t or s = t: split on trichotomy and refute every other case.
  const target = parse(goal) ?? (goal.tag === "eq" && context.isRational(goal.left) && context.isRational(goal.right)
    ? { strict: false, left: goal.left, right: goal.right } : undefined);
  if (!target) return undefined;
  const trichotomy = context.lemma("rationalLess.trichotomy", [target.left, target.right], []);
  if (!trichotomy) return undefined;
  const refute = (formula: Formula, proof: Proof): Proof | undefined => {
    if (formulaEquals(formula, goal)) return proof;
    if (!parse(formula) && formula.tag !== "eq") return undefined;
    context.extraAssumptions.push(formula);
    try {
      const absurdity = engine(bottom, [{ formula, proof }]);
      return absurdity ? falseElim(goal, absurdity) : undefined;
    } finally {
      context.extraAssumptions.pop();
    }
  };
  const split = (proof: Proof, formula: Formula): Proof | undefined => {
    if (formula.tag !== "or") return refute(formula, proof);
    const left = split(assume(formula.left), formula.left);
    if (!left) return undefined;
    const right = split(assume(formula.right), formula.right);
    if (!right) return undefined;
    return orElim(proof, left, right);
  };
  let shape: Formula;
  try { shape = context.check(trichotomy); } catch { return undefined; }
  const result = split(trichotomy, shape);
  if (!result) return undefined;
  try { return formulaEquals(context.check(result), goal) ? result : undefined; } catch { return undefined; }
}
