// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import type { Formula, Term } from "./ast.ts";

export type Proof =
  | { readonly rule: "assumption"; readonly formula: Formula }
  | { readonly rule: "axiom"; readonly name: string }
  | { readonly rule: "theorem"; readonly name: string }
  | { readonly rule: "definition"; readonly name: string; readonly property?: string }
  | { readonly rule: "refl"; readonly term: Term }
  | {
      /** Kernel-replayed definitional equality for closed terms. */
      readonly rule: "compute";
      readonly left: Term;
      readonly right: Term;
      /** Exact allow-list of admitted function equations used by reduction. */
      readonly definitions: readonly string[];
    }
  | { readonly rule: "rationalClassCompute"; readonly left: Term; readonly right: Term }
  | { readonly rule: "symm"; readonly proof: Proof }
  | { readonly rule: "trans"; readonly left: Proof; readonly right: Proof }
  | { readonly rule: "congr"; readonly fn: string; readonly proofs: readonly Proof[] }
  | { readonly rule: "eqElim"; readonly equality: Proof; readonly variable: string; readonly motive: Formula; readonly evidence: Proof; readonly reverse?: boolean }
  | { readonly rule: "impIntro"; readonly assumption: Formula; readonly body: Proof }
  | { readonly rule: "impElim"; readonly implication: Proof; readonly argument: Proof }
  | { readonly rule: "forallIntro"; readonly variable: string; readonly body: Proof }
  | { readonly rule: "forallElim"; readonly universal: Proof; readonly term: Term }
  | { readonly rule: "andIntro"; readonly left: Proof; readonly right: Proof }
  | { readonly rule: "andElimLeft"; readonly conjunction: Proof }
  | { readonly rule: "andElimRight"; readonly conjunction: Proof }
  | { readonly rule: "orIntroLeft"; readonly proof: Proof; readonly right: Formula }
  | { readonly rule: "orIntroRight"; readonly left: Formula; readonly proof: Proof }
  | { readonly rule: "orElim"; readonly disjunction: Proof; readonly left: Proof; readonly right: Proof }
  | { readonly rule: "iffIntro"; readonly forward: Proof; readonly backward: Proof }
  | { readonly rule: "iffElimLeft"; readonly equivalence: Proof }
  | { readonly rule: "iffElimRight"; readonly equivalence: Proof }
  | { readonly rule: "existsIntro"; readonly variable: string; readonly body: Formula; readonly witness: Term; readonly evidence: Proof }
  | { readonly rule: "existsElim"; readonly existential: Proof; readonly witness: string; readonly body: Proof }
  | { readonly rule: "falseElim"; readonly conclusion: Formula; readonly absurdity: Proof }
  | { readonly rule: "dne"; readonly proposition: Formula; readonly proof: Proof }
  | {
      readonly rule: "induction";
      readonly datatype: string;
      readonly parameters: readonly Term[];
      readonly variable: string;
      readonly motive: Formula;
      readonly cases: readonly {
        readonly constructor: string;
        readonly fields: readonly string[];
        readonly proof: Proof;
      }[];
    }
  | {
      readonly rule: "wellFoundedInduction";
      readonly relation: Term;
      readonly domain: Term;
      readonly variable: string;
      readonly predecessor: string;
      readonly motive: Formula;
      readonly wellFounded: Proof;
      readonly step: Proof;
    };

export const assume = (formula: Formula): Proof => ({ rule: "assumption", formula });
export const axiom = (name: string): Proof => ({ rule: "axiom", name });
export const theorem = (name: string): Proof => ({ rule: "theorem", name });
export const definition = (name: string, property = "equation"): Proof => ({ rule: "definition", name, property });
export const refl = (term: Term): Proof => ({ rule: "refl", term });
export const compute = (left: Term, right: Term, definitions: readonly string[]): Proof =>
  ({ rule: "compute", left, right, definitions: [...definitions] });
export const rationalClassCompute = (left: Term, right: Term): Proof =>
  ({ rule: "rationalClassCompute", left, right });
export const symm = (proof: Proof): Proof => ({ rule: "symm", proof });
export const trans = (left: Proof, right: Proof): Proof => ({ rule: "trans", left, right });
export const congr = (fn: string, ...proofs: Proof[]): Proof => ({ rule: "congr", fn, proofs });
export const eqElim = (equality: Proof, variable: string, motive: Formula, evidence: Proof, reverse = false): Proof =>
  ({ rule: "eqElim", equality, variable, motive, evidence, reverse });
export const impIntro = (assumption: Formula, body: Proof): Proof => ({ rule: "impIntro", assumption, body });
export const impElim = (implication: Proof, argument: Proof): Proof => ({ rule: "impElim", implication, argument });
export const forallIntro = (variable: string, body: Proof): Proof => ({ rule: "forallIntro", variable, body });
export const forallElim = (universal: Proof, term: Term): Proof => ({ rule: "forallElim", universal, term });
export const andIntro = (left: Proof, right: Proof): Proof => ({ rule: "andIntro", left, right });
export const andElimLeft = (conjunction: Proof): Proof => ({ rule: "andElimLeft", conjunction });
export const andElimRight = (conjunction: Proof): Proof => ({ rule: "andElimRight", conjunction });
export const orIntroLeft = (proof: Proof, right: Formula): Proof => ({ rule: "orIntroLeft", proof, right });
export const orIntroRight = (left: Formula, proof: Proof): Proof => ({ rule: "orIntroRight", left, proof });
export const orElim = (disjunction: Proof, left: Proof, right: Proof): Proof => ({ rule: "orElim", disjunction, left, right });
export const iffIntro = (forward: Proof, backward: Proof): Proof => ({ rule: "iffIntro", forward, backward });
export const iffElimLeft = (equivalence: Proof): Proof => ({ rule: "iffElimLeft", equivalence });
export const iffElimRight = (equivalence: Proof): Proof => ({ rule: "iffElimRight", equivalence });
export const existsIntro = (variable: string, body: Formula, witness: Term, evidence: Proof): Proof =>
  ({ rule: "existsIntro", variable, body, witness, evidence });
export const existsElim = (existential: Proof, witness: string, body: Proof): Proof =>
  ({ rule: "existsElim", existential, witness, body });
export const falseElim = (conclusion: Formula, absurdity: Proof): Proof => ({ rule: "falseElim", conclusion, absurdity });
export const dne = (proposition: Formula, proof: Proof): Proof => ({ rule: "dne", proposition, proof });
export const induction = (
  datatype: string,
  variable: string,
  motive: Formula,
  cases: Extract<Proof, { rule: "induction" }>["cases"],
  parameters: readonly Term[] = [],
): Proof => ({ rule: "induction", datatype, parameters: [...parameters], variable, motive, cases });
export const wellFoundedInduction = (
  relation: Term,
  domain: Term,
  variable: string,
  predecessor: string,
  motive: Formula,
  wellFounded: Proof,
  step: Proof,
): Proof => ({
  rule: "wellFoundedInduction", relation, domain, variable, predecessor,
  motive, wellFounded, step,
});

// Ergonomic proof assembly. These are untrusted macros: each builds the
// primitive proof object that Kernel.checkProof independently validates.
export function at(proof: Proof, ...terms: readonly Term[]): Proof {
  return terms.reduce<Proof>((result, term) => forallElim(result, term), proof);
}

export function equation(name: string, clause: number | string, ...terms: readonly Term[]): Proof {
  const property = typeof clause === "number" ? `equation.${clause}` : clause;
  return at(definition(name, property), ...terms);
}

export function calc(first: Proof, ...rest: readonly Proof[]): Proof {
  return rest.reduce<Proof>((result, proof) => trans(result, proof), first);
}

export function all(variables: readonly string[], proof: Proof): Proof {
  return variables.reduceRight<Proof>((result, variable) => forallIntro(variable, result), proof);
}

export function given(assumptions: readonly Formula[], proof: Proof): Proof {
  return assumptions.reduceRight<Proof>((result, assumption) => impIntro(assumption, result), proof);
}
