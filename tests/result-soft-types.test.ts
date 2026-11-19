// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  createZfgKernel, formatFormula, loadModuleSourceGraph,
} from "../src/index.ts";

// A definition's result may carry any soft type a binder may carry: a
// predicate with its carrier, `: List(A)`, or a carrier the facts in scope
// supply, `: R` under CommRing(R). The elaborator owes `f.type`, proved by
// inference, by the definition's induction, or by the author, and the value
// is placed by that typing.
const lists =
  "module Results\nimport Grace.Cumulus.Algebra.Polynomial.HornerArithmetic\n";

function load(source: string, file = "Results.g17") {
  const kernel = createZfgKernel();
  const loaded = loadModuleSourceGraph(kernel, [{ file, source }], ["lib"]);
  return {
    kernel, warnings: loaded.find(item => item.file === file)!.warnings,
  };
}

function failure(source: string): string {
  try {
    load(source);
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
  throw new Error("expected a failure");
}

test("an explicit definition with a List result is typed by inference and " +
  "its value is placed as a list", () => {
  const { kernel } = load(lists + `
def fullList {A : Set} (leading ∈ A) (cs : List(A)) : List(A) :=
  append{A}(leading :: [], cs)

theorem fullList.typed (A leading : Set) (cs : List(A))
  requires initial : leading ∈ A
  shows List(A, fullList{A}(leading, cs))
proof
  exact fullList.type

theorem fullList.placed (A leading h : Set) (cs : List(A))
  requires initial : leading ∈ A
  shows length(fullList{A}(leading, cs)) =
      length(fullList{A}(leading, cs)) ∧
    listMap{A}(h, fullList{A}(leading, cs)) =
      listMap{A}(h, fullList{A}(leading, cs))
proof
  refine ⟨rfl, rfl⟩
`);
  assert.equal(formatFormula(kernel.theorems.get("Results.fullList.type")!),
    "∀ A, ∀ leading ∈ A, ∀ cs, List(A, cs) → " +
    "List(A, fullList(A, leading, cs))");
});

test("an equation-style definition with a List result is typed by its " +
  "induction, a guarded parameter generalized too", () => {
  const { kernel } = load(lists + `
def dup {A : Set} (xs : List(A)) → List(A)
  | List.nil => []
  | List.cons(x, tail) => x :: x :: dup(tail)
  descends xs

def padded {A : Set} (z ∈ A) (xs : List(A)) → List(A)
  | z, List.nil => z :: []
  | z, List.cons(x, tail) => x :: padded(z, tail)
  descends xs

theorem padded.typed (A z : Set) (xs : List(A))
  requires zin : z ∈ A
  shows List(A, padded{A}(z, dup{A}(xs)))
proof
  typecheck
`);
  assert.ok(kernel.theorems.has("Results.dup.type"));
  assert.equal(formatFormula(kernel.theorems.get("Results.padded.type")!),
    "∀ A, ∀ z ∈ A, ∀ xs, List(A, xs) → List(A, padded(A, z, xs))");
});

test("a result inference cannot type is proved by the author, and " +
  "unproved it is an error", () => {
  const dropping = lists + `import Grace.Cumulus.List.Filter

def dropZ {A : Set} (zero : Set) (xs : List(A)) → List(A)
  | zero, List.nil => []
  | zero, List.cons(x, tail) =>
      boolChoice(memberTest({zero}, x), dropZ(zero, tail), x :: tail)
  descends xs
`;
  assert.match(failure(dropping),
    /cannot prove declared result type of Results\.dropZ; add a proof block/);
  const { kernel } = load(dropping + `proof
  induction xs
  | List.nil =>
    rw dropZ
    typecheck
  | List.cons(x, tail) using ih =>
    sorry
`);
  assert.ok(kernel.theorems.has("Results.dropZ.type"));
  const explicit = lists + `
def twice {A : Set} (cs : List(A)) : List(A) := append{A}(cs, cs)
proof
  unfold twice
  typecheck
`;
  assert.ok(load(explicit).kernel.theorems.has("Results.twice.type"));
});

test("a definition in a section owes its type under the section " +
  "hypotheses, which its proof may use and its uses supply", () => {
  const section = lists + `
section Negation
variable (A neg : Set)
hypothesis function : neg : A → A

def negList (cs : List(A)) : List(A) := listMap{A}(neg, cs)
proof
  unfold negList
  typecheck

theorem negList.inside (cs : List(A))
  shows List(A, negList(cs))
proof
  exact negList.type
end Negation

theorem negList.outside (A neg : Set) (cs : List(A))
  requires function : neg : A → A
  shows List(A, negList(A, neg, cs))
proof
  exact negList.type with function
`;
  const { kernel } = load(section);
  assert.equal(formatFormula(kernel.theorems.get("Results.negList.type")!),
    "∀ A, ∀ neg, ∀ cs, List(A, cs) → FunctionBetween(neg, A, A) → " +
    "List(A, negList(A, neg, cs))");
  // Outside the section the premise is owed: a fact in scope supplies it,
  // and without one the use fails.
  const unsupplied = section
    .replace("  requires function : neg : A → A\n", "")
    .replace("exact negList.type with function", "exact negList.type");
  assert.match(failure(unsupplied), /negList\.type needs evidence for/);
  // A pending obligation is discharged by a closure theorem written inside
  // the section, which has the same premises.
  const handWritten = load(lists + `
section Negation
variable (A neg : Set)
hypothesis closed : ∀ x, x ∈ A → neg(x) ∈ A

def negList (cs : List(A)) : List(A) := listMap{A}(neg, cs)

theorem negList.type (cs : List(A))
  shows List(A, negList(cs))
proof
  sorry
end Negation
`);
  assert.equal(
    formatFormula(handWritten.kernel.theorems.get("Results.negList.type")!),
    "∀ A, ∀ neg, ∀ cs, List(A, cs) → (∀ x ∈ A, neg(x) ∈ A) → " +
    "List(A, negList(A, neg, cs))");
});

test("a section definition with a Nat result takes the section hypotheses " +
  "as premises of its type", () => {
  const { kernel } = load(`module Results
import Grace.Cumulus.Nat

section Shifted
variable (k : Set)
hypothesis natural : Nat(k)

def shifted (n : Nat) : Nat := n + k
proof
  unfold shifted
  typecheck
end Shifted
`);
  assert.equal(formatFormula(kernel.theorems.get("Results.shifted.type")!),
    "∀ k n : ℕ, shifted(k, n) : ℕ");
});

test("a result typed by a carrier, `: R` under CommRing(R) or a structure " +
  "value, states membership and places the value in the ring", () => {
  const { kernel } = load(`module Results
import Grace.Cumulus.Algebra.Polynomial.BundledRoots

section Bundled
variable (R I : Set)
hypothesis comm : CommRing(R)

def sq (a : R) : R := a * a
proof
  sorry

def cube (a : R) : R := sq(a) * a

def unitPoly (a : R) : polynomialRing(R, I) :=
  Ring.one(polynomialRing(R, I))
proof
  sorry

theorem sq.placed (a : R)
  shows sq(a) * sq(a) ∈ R.carrier
proof
  typecheck
end Bundled

theorem sq.outside (R I a : Set)
  requires comm : CommRing(R)
  requires member : a ∈ R.carrier
  shows sq(R, I, a) ∈ R.carrier
proof
  exact sq.type with comm
`);
  assert.equal(formatFormula(kernel.theorems.get("Results.sq.type")!),
    "∀ R I, ∀ a ∈ R.carrier, CommRing(R) → sq(R, I, a) ∈ R.carrier");
  assert.ok(kernel.theorems.has("Results.cube.type"));
  assert.equal(formatFormula(kernel.theorems.get("Results.unitPoly.type")!),
    "∀ R I, ∀ a ∈ R.carrier, CommRing(R) → " +
    "unitPoly(R, I, a) ∈ Ring.carrier(polynomialRing(R, I))");
});

test("an ill-formed or unknown result annotation is rejected with the " +
  "forms a result may take", () => {
  assert.match(
    failure(lists + "\ndef bad {A : Set} (cs : List(A)) : List(A, A) := cs\n"),
    /unknown definition result type List\(A, A\); a result is annotated as/);
  assert.match(failure(lists + "\ndef bad (A x : Set) : A := x\n"),
    /unknown definition result type A; .* a result `: A` needs a hypothesis/);
  assert.match(
    failure(lists +
      "\ndef bad {A : Set} (cs : List(A)) : Set := cs\nproof\n  typecheck\n"),
    /Set is the kernel sort and needs no result-type proof/);
});
