// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled polynomial rings: under CommRing(R) the value polynomialRing(R, I)
// is a commutative ring by instance, its elements carry the ring notation
// and `ring` once that instance is named, the variables are X(R, I, j) and
// the constants the homomorphism polynomialConstant(R, I), evaluation is
// evaluationHom(R, S, I, f, v) with the universal property in the bundled
// notation, the point ideal pointIdeal(R, I, v) is an ideal of the bundled
// ring and maximal over a field, the one-variable factor theorem and root
// finiteness read over Field(R), and the bridges reach the forms over
// separate pieces in both directions.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BundledPolynomials\nimport Grace.Cumulus.Algebra.Polynomial.BundledIdeals\nimport Grace.Cumulus.Algebra.Polynomial.BundledRoots\nimport Grace.Cumulus.Algebra.Polynomial.BundledNullstellensatz\n";

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledPolynomials.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

// The Nullstellensatz module reaches Zorn's lemma, so a kernel without
// choice loads the ideal layer alone.
const loadHeader = "module BundledPolynomials\nimport Grace.Cumulus.Algebra.Polynomial.BundledIdeals\n";

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledPolynomials.g17", source }], ["lib"]);
  return kernel;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name === name)!.statement;

test("polynomialRing(R, I) is a commutative ring by instance, and its elements carry the ring notation and ring", () => {
  const result = check(header + `
section Polynomials
variable (R I : Set)
hypothesis comm : CommRing(R)

theorem instance_ring
  shows CommRing(polynomialRing(R, I))
proof
  exact polynomialRing.comm_ring with *

theorem swap (p q : Set)
  requires hp : p ∈ Ring.carrier(polynomialRing(R, I))
  requires hq : q ∈ Ring.carrier(polynomialRing(R, I))
  shows Ring.mul(polynomialRing(R, I))(p, q) = Ring.mul(polynomialRing(R, I))(q, p)
proof
  have poly : CommRing(polynomialRing(R, I)) := polynomialRing.comm_ring with *
  have commute : p * q = q * p by ring
  exact commute

theorem generators (j : Set) (a : R)
  shows X(R, I, j) ∈ polynomialRing(R, I) ∧
    polynomialConstant(R, I)(a) ∈ polynomialRing(R, I) ∧
    (polynomialConstant(R, I) : R →+* polynomialRing(R, I))
proof
  refine ⟨?_, ?_, ?_⟩
  . exact X.mem with *
  . exact polynomialConstant.mem with *
  . exact polynomialConstant.hom with *
end Polynomials

section Supplied
variable (R I : Set)
hypothesis comm : CommRing(R)

theorem squares (p q : polynomialRing(R, I))
  shows (p + q) * (p - q) = p * p - q * q
proof
  ring

theorem doubled (p : polynomialRing(R, I))
  shows polynomialRing(R, I)[2] * p = p + p
proof
  ring

theorem placed (p : Set)
  requires hp : p ∈ polynomialRing(R, I)
  shows p * polynomialRing(R, I)[1] = p
proof
  ring
end Supplied
`);
  assert.equal(statement(result, "BundledPolynomials.instance_ring"), "∀ R, ∀ I, CommRing(R) → CommRing(polynomialRing(R, I))");
  // The instance supplies the ring the way a hypothesis does: the carrier
  // binder, the membership, the operations, and the numerals of
  // polynomialRing(R, I) need no hypothesis naming it.
  assert.equal(statement(result, "BundledPolynomials.squares"),
    "∀ R I, ∀ (p q : polynomialRing(R, I)), CommRing(R) → (p + q) * (p - q) = p * p - q * q");
  assert.equal(statement(result, "BundledPolynomials.doubled"),
    "∀ R I, ∀ (p : polynomialRing(R, I)), CommRing(R) → polynomialRing(R, I)[2] * p = p + p");
  assert.match(statement(result, "BundledPolynomials.placed"), /→ p ∈ polynomialRing\(R, I\) → p \* Ring\.one\(polynomialRing\(R, I\)\) = p$/u);
});

test("the bundled ring, its ideals, and its homomorphisms are the engine's forms at the projections, in both directions", () => {
  const kernel = load(loadHeader + `
section Bridges
variable (R S I J g : Set)
hypothesis comm : CommRing(R)
hypothesis target : CommRing(S)

theorem down
  requires ideal : Ideal(polynomialRing(R, I), J)
  requires hom : g : polynomialRing(R, I) →+* S
  shows IsIdeal(polynomials(I, R.carrier, R.zero), polynomialAdd(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      constantFunction(monomials(I), R.carrier, R.zero), polynomialNeg(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      polynomialMul(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one), J) ∧
    IsRingHom(g, polynomials(I, R.carrier, R.zero), polynomialAdd(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      constantFunction(monomials(I), R.carrier, R.zero), polynomialNeg(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      polynomialMul(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one), polynomialConstant(I, R.carrier, R.zero, R.one),
      S.carrier, S.add, S.zero, S.neg, S.mul, S.one)
proof
  constructor
  . exact Ideal.polynomial_parts with *
  . exact RingHom.polynomial_parts with *

theorem up
  requires ideal : IsIdeal(polynomials(I, R.carrier, R.zero), polynomialAdd(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      constantFunction(monomials(I), R.carrier, R.zero), polynomialNeg(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one),
      polynomialMul(I, R.carrier, R.add, R.zero, R.neg, R.mul, R.one), J)
  shows Ideal(polynomialRing(R, I), J)
proof
  exact Ideal.polynomial_of_parts with *
end Bridges
`);
  assert.equal(kernel.functions.get("Grace.Cumulus.Algebra.Polynomial.Bundled.polynomialRing"), 2);
  assert.equal(kernel.functions.get("Grace.Cumulus.Algebra.Polynomial.Bundled.polynomialConstant"), 2);
  assert.equal(kernel.functions.get("Grace.Cumulus.Algebra.Polynomial.polynomialConstant"), 4);
  assert.equal(kernel.functions.get("Grace.Cumulus.Algebra.Polynomial.BundledIdeals.pointIdeal"), 3);
  assert.equal(kernel.functions.get("Grace.Cumulus.Algebra.Polynomial.PointIdeal.pointIdeal"), 8);
  assert.ok(kernel.theorems.has("BundledPolynomials.down") && kernel.theorems.has("BundledPolynomials.up"));
});

test("evaluation through a coefficient homomorphism has the universal property in the bundled notation", () => {
  const result = check(header + `
section Evaluation
variable (R S I f v : Set)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : f : R →+* S
hypothesis assignment : v : I → S.carrier

theorem values (j : Set) (a : R)
  requires index : j ∈ I
  shows (evaluationHom(R, S, I, f, v) : polynomialRing(R, I) →+* S) ∧
    evaluationHom(R, S, I, f, v)(X(R, I, j)) = v(j) ∧
    evaluationHom(R, S, I, f, v)(polynomialConstant(R, I)(a)) = f(a)
proof
  refine ⟨?_, ?_, ?_⟩
  . exact evaluationHom.hom with *
  . exact evaluationHom.map_X with *
  . exact evaluationHom.map_constant with *

theorem unique (g : Set)
  requires candidate : g : polynomialRing(R, I) →+* S
  requires constants : ∀ a ∈ R, g(polynomialConstant(R, I)(a)) = f(a)
  requires variables : ∀ j ∈ I, g(X(R, I, j)) = v(j)
  shows g = evaluationHom(R, S, I, f, v)
proof
  exact evaluationHom.unique with *
end Evaluation

section Points
variable (R I v : Set)
hypothesis comm : CommRing(R)
hypothesis assignment : v : I → R.carrier

theorem at_point (j : Set) (a : R)
  requires index : j ∈ I
  shows (evaluationAt(R, I, v) : polynomialRing(R, I) →+* R) ∧
    evaluationAt(R, I, v)(X(R, I, j)) = v(j) ∧
    evaluationAt(R, I, v)(polynomialConstant(R, I)(a)) = a ∧
    evaluationAt(R, I, v) = evaluationHom(R, R, I, identity(R.carrier), v)
proof
  refine ⟨?_, ?_, ?_, ?_⟩
  . exact evaluationAt.hom with *
  . exact evaluationAt.map_X with *
  . exact evaluationAt.map_constant with *
  . exact evaluationAt.eq_evaluationHom with *
end Points
`);
  assert.equal(statement(result, "BundledPolynomials.unique"),
    "∀ R, ∀ S, ∀ I, ∀ f, ∀ v, ∀ g, CommRing(R) → CommRing(S) → RingHom(f, R, S) → FunctionBetween(v, I, S.carrier) → " +
    "RingHom(g, polynomialRing(R, I), S) → (∀ a ∈ R.carrier, g(polynomialConstant(R, I)(a)) = f(a)) → " +
    "(∀ j ∈ I, g(X(R, I, j)) = vⱼ) → g = evaluationHom(R, S, I, f, v)");
  assert.match(statement(result, "BundledPolynomials.values"), /^∀ R S I f v j, ∀ \(a : R\), /u);
});

test("point ideals are ideals of the bundled ring, maximal over a field, and the factor theorem, root finiteness, and the Nullstellensatz read over Field(R)", () => {
  const result = check(header + `
section Points
variable (R I v : Set)
hypothesis comm : CommRing(R)
hypothesis assignment : v : I → R.carrier

theorem ideal (p : Set)
  shows Ideal(polynomialRing(R, I), pointIdeal(R, I, v)) ∧
    (p ∈ pointIdeal(R, I, v) ↔ p ∈ Ring.carrier(polynomialRing(R, I)) ∧ evaluationAt(R, I, v)(p) = R[0])
proof
  constructor
  . exact Ideal.point with *
  . exact pointIdeal.mem_iff with *
end Points

section Fields
variable (R I v leading : Set)
hypothesis field : Field(R)
hypothesis assignment : v : I → R.carrier
hypothesis initial : leading ∈ R
hypothesis nonzero : leading ≠ R[0]

theorem maximal
  shows MaximalIdeal(polynomialRing(R, I), pointIdeal(R, I, v))
proof
  exact MaximalIdeal.point with *

theorem factor (a x c : R) (cs : List(R.carrier))
  requires root : horner(R, leading, a, c :: cs) = R[0]
  shows horner(R, leading, x, c :: cs) =
    (x - a) * horner(R, leading, x, syntheticQuotient(R, leading, a, cs))
proof
  have comm := Field.to_comm_ring with field
  exact horner.factor with *

theorem finite_roots (cs : List(R.carrier))
  shows Finite(rootSet(R, leading, cs))
proof
  exact rootSet.finite with *
end Fields

section Closed
variable (R I G : Set)
hypothesis closed : AlgebraicallyClosed(R)
hypothesis finite : Finite(I)
hypothesis generators : G ⊆ polynomialRing(R, I)

theorem nullstellensatz
  shows Ring.one(polynomialRing(R, I)) ∈ generatedIdeal(polynomialRing(R, I), G) ↔
    ¬(∃ v, (v : I → R.carrier) ∧ (∀ p ∈ G, evaluationAt(R, I, v)(p) = R[0]))
proof
  exact polynomialRing.unit_iff_no_common_zero with *
end Closed
`);
  assert.equal(statement(result, "BundledPolynomials.maximal"),
    "∀ R, ∀ I, ∀ v, ∀ leading, Field(R) → FunctionBetween(v, I, R.carrier) → leading ∈ R → leading ≠ R.zero → MaximalIdeal(polynomialRing(R, I), pointIdeal(R, I, v))");
  assert.match(statement(result, "BundledPolynomials.factor"),
    /horner\(R, leading, a, c :: cs\) = R\.zero → horner\(R, leading, x, c :: cs\) = \(x - a\) \* horner\(R, leading, x, syntheticQuotient\(R, leading, a, cs\)\)$/u);
  assert.match(statement(result, "BundledPolynomials.finite_roots"), /→ Finite\(rootSet\(R, leading, cs\)\)$/u);
  assert.match(statement(result, "BundledPolynomials.nullstellensatz"),
    /AlgebraicallyClosed\(R\) → Finite\(I\) → G ⊆ polynomialRing\(R, I\) → \(Ring\.one\(polynomialRing\(R, I\)\) ∈ generatedIdeal\(polynomialRing\(R, I\), G\) ↔ ¬\(∃ \(v : I → R\.carrier\), ∀ p ∈ G, evaluationAt\(R, I, v\)\(p\) = R\.zero\)\)$/u);
});

test("the example file checks, with ring arithmetic on polynomials and evaluation through the homomorphism laws", () => {
  const result = check(readFileSync("examples/BundledPolynomials.g17", "utf8"));
  assert.match(statement(result, "BundledPolynomials.difference_of_squares"), /\(p \+ q\) \* \(p - q\) = p \* p - q \* q$/u);
  assert.match(statement(result, "BundledPolynomials.evaluate_square_plus"), /= vⱼ \* vⱼ \+ a$/u);
});
