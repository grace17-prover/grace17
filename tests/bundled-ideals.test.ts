// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The ideal theory of bundled rings: under a hypothesis Ring(R) an ideal is
// Ideal(R, I), its elements carry the ring notation, the closure facts are
// instances, quotient rings are quotientRing(R, I), homomorphisms are
// f : R →+* S with the kernel written ker(f) and the induced map
// inducedMap(f), the first isomorphism theorem reads in that notation,
// and the parameterized forms stay reachable through the bridges.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, formulaEquals, loadModuleSourceGraph } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BundledIdeals\nimport Grace.Cumulus.Algebra.Ring\n";

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledIdeals.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledIdeals.g17", source }], ["lib"]);
  return kernel;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name === name)!.statement;

test("Ideal(R, I) reads the operations off the ring hypothesis, and its closure facts are instances", () => {
  const result = check(header + `
section Ideals
variable (R I : Set)
hypothesis ring : Ring(R)
hypothesis ideal : Ideal(R, I)

theorem closure (a : R) (x y : I)
  shows a * x + y - x ∈ I
proof
  typecheck

theorem add_mem (x y : I)
  shows x + y ∈ I
proof
  exact Ideal.add_mem with *

theorem whole_of_one
  requires oneIn : R[1] ∈ I
  shows I = R.carrier
proof
  exact Ideal.contains_one with *
end Ideals
`);
  assert.equal(statement(result, "BundledIdeals.closure"),
    "∀ R I, ∀ (a : R), ∀ (x y : I), Ring(R) → Ideal(R, I) → a * x + y - x ∈ I");
  assert.equal(statement(result, "BundledIdeals.add_mem"), "∀ R I, ∀ (x y : I), Ring(R) → Ideal(R, I) → x + y ∈ I");
});

test("the bundled ideal is the parameterized ideal at the projections, in both directions", () => {
  const kernel = load(header + `
theorem down (R I : Set)
  requires ideal : Ideal(R, I)
  shows IsIdeal(R.carrier, R.add, R.zero, R.neg, R.mul, I)
proof
  exact Ideal.parts with ideal

theorem up (A add zero neg mul one I : Set)
  requires ideal : IsIdeal(A, add, zero, neg, mul, I)
  shows Ideal(Ring.mk(A, add, zero, neg, mul, one), I)
proof
  exact Ideal.of_parts with ideal
`);
  assert.equal(kernel.predicates.get("Grace.Cumulus.Algebra.Ring.Ideal.Ideal"), 2);
  assert.equal(kernel.predicates.get("Grace.Cumulus.Algebra.Ring.IdealCore.IsIdeal"), 6);
  assert.ok(kernel.theorems.has("BundledIdeals.down") && kernel.theorems.has("BundledIdeals.up"));
});

test("quotient rings, homomorphisms, kernels, and the first isomorphism theorem read in the bundled notation", () => {
  const result = check(header + `
section Quotients
variable (R I : Set)
hypothesis comm : CommRing(R)
hypothesis ideal : Ideal(R, I)

theorem quotient
  shows CommRing(R ⧸ I)
proof
  exact quotientRing.comm_ring with *

theorem set_quotient (A r : Set)
  shows (A ⧸ r) = (A ⧸ r) ∧ (R.carrier ⧸ r) = (R.carrier ⧸ r)
proof
  constructor
  . rfl
  . rfl

theorem classes (x y : R)
  shows ⟦x⟧[R.carrier, quotientRelation(R, I)] = ⟦y⟧[R.carrier, quotientRelation(R, I)] ↔ x - y ∈ I
proof
  exact quotientRing.class_eq_iff with *
end Quotients

section Homs
variable (f R S : Set)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : f : R →+* S

theorem kernel
  shows Ideal(R, ker(f))
proof
  exact ringKernel.ideal with *

theorem preserves (x y : R)
  shows f(x * y + R[1]) = f(x) * f(y) + S[1]
proof
  rw [RingHom.map_add, RingHom.map_mul, RingHom.map_one]
  rfl

theorem first_isomorphism
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows inducedMap(f) : R ⧸ ker(f) ≃+* S
proof
  exact RingHom.first_isomorphism with *
end Homs
`);
  assert.equal(statement(result, "BundledIdeals.quotient"), "∀ R, ∀ I, CommRing(R) → Ideal(R, I) → CommRing(R ⧸ I)");
  assert.match(statement(result, "BundledIdeals.set_quotient"), /\(A ⧸ r\) = \(A ⧸ r\) ∧ \(R\.carrier ⧸ r\) = \(R\.carrier ⧸ r\)$/u);
  assert.equal(statement(result, "BundledIdeals.kernel"),
    "∀ f, ∀ R, ∀ S, CommRing(R) → CommRing(S) → RingHom(f, R, S) → Ideal(R, ker(f))");
  assert.equal(statement(result, "BundledIdeals.preserves"),
    "∀ f R S, ∀ (x y : R), CommRing(R) → CommRing(S) → RingHom(f, R, S) → f(x * y + R.one) = f(x) * f(y) + S.one");
  assert.match(statement(result, "BundledIdeals.first_isomorphism"),
    /RingIso\(inducedMap\(f\), R ⧸ ker\(f\), S\)$/u);
  // The spelled forms denote the same terms.
  const spelled = load(header + `
section Homs
variable (f R S : Set)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : f : R →+* S

theorem first_isomorphism
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows quotientMap(f, R.carrier, S.carrier, quotientRelation(R, ringKernel(f, R.carrier, S.zero))) :
    R ⧸ ringKernel(f, R.carrier, S.zero) ≃+* S
proof
  exact RingHom.first_isomorphism with *
end Homs
`);
  const written = load(header + `
section Homs
variable (f R S : Set)
hypothesis source : CommRing(R)
hypothesis target : CommRing(S)
hypothesis hom : f : R →+* S

theorem first_isomorphism
  requires onto : SurjectiveBetween(f, R.carrier, S.carrier)
  shows inducedMap(f) : R ⧸ ker(f) ≃+* S
proof
  exact RingHom.first_isomorphism with *
end Homs
`);
  assert.ok(formulaEquals(spelled.theorems.get("BundledIdeals.first_isomorphism")!, written.theorems.get("BundledIdeals.first_isomorphism")!));
});

test("a structure variable in a kernel or ideal image argument is read as its carrier", () => {
  const kernel = load(header + `
theorem spelled (f R S : Set)
  requires hom : f : R →+* S
  shows ringKernel(f, R, S[0]) ⊆ R ∧ idealComap(f, R, S.carrier) ⊆ R
proof
  constructor
  . exact RingHom.kernel_subset with hom
  . intros x hx
    have data := idealComap.membership.forward with hx
    exact data.left

theorem explicit (f R S : Set)
  requires hom : f : R →+* S
  shows ringKernel(f, R.carrier, S.zero) ⊆ R.carrier ∧ idealComap(f, R.carrier, S.carrier) ⊆ R.carrier
proof
  constructor
  . exact RingHom.kernel_subset with hom
  . intros x hx
    have data := idealComap.membership.forward with hx
    exact data.left
`);
  assert.ok(formulaEquals(kernel.theorems.get("BundledIdeals.spelled")!, kernel.theorems.get("BundledIdeals.explicit")!));
});

test("R ⧸ I is quotientRing(R, I) under a ring or ideal hypothesis and for a closed instance, and quotient(A, r) otherwise", () => {
  const written = load(header + `
theorem under_ring (R I : Set)
  requires ring : Ring(R)
  shows Ring.carrier(R ⧸ I) = (R.carrier ⧸ quotientRelation(R, I))
proof
  exact quotientRing.carrierOf with *

theorem under_ideal (R I A r : Set)
  requires ideal : Ideal(R, I)
  shows Ring.carrier(R ⧸ I) = (R.carrier ⧸ quotientRelation(R, I)) ∧ (A ⧸ r) = (A ⧸ r)
proof
  constructor
  . exact quotientRing.carrierOf with *
  . rfl

theorem plain (R I : Set)
  shows (R ⧸ I) = (R ⧸ I)
proof
  rfl
`);
  const spelled = load(header + `
theorem under_ring (R I : Set)
  requires ring : Ring(R)
  shows Ring.carrier(quotientRing(R, I)) = quotient(R.carrier, quotientRelation(R, I))
proof
  exact quotientRing.carrierOf with *

theorem under_ideal (R I A r : Set)
  requires ideal : Ideal(R, I)
  shows Ring.carrier(quotientRing(R, I)) = quotient(R.carrier, quotientRelation(R, I)) ∧ quotient(A, r) = quotient(A, r)
proof
  constructor
  . exact quotientRing.carrierOf with *
  . rfl

theorem plain (R I : Set)
  shows quotient(R, I) = quotient(R, I)
proof
  rfl
`);
  for (const name of ["under_ring", "under_ideal", "plain"]) {
    assert.ok(formulaEquals(written.theorems.get(`BundledIdeals.${name}`)!, spelled.theorems.get(`BundledIdeals.${name}`)!), name);
  }
  const result = check(header + "import Grace.Cumulus.Int.Ring\n" + `
def integerRing : Set := Ring.mk(ℤ, integerAdd, integerZero, integerNeg, integerMul, integerOne)

instance integerRing.comm_ring
  shows CommRing(integerRing)
proof
  unfold integerRing
  exact CommRing.of_parts with integers.comm_ring

theorem closed (I : Set)
  shows Ring.carrier(integerRing ⧸ I) = (integerRing.carrier ⧸ quotientRelation(integerRing, I))
proof
  exact quotientRing.carrierOf with *
`);
  assert.equal(statement(result, "BundledIdeals.closed"),
    "∀ I, Ring.carrier(integerRing ⧸ I) = (integerRing.carrier ⧸ quotientRelation(integerRing, I))");
});
