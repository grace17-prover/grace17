// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { canonical, createZfgKernel, loadModuleSourceGraph } from "../src/index.ts";

// Placing operands in rings: an application no ring in scope can place is
// an error rather than a natural-number reading, an operand the typing
// rules place keeps the ring, and the natural readings stay natural.
test("an operand no ring in scope places is an error naming the missing premise", () => {
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "Placement.g17", source: `module Placement
import Grace.Cumulus.Algebra.Polynomial.Bundled
import Grace.Cumulus.Algebra.Ring.Pow

section Relations
variable (K : Set)
hypothesis polynomials : CommRing(polynomialRing(K, 4))

def relCusp : Set := X(K, 4, 1)^2 + X(K, 4, 2)^3 - X(K, 4, 3)*X(K, 4, 0)

end Relations
` }], ["lib"]), /cannot place X\(K, 4, 1\) for \^.*polynomialRing\(K, 4\).*by X\.mem needs CommRing\(K\)/);
});

test("an operand the typing rules place in an instance-supplied ring keeps that ring", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Placement.g17", source: `module Placement
import Grace.Cumulus.Algebra.Polynomial.Bundled
import Grace.Cumulus.Algebra.Ring.Pow

section Values
variable (B x y : Set)
hypothesis base : CommRing(B)
hypothesis xIn : x ∈ B
hypothesis yIn : y ∈ B

theorem cusp
  shows polynomialConstant(B, 1)(x)^2 + polynomialConstant(B, 1)(y)^3 =
    polynomialConstant(B, 1)(y)^3 + polynomialConstant(B, 1)(x)^2
proof
  have polynomials := polynomialRing.comm_ring at B, 1 with base
  ring

end Values
` }], ["lib"]);
  const statement = canonical(kernel.theorems.get("Placement.cusp")!);
  assert.match(statement, /Ring\.Pow\.Ring\.pow"/);
  assert.match(statement, /Ring\.Basic\.Ring\.add"/);
  assert.doesNotMatch(statement, /Nat\.Pow\.pow"|Nat\.Rec\.add"/);
});

test("natural operands by binder, fact, and ring members keep their readings", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Placement.g17", source: `module Placement
import Grace.Cumulus.Algebra.Polynomial.Bundled
import Grace.Cumulus.Algebra.Ring.Pow

section Controls
variable (K : Set, n : Nat)
hypothesis base : CommRing(K)

theorem nat_binder
  shows n^2 + 1 = n^2 + 1
proof
  rfl

theorem nat_fact (m : Set)
  requires natural : Nat(m)
  shows m^2 * 2 = m^2 * 2
proof
  rfl

theorem ring_power (a : K)
  shows a^2 * a = a^2 * a
proof
  rfl

end Controls
` }], ["lib"]);
  assert.match(canonical(kernel.theorems.get("Placement.nat_binder")!), /Nat\.Pow\.pow"/);
  assert.match(canonical(kernel.theorems.get("Placement.nat_fact")!), /Nat\.Rec\.mul"/);
  assert.match(canonical(kernel.theorems.get("Placement.ring_power")!), /Ring\.Pow\.Ring\.pow"/);
});

// A binder bounded by a ring value reads the carrier whenever a ring fact
// about the value is in scope: by closed instance, hypothesis, instance,
// or a local fact of the proof.
test("a binder bounded by a ring value reads its carrier", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Carrier.g17", source: `module Carrier
import Grace.Cumulus.Algebra.Algebras
import Grace.Cumulus.Complex.Field

theorem complex
  shows ∀ a ∈ complexRing, a ∈ Ring.carrier(complexRing)
proof
  intros a aIn
  exact aIn

section ByHypothesis
variable (A : Set)
hypothesis ring : CommRing(Algebra.ring(A))

theorem projection
  shows ∀ a ∈ Algebra.ring(A), a ∈ Ring.carrier(Algebra.ring(A))
proof
  intros a aIn
  exact aIn

end ByHypothesis

section ByInstance
variable (A : Set)
hypothesis algebra : Algebra(A)

theorem projection_instance
  shows ∀ a ∈ Algebra.ring(A), a ∈ Ring.carrier(Algebra.ring(A))
proof
  intros a aIn
  exact aIn

end ByInstance

def baseRing : Set := complexRing

theorem local_fact
  shows ∀ b ∈ Ring.carrier(baseRing), b ∈ Ring.carrier(baseRing)
proof
  have ring : CommRing(baseRing) by unfold baseRing; exact complexRing.comm_ring
  have inner : ∀ b ∈ baseRing, b ∈ Ring.carrier(baseRing)
    intros b bIn
    exact bIn
  exact inner

theorem plain_set (S : Set)
  shows ∀ a ∈ S, a ∈ S
proof
  intros a aIn
  exact aIn
` }], ["lib"]);
  const carrier = /complexRing","tag":"app"\}\],"fn":"Grace\.Cumulus\.Algebra\.Ring\.Basic\.Ring\.carrier"/;
  assert.match(canonical(kernel.theorems.get("Carrier.complex")!), carrier);
  assert.match(canonical(kernel.theorems.get("Carrier.projection_instance")!), /Algebra\.ring","tag":"app"\}\],"fn":"Grace\.Cumulus\.Algebra\.Ring\.Basic\.Ring\.carrier"/);
  assert.doesNotMatch(canonical(kernel.theorems.get("Carrier.plain_set")!), /Ring\.carrier/);
});

// The arrow guard reads a ring value as its carrier under the same
// conditions, since the definition of FunctionBetween uses its last two
// parameters as sets of elements.
test("the arrow guard reads a ring value as its carrier", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Arrow.g17", source: `module Arrow
import Grace.Cumulus.Algebra.Polynomial.Bundled

section Arrow
variable (R I f : Set)
hypothesis base : CommRing(R)
hypothesis function : f : polynomialRing(R, I) → polynomialRing(R, I)

theorem closed (p : Set)
  requires pIn : p ∈ polynomialRing(R, I)
  shows f(p) ∈ polynomialRing(R, I)
proof
  exact FunctionBetween.apply_closed with function, pIn

end Arrow
` }], ["lib"]);
  const guard = canonical(kernel.theorems.get("Arrow.closed")!);
  assert.match(guard, /polynomialRing","tag":"app"\}\],"fn":"Grace\.Cumulus\.Algebra\.Ring\.Basic\.Ring\.carrier","tag":"app"\},\{"args":\[\{"args":\[\{"name":"R","tag":"var"\},\{"name":"I","tag":"var"\}\],"fn":"[^"]*polynomialRing","tag":"app"\}\],"fn":"Grace\.Cumulus\.Algebra\.Ring\.Basic\.Ring\.carrier","tag":"app"\}\],"pred":"[^"]*FunctionBetween"/);
});

// The numeral notation R[n] accepts a projection as the ring when a
// hypothesis or an instance places a ring structure on it.
test("R[n] on a projection placed in a ring by hypothesis or instance", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Numeral.g17", source: `module Numeral
import Grace.Cumulus.Algebra.Algebras
import Grace.Cumulus.Algebra.Polynomial.Algebra

section Numeral
variable (A K : Set)
hypothesis algebra : Algebra(A)
hypothesis base : CommRing(K)
hypothesis compound : CommRing(Algebra.ring(polynomialAlgebra(K, 2)))

theorem two
  shows Algebra.ring(A)[2] = Algebra.ring(A)[1] + Algebra.ring(A)[1]
proof
  have ring := Algebra.comm_ring with algebra
  ring

theorem two_compound
  shows Algebra.ring(polynomialAlgebra(K, 2))[2] =
    Algebra.ring(polynomialAlgebra(K, 2))[1] + Algebra.ring(polynomialAlgebra(K, 2))[1]
proof
  ring

end Numeral
` }], ["lib"]);
  assert.match(canonical(kernel.theorems.get("Numeral.two")!), /Ring\.Numeral\.ringNat"/);
  assert.match(canonical(kernel.theorems.get("Numeral.two_compound")!), /Ring\.Numeral\.ringNat"/);
});

// A literal filling a parameter declared Nat stays natural inside a ring
// scope, while the ring's own numerals keep reading as the ring numerals.
test("a literal in a Nat parameter stays natural inside a ring scope", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Literal.g17", source: `module Literal
import Grace.Cumulus.Real.Metric

section Literal
notation ring R := (ℝ, realAdd, realZero, realNeg, realMul, realOne)

def two : Set := realNumeral(2)

theorem literal
  shows two = realNat(2)
proof
  simp [two, realNumeral]

theorem ring_literal (x : Real)
  shows x * 2 = x + x
proof
  ring

end Literal
` }], ["lib"]);
  assert.match(canonical(kernel.definitions.get("Literal.two")!.properties.get("equation")!),
    /\{"tag":"nat","value":"2"\}\],"fn":"Grace\.Cumulus\.Real\.Natural\.realNumeral"/);
  assert.match(canonical(kernel.theorems.get("Literal.ring_literal")!),
    /realMul","tag":"app"\},\{"name":"x","tag":"var"\},\{"args":\[\{"tag":"nat","value":"2"\}\],"fn":"Grace\.Cumulus\.Real\.Natural\.realNumeral"/);
});

// Among equal rings spelled apart, a membership fact whose container is a
// definition unfolding to one candidate's carrier selects it; with no
// evidence the error lists the candidates.
test("a membership fact through a definition selects among equal rings spelled apart", () => {
  const header = `module Equal
import Grace.Cumulus.Algebra.Polynomial.Algebra
import Grace.Cumulus.Algebra.Ring.Pow

section Ambiguous
variable (K p q : Set)
hypothesis base : CommRing(K)
hypothesis polynomials : CommRing(polynomialRing(K, 2))
hypothesis algebraRing : CommRing(Algebra.ring(polynomialAlgebra(K, 2)))
hypothesis pIn : p ∈ algebraCarrier(polynomialAlgebra(K, 2))
`;
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Equal.g17", source: header + `
theorem square
  shows p^2 = p * p
proof
  sorry

end Ambiguous
` }], ["lib"]);
  assert.match(canonical(kernel.theorems.get("Equal.square")!),
    /polynomialAlgebra","tag":"app"\}\],"fn":"[^"]*Algebra\.ring","tag":"app"\},\{"name":"p","tag":"var"\},\{"tag":"nat","value":"2"\}\],"fn":"[^"]*Ring\.pow"/);
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "Equal.g17", source: header + `
theorem none
  shows q^2 = q * q
proof
  sorry

end Ambiguous
` }], ["lib"]), /ambiguous notation.*polynomialRing\(K, 2\).*Algebra\.ring\(polynomialAlgebra\(K, 2\)\)/);
});
