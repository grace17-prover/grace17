// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.PointIdeal
${source}` }], ["lib"]), pattern);
}

test("point ideals, residue rings, and generic maximal kernels have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialPoints.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n => /^(Grace.Cumulus.Algebra.Field.Homomorphism\.|Grace.Cumulus.Algebra.Polynomial.PointIdeal\.|PolynomialPoints\.)/.test(n));
  assert.ok(names.length >= 19, `expected every new boundary, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("a homomorphism to a field needs surjectivity for the maximal-kernel theorem", () => {
  rejects(`theorem invalid (f A add zero neg mul one B plus z minus times unit : Set)
  requires source : IsCommRing(A, add, zero, neg, mul, one)
  requires field : IsField(B, plus, z, minus, times, unit)
  requires hom : IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)
  shows IsMaximalIdeal(A, add, zero, neg, mul, one, ringKernel(f, A, z))
proof
  exact IsRingHom.kernel_maximal at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit with *
`, /SurjectiveBetween/);
});

test("point maximality retains the field hypothesis", () => {
  rejects(`theorem invalid (I A add zero neg mul one v : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires assignment : FunctionBetween(v, I, A)
  shows IsMaximalIdeal(polynomials(I, A, zero), polynomialAdd(I, A, add, zero, neg, mul, one), constantFunction(monomials(I), A, zero), polynomialNeg(I, A, add, zero, neg, mul, one), polynomialMul(I, A, add, zero, neg, mul, one), polynomialConstant(I, A, zero, one), pointIdeal(I, A, add, zero, neg, mul, one, v))
proof
  exact pointIdeal.maximal at I, A, add, zero, neg, mul, one, v with *
`, /IsField/);
});

test("coordinate recovery requires the coordinate to belong to the variable set", () => {
  rejects(`theorem invalid (I A add zero neg mul one v j a : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires assignment : FunctionBetween(v, I, A)
  requires coefficient : a ∈ A
  shows polynomialCoordinateDifference(I, A, add, zero, neg, mul, one, j, a) ∈ pointIdeal(I, A, add, zero, neg, mul, one, v) ↔ v(j) = a
proof
  exact pointIdeal.coordinate_difference at I, A, add, zero, neg, mul, one, v, j, a with *
`, /j ∈ I/);
});

test("point ideal separation requires both inputs to be assignments", () => {
  rejects(`theorem invalid (I A add zero neg mul one v w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires assignment : FunctionBetween(v, I, A)
  shows pointIdeal(I, A, add, zero, neg, mul, one, v) = pointIdeal(I, A, add, zero, neg, mul, one, w) ↔ v = w
proof
  exact pointIdeal.eq_iff at I, A, add, zero, neg, mul, one, v, w with *
`, /FunctionBetween\(w, I, A\)/);
});
