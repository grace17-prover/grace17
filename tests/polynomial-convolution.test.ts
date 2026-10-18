// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("finite convolution, grouped-sum linearity, and ideal absorption have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialConvolution.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Cardinal.FiniteImage.", "Grace.Cumulus.Algebra.Ring.Pushforward.", "Grace.Cumulus.Algebra.Polynomial.Convolution.", "Grace.Cumulus.Algebra.Polynomial.IdealSupport.", "PolynomialConvolution."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  assert.ok(names.length >= 41, `expected all new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.IdealSupport
${source}` }], ["lib"]), pattern);
}

test("convolution closure requires both polynomial inputs", () => {
  rejects(`theorem invalid (I A add zero neg mul one p q : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, p, q) ∈ polynomials(I, A, zero)
proof
  exact polynomialProduct.member at I, A, add, zero, neg, mul, one, p, q with *
`, /q ∈ polynomials/);
});

test("finite pushforward closure cannot omit a finite summation domain", () => {
  rejects(`theorem invalid (D C A add zero neg mul one h w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires weights : FunctionBetween(w, D, A)
  shows FunctionBetween(finitePushforward(D, C, A, add, zero, neg, mul, one, h, w), C, A)
proof
  exact finitePushforward.function at D, C, A, add, zero, neg, mul, one, h, w with *
`, /Finite/);
});

test("polynomial support absorption retains the monomial ideal condition", () => {
  rejects(`theorem invalid (I A add zero neg mul one U p q : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ monomialIdealPolynomials(I, A, zero, U)
  requires memberQ : q ∈ polynomials(I, A, zero)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, p, q) ∈ monomialIdealPolynomials(I, A, zero, U)
proof
  exact monomialIdealPolynomials.mul_right at I, A, add, zero, neg, mul, one, U, p, q with *
`, /MonomialIdeal/);
});

test("the finite-image theorem retains finiteness of its source", () => {
  rejects(`theorem invalid (D C f S : Set)
  requires function : FunctionBetween(f, D, C)
  requires subset : S ⊆ D
  shows Finite(functionImage(f, S, C))
proof
  exact Finite.function_image at D, C, f, S with *
`, /Finite/);
});
