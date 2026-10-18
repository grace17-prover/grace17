// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("grouped-map composition and both convolution distributive laws have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/ConvolutionDistributivity.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Ring.PushforwardComposition.", "Grace.Cumulus.Algebra.Polynomial.ConvolutionBounds.", "Grace.Cumulus.Algebra.Polynomial.Distributivity.", "ConvolutionDistributivity."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  names.push("Grace.Cumulus.Algebra.CoefficientSingle.singleValue.zero", "Grace.Cumulus.Algebra.CoefficientSingle.singleValue.iterated", "Grace.Cumulus.Algebra.Ring.SumSupport.finiteRingSum.select");
  assert.ok(names.length >= 23, `expected new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.Distributivity
${source}` }], ["lib"]), pattern);
}

test("two-stage grouping retains finiteness of the intermediate sum domain", () => {
  rejects(`theorem invalid (D C B A add zero neg mul one h k w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finiteD : Finite(D)
  requires weights : FunctionBetween(w, D, A)
  requires firstMap : FunctionBetween(h, D, C)
  requires secondMap : FunctionBetween(k, C, B)
  shows finitePushforward(C, B, A, add, zero, neg, mul, one, k, finitePushforward(D, C, A, add, zero, neg, mul, one, h, w)) = finitePushforward(D, B, A, add, zero, neg, mul, one, compose(k, h, D, C, B), w)
proof
  exact finitePushforward.compose at D, C, B, A, add, zero, neg, mul, one, h, k, w with *
`, /Finite\(C\)/);
});

test("a common convolution domain must include all support pairs", () => {
  rejects(`theorem invalid (I D A add zero neg mul one p q : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  requires memberQ : q ∈ polynomials(I, A, zero)
  requires domain : D ⊆ monomials(I) × monomials(I)
  requires finite : Finite(D)
  shows finitePushforward(D, monomials(I), A, add, zero, neg, mul, one, monomialMul(I), boundedConvolutionWeights(I, D, A, add, zero, neg, mul, one, p, q)) = polynomialProduct(I, A, add, zero, neg, mul, one, p, q)
proof
  exact polynomialProduct.on_domain at I, D, A, add, zero, neg, mul, one, p, q with *
`, /convolutionPairs.*⊆ D/);
});

test("distributivity retains the third polynomial's carrier hypothesis", () => {
  rejects(`theorem invalid (I A add zero neg mul one p q r : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  requires memberQ : q ∈ polynomials(I, A, zero)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, p, coefficientAdd(monomials(I), A, add, zero, neg, mul, one, q, r)) = coefficientAdd(monomials(I), A, add, zero, neg, mul, one, polynomialProduct(I, A, add, zero, neg, mul, one, p, q), polynomialProduct(I, A, add, zero, neg, mul, one, p, r))
proof
  exact polynomialProduct.add_right at I, A, add, zero, neg, mul, one, p, q, r with *
`, /r ∈ polynomials/);
});
