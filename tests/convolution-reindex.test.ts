// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("zero-extension, reindexing, and convolution commutativity have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/ConvolutionReindex.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Ring.SumSupport.", "Grace.Cumulus.Algebra.Ring.PushforwardTransport.", "Grace.Cumulus.Algebra.Polynomial.ConvolutionLaws.", "Grace.Cumulus.Cardinal.Product.swappedPair.", "Grace.Cumulus.Cardinal.Product.productSwap.", "ConvolutionReindex."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  assert.ok(names.length >= 24, `expected new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.ConvolutionLaws
${source}` }], ["lib"]), pattern);
}

test("zero-extension cannot discard arbitrary nonzero summands", () => {
  rejects(`theorem invalid (D S A add zero neg mul one w v : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(D)
  requires weightsW : FunctionBetween(w, D, A)
  requires weightsV : FunctionBetween(v, S, A)
  requires subset : S ⊆ D
  requires agreement : ∀ s ∈ S, w(s) = v(s)
  shows finiteRingSum(D, A, add, zero, neg, mul, one, w) = finiteRingSum(S, A, add, zero, neg, mul, one, v)
proof
  exact finiteRingSum.zero_extension at D, S, A, add, zero, neg, mul, one, w, v with *
`, /w\(.*\) = zero/);
});

test("finite-sum reindexing requires bijectivity, not merely a function", () => {
  rejects(`theorem invalid (D E A add zero neg mul one w v f : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(D)
  requires weightsW : FunctionBetween(w, D, A)
  requires weightsV : FunctionBetween(v, E, A)
  requires function : FunctionBetween(f, D, E)
  requires values : ∀ d ∈ D, w(d) = v(f(d))
  shows finiteRingSum(D, A, add, zero, neg, mul, one, w) = finiteRingSum(E, A, add, zero, neg, mul, one, v)
proof
  exact finiteRingSum.reindex at D, E, A, add, zero, neg, mul, one, w, v, f with *
`, /BijectiveBetween/);
});

test("grouped reindexing retains the output-index agreement", () => {
  rejects(`theorem invalid (D E C A add zero neg mul one h k w v f : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(D)
  requires weightsW : FunctionBetween(w, D, A)
  requires weightsV : FunctionBetween(v, E, A)
  requires bijective : BijectiveBetween(f, D, E)
  requires weights : ∀ d ∈ D, w(d) = v(f(d))
  shows finitePushforward(D, C, A, add, zero, neg, mul, one, h, w) = finitePushforward(E, C, A, add, zero, neg, mul, one, k, v)
proof
  exact finitePushforward.reindex at D, E, C, A, add, zero, neg, mul, one, h, k, w, v, f with *
`, /h\(.*\) = k/);
});

test("convolution commutativity retains coefficient-ring commutativity", () => {
  rejects(`theorem invalid (I A add zero neg mul one p q : Set)
  requires ring : IsRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  requires memberQ : q ∈ polynomials(I, A, zero)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, p, q) = polynomialProduct(I, A, add, zero, neg, mul, one, q, p)
proof
  exact polynomialProduct.commutative at I, A, add, zero, neg, mul, one, p, q with *
`, /CommRing/);
});
