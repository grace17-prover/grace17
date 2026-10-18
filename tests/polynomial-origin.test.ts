// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("coefficient embedding, origin evaluation, and its quotient have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialOrigin.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Polynomial.Constants.",
    "Grace.Cumulus.Algebra.Polynomial.Origin.", "PolynomialOrigin."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  names.push("Grace.Cumulus.Algebra.Ring.PushforwardTransport.finitePushforward.unique_fiber");
  assert.ok(names.length >= 32, `expected all new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.Origin
${source}` }], ["lib"]), pattern);
}

test("embedding requires the designated zero to belong to the coefficient carrier", () => {
  rejects(`theorem invalid (I A zero a : Set)
  requires coefficient : a ∈ A
  shows polynomialAtOrigin(I, A, zero)(polynomialCoefficients(I, A, zero)(a)) = a
proof
  exact polynomialAtOrigin.coefficients at I, A, zero, a with *
`, /zero ∈ A/);
});

test("a variable evaluates to zero only when its index belongs to the variable set", () => {
  rejects(`theorem invalid (I A zero one j : Set)
  requires zeroIn : zero ∈ A
  requires oneIn : one ∈ A
  shows polynomialAtOrigin(I, A, zero)(polynomialVariable(I, A, zero, one, j)) = zero
proof
  exact polynomialAtOrigin.variable at I, A, zero, one, j with *
`, /j ∈ I/);
});

test("constant-coefficient multiplication retains finite-support membership", () => {
  rejects(`theorem invalid (I A add zero neg mul one p q : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  requires functionQ : FunctionBetween(q, monomials(I), A)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, p, q)(monomialOne(I)) = call2(mul, p(monomialOne(I)), q(monomialOne(I)))
proof
  exact polynomialProduct.constant_coefficient at I, A, add, zero, neg, mul, one, p, q with *
`, /q ∈ polynomials/);
});

test("isolating a convolution contribution requires uniqueness of the fiber", () => {
  rejects(`theorem invalid (D C A add zero neg mul one h w d c : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(D)
  requires weights : FunctionBetween(w, D, A)
  requires source : d ∈ D
  requires target : c ∈ C
  requires image : h(d) = c
  shows finitePushforward(D, C, A, add, zero, neg, mul, one, h, w)(c) = w(d)
proof
  exact finitePushforward.unique_fiber at D, C, A, add, zero, neg, mul, one, h, w, d, c with *
`, /h\(e\).*c|∀ e/);
});
