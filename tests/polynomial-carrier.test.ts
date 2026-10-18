// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("monomial monoid and polynomial carriers have complete Choice-free audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialStarter.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Polynomial.", "Grace.Cumulus.Algebra.Ring.SumExtension.", "PolynomialStarter."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  assert.ok(names.length >= 58, `expected the new proofs, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("variable faithfulness cannot omit coefficient nontriviality", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial
theorem invalid (I A z unit j k : Set)
  requires zeroIn : z ∈ A
  requires unitIn : unit ∈ A
  requires first : j ∈ I
  requires second : k ∈ I
  requires equal : polynomialVariable(I, A, z, unit, j) = polynomialVariable(I, A, z, unit, k)
  shows j = k
proof
  exact polynomialVariable.injective at I, A, z, unit, j, k with *
` }], ["lib"]), /unit ≠ z|unit = z/);
});

test("the finite-sum insertion formula retains freshness", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.SumExtension
theorem invalid (V A add zero neg mul one w a : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(V)
  requires weights : FunctionBetween(w, insert(a, V), A)
  shows finiteRingSum(insert(a, V), A, add, zero, neg, mul, one, w) = call2(add, finiteRingSum(V, A, add, zero, neg, mul, one, restrict(w, V)), w(a))
proof
  exact finiteRingSum.insert at V, A, add, zero, neg, mul, one, w, a with *
` }], ["lib"]), /a ∉ V/);
});

test("monomial cancellation retains its carrier hypotheses", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.Monomial
theorem invalid (I m n p : Set)
  requires first : m ∈ monomials(I)
  requires second : n ∈ monomials(I)
  requires equal : monomialProduct(I, m, n) = monomialProduct(I, m, p)
  shows n = p
proof
  exact monomialProduct.cancel at I, m, n, p with *
` }], ["lib"]), /p ∈ monomials/);
});
