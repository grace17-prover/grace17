// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.Assignment
${source}` }], ["lib"]), pattern);
}

test("finite products, arbitrary assignments, and common-zero certificates have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialAssignments.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n => /^(Grace.Cumulus.Algebra.Ring.FiniteProduct\.|Grace.Cumulus.Algebra.Polynomial.Assignment\.|PolynomialAssignments\.)/.test(n));
  assert.ok(names.length >= 57, `expected all new boundaries, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("evaluation requires an assignment defined on the full variable set", () => {
  rejects(`theorem invalid (I J A add zero neg mul one v : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires partial : FunctionBetween(v, J, A)
  shows MonomialCharacter(I, A, mul, one, monomialEvaluate(I, A, add, zero, neg, mul, one, v))
proof
  exact monomialEvaluate.character at I, A, add, zero, neg, mul, one, v with *
`, /FunctionBetween\(v, I, A\)/);
});

test("variable evaluation retains its index membership hypothesis", () => {
  rejects(`theorem invalid (I A add zero neg mul one v j : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires assignment : FunctionBetween(v, I, A)
  shows polynomialAt(I, A, add, zero, neg, mul, one, v)(polynomialVariable(I, A, zero, one, j)) = v(j)
proof
  exact polynomialAt.variable at I, A, add, zero, neg, mul, one, v, j with *
`, /j ∈ I/);
});

test("unit certificates require a nontrivial target ring to rule out common zeros", () => {
  rejects(`theorem invalid (I A add zero neg mul one G : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires generators : G ⊆ polynomials(I, A, zero)
  requires certificate : polynomialConstant(I, A, zero, one) ∈ idealSpan(polynomials(I, A, zero), polynomialAdd(I, A, add, zero, neg, mul, one), constantFunction(monomials(I), A, zero), polynomialNeg(I, A, add, zero, neg, mul, one), polynomialMul(I, A, add, zero, neg, mul, one), G)
  shows ¬(∃ v, PolynomialCommonZero(I, A, add, zero, neg, mul, one, G, v))
proof
  exact polynomialIdeal.no_common_zero at I, A, add, zero, neg, mul, one, G with *
`, /Nontrivial/);
});

test("finite products cannot discard nonunit factors", () => {
  rejects(`theorem invalid (D S A add zero neg mul one w v : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(D)
  requires weightsW : FunctionBetween(w, D, A)
  requires weightsV : FunctionBetween(v, S, A)
  requires subset : S ⊆ D
  requires agreement : ∀ s ∈ S, w(s) = v(s)
  shows finiteRingProduct(D, A, add, zero, neg, mul, one, w) = finiteRingProduct(S, A, add, zero, neg, mul, one, v)
proof
  exact finiteRingProduct.unit_extension at D, S, A, add, zero, neg, mul, one, w, v with *
`, /w\(d\) = one/);
});
