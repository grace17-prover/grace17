// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("single-index maps and canonical finite sums have complete Choice-free audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/FiniteSetSums.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.CoefficientSingle.", "Grace.Cumulus.Algebra.Ring.IndexedSum.", "Grace.Cumulus.Algebra.Ring.FiniteSetSum.", "FiniteSetSums."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  assert.ok(names.length >= 48, `expected the new proofs, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("reindexing does not silently discard repetitions", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.IndexedSum
theorem invalid (A add zero neg mul one w f g : Set, n m : Nat)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires valuesF : WeightedValues(w, f, A, n)
  requires valuesG : WeightedValues(w, g, A, m)
  requires coveredF : ∀ i ∈ n, Occurs(g, m, f(i))
  requires coveredG : ∀ j ∈ m, Occurs(f, n, g(j))
  shows indexedRingSum(w, f, add, zero, n) = indexedRingSum(w, g, add, zero, m)
proof
  exact indexedRingSum.same_entries at A, add, zero, neg, mul, one, w, f, g, n, m with *
` }], ["lib"]), /DistinctValues/);
});

test("canonical finite-sum closure retains the finiteness hypothesis", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.FiniteSetSum
theorem invalid (V A add zero neg mul one w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires weights : FunctionBetween(w, V, A)
  shows finiteRingSum(V, A, add, zero, neg, mul, one, w) ∈ A
proof
  exact finiteRingSum.closed at V, A, add, zero, neg, mul, one, w with *
` }], ["lib"]), /Finite/);
});

test("singleton support equality requires a nonzero coefficient", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.CoefficientSingle
theorem invalid (I A z a j : Set)
  requires zeroIn : z ∈ A
  requires coefficient : a ∈ A
  requires index : j ∈ I
  shows functionSupport(coefficientSingle(I, A, z, a, j), I, z) = {j}
proof
  exact coefficientSingle.support_nonzero at I, A, z, a, j with *
` }], ["lib"]), /a ≠ z|a = z/);
});
