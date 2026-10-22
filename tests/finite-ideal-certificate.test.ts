// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

test("arbitrary finite sums and generated-ideal certificates are public and choice-free", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/FiniteIdealCertificate.g17"], ["lib"]);
  const names = [
    ...["ringScale.closed", "ringSum.nil", "ringSum.cons", "IsIdeal.sum_mem", "ringSum.closed", "ringSum.append", "ringSum.scale", "IsRingHom.sum"]
      .map(n => `Grace.Cumulus.Algebra.Ring.FiniteSum.${n}`),
    ...["idealProducts.subset", "idealProducts.scale",
      "idealProducts.contains", "finiteIdealSums.zero", "finiteIdealSums.contains", "finiteIdealSums.add", "finiteIdealSums.scale",
      "finiteIdealSums.ideal", "idealProducts.subset_span", "idealSpan.eq_finite_sums", "idealSpan.finite_certificate",
      "idealSpan.unit_iff_finite_certificate", "idealSpan.finite_certificate_obstructs_vanishing"]
      .map(n => `Grace.Cumulus.Algebra.Ring.FiniteCombination.${n}`),
    "FiniteIdealCertificate.finite_witness", "FiniteIdealCertificate.no_common_zero",
  ];
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("finite sums require each summand to belong to the ideal", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring
theorem invalid (A add zero neg mul I C : Set) (xs : List(C))
  requires ideal : IsIdeal(A, add, zero, neg, mul, I)
  shows ringSum{C}(add, zero, xs) ∈ I
proof
  exact IsIdeal.sum_mem at A, add, zero, neg, mul, I, C, xs with *
` }], ["lib"]), /Subset|⊆/);
});

test("nested carrier binders accept whitespace without changing their kernel meaning", () => {
  const source = `module Nested
import Grace.Cumulus.Algebra.Ring
theorem nested (A mul G : Set) (xs : List(idealProducts(A, mul, G)))
  shows xs = xs
proof
  rfl
`;
  const a = createZfKernel();
  const b = createZfKernel();
  loadModuleSourceGraph(a, [{ file: "Nested.g17", source }], ["lib"]);
  loadModuleSourceGraph(b, [{ file: "Nested.g17", source: source.replace("idealProducts(A, mul, G)", "idealProducts(A,mul,G)") }], ["lib"]);
  assert.ok(formulaEquals(a.theorems.get("nested")!, b.theorems.get("nested")!));
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Nested.g17", source: source.replace("List(idealProducts(A, mul, G))", "List(A) junk") }], ["lib"]), /malformed soft type/);
});
