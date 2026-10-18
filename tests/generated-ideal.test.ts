// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, createSetTheoryKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("generated ideals and unit certificate soundness are checked in ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/NullstellensatzCertificate.g17"], ["lib"]);
  for (const name of [
    ...["membership", "subset", "contains", "least", "ideal", "mono", "eq_of_ideal", "idempotent", "unit_iff", "unit_of_linear_combination2", "unit_obstructs_vanishing"]
      .map(n => `Grace.Cumulus.Algebra.Ring.GeneratedIdeal.idealSpan.${n}`),
    "NullstellensatzCertificate.unit_certificate", "NullstellensatzCertificate.no_common_zero",
  ]) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});
test("the maximal-ideal reduction records ordinary Choice through Zorn", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring/MaximalIdeal.g17"], ["lib"]);
  for (const n of ["exists_maximal", "unit_iff_no_maximal"]) {
    const audit = auditTheoremAxioms(kernel, `Grace.Cumulus.Algebra.Ring.MaximalIdeal.idealSpan.${n}`);
    assert.equal(audit.complete, true);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), ["set.choice"]);
  }
});
test("unit certificate soundness cannot omit nontriviality of the target", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring
theorem invalid (f A add zero neg mul one B plus z minus times unit G : Set)
  requires source : IsCommRing(A, add, zero, neg, mul, one)
  requires target : IsCommRing(B, plus, z, minus, times, unit)
  requires hom : IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)
  requires bounded : G ⊆ A
  requires certificate : one ∈ idealSpan(A, add, zero, neg, mul, G)
  shows ¬(∀ p ∈ G, f(p) = z)
proof
  exact idealSpan.unit_obstructs_vanishing at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, G with *
` }], ["lib"]), /Nontrivial/);
});
