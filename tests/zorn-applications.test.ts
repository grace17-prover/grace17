// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createSetTheoryKernel, createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("maximal extensions and maximal ideals have complete ordinary-AC audits", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["examples/ZornApplications.g17"], ["lib"]);
  for (const name of [
    "Grace.Cumulus.Set.MaximalPrinciple.maximal_extension",
    "Grace.Cumulus.Set.MaximalPrinciple.Chain.extends_maximal",
    "Grace.Cumulus.Set.MaximalPrinciple.Zorn.above",
    "Grace.Cumulus.Algebra.Ring.MaximalIdeal.ProperIdeal.extends_maximal",
    "Grace.Cumulus.Algebra.Ring.MaximalIdeal.MaximalIdeal.exists",
    ...["extend_chain", "maximal_above", "maximal_ideal", "extend_ideal"].map(n => `ZornApplications.${n}`),
  ]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), ["set.choice"], name);
    assert.ok(!audit.hereditary.some(a => /sorry/.test(a)), name);
  }
});

test("ordinary ring imports and ideal closure laws remain ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring.g17"], ["lib"]);
  for (const suffix of ["IsIdeal.union_chain", "IsProperIdeal.union_chain", "IsIdeal.whole_of_one",
    "IsIdeal.zero_ideal", "IsProperIdeal.zero_ideal", "IsProperIdeal.iff_ne_whole", "IsMaximalIdeal.eq_or_whole"]) {
    const audit = auditTheoremAxioms(kernel, `Grace.Cumulus.Algebra.Ring.IdealCore.${suffix}`);
    assert.equal(audit.complete, true);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), []);
  }
});

test("nontriviality and properness cannot be dropped from maximal-ideal existence", () => {
  for (const body of [
    `requires ring : IsRing(A, add, zero, neg, mul, one)
     shows ∃ M, IsMaximalIdeal(A, add, zero, neg, mul, one, M)
proof
  exact IsMaximalIdeal.exists_of_nontrivial at A, add, zero, neg, mul, one with *`,
    `requires ideal : IsIdeal(A, add, zero, neg, mul, I)
     shows ∃ M, IsMaximalIdeal(A, add, zero, neg, mul, one, M) ∧ I ⊆ M
proof
  exact IsMaximalIdeal.exists_above at A, add, zero, neg, mul, one, I with *`,
  ]) {
    const kernel = createSetTheoryKernel({ profile: "ZFC" });
    loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring/MaximalIdeal.g17"], ["lib"]);
    assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "Missing.g17", source: `
module Missing
import Grace.Cumulus.Algebra.Ring.MaximalIdeal
theorem invalid (A add zero neg mul one I : Set)
  ${body}
` }], ["lib"]), /surface|argument|proof|premise|requires|goal/i);
  }
});
