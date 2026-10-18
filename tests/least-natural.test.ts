// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, createZfgKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("least-number selection proves membership and minimality in ZF, including an unordered pair", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/LeastNaturalStarter.g17"], ["lib"]);
  for (const name of ["Grace.Cumulus.Nat.Least.leastNatural.member",
    "Grace.Cumulus.Nat.Least.leastNatural.least", "LeastNaturalStarter.least_of_unordered_pair"]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), [], name);
  }
});

test("least-number membership cannot omit either the inhabited or natural-subset premise", () => {
  for (const premise of ["requires inhabited : Nonempty(S)", "requires naturals : S ⊆ ℕ"]) {
    const kernel = createZfKernel();
    assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "LeastMissing.g17", source: `
module LeastMissing
import Grace.Cumulus.Nat.Least
theorem invalid (S : Set)
  ${premise}
  shows leastNatural(S) ∈ S
proof
  exact leastNatural.member at S with *
` }], ["lib"]));
  }
});

test("the migrated compactness and integration laws have complete hereditary audits without Choice", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Real/Analysis/Integration/IndefiniteIntegral.g17"], ["lib"]);
  for (const name of [
    "Grace.Cumulus.Real.Analysis.SequentialCompactness.closedInterval.bolzano_weierstrass",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.refinementIndex.selected",
    "Grace.Cumulus.Real.Analysis.Integration.PartitionSplit.refinementSegmentCount.selected",
  ]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), [], name);
  }
  const integral = auditTheoremAxioms(kernel,
    "Grace.Cumulus.Real.Analysis.Integration.IndefiniteIntegral.integralValue.selected");
  assert.equal(integral.complete, true);
  assert.ok(integral.hereditary.includes("set.globalChoice"));
  assert.ok(integral.axioms.find(a => a.name === "set.globalChoice")!.path.every(
    name => !name.includes("monotoneIndex") && !name.includes("refinementIndex")));

});
