// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createSetTheoryKernel, createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("Zorn and maximal chains check in ZFC, using ordinary Choice and no admissions", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["examples/ZornStarter.g17"], ["lib"]);
  assert.equal(kernel.axioms.has("set.globalChoice"), false);
  for (const name of ["Grace.Cumulus.Set.ChoiceFunctions.SubsetChoice.exists",
    "Grace.Cumulus.Set.Zorn.Zorn.theorem", "Grace.Cumulus.Set.Zorn.Chain.exists_maximal",
    "ZornStarter.maximal_element", "ZornStarter.maximal_chain"]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, JSON.stringify(audit.unavailable));
    assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), ["set.choice"], name);
    assert.ok(!audit.hereditary.some(a => /sorry/.test(a)), name);
  }
  const hartogs = auditTheoremAxioms(kernel, "Grace.Cumulus.Cardinal.Hartogs.Hartogs.theorem");
  assert.equal(hartogs.complete, true);
  assert.deepEqual(hartogs.hereditary.filter(a => /choice/i.test(a)), []);
});

test("the Choice-based module cannot silently check under ZF", () => {
  assert.throws(() => loadModuleGraph(createZfKernel(), ["lib/Grace/Cumulus/Set/Zorn.g17"], ["lib"]));
});

test("Zorn does not manufacture a maximal point from a partial order alone", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "MissingBounds.g17", source: `
module MissingBounds
import Grace.Cumulus.Set.Zorn
theorem invalid (A r : Set)
  requires order : IsPartialOrder(A, r)
  shows ∃ m, Maximal(A, r, m)
proof
  exact Zorn.theorem at A, r with *
` }], ["lib"]));
});
