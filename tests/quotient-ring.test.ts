// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createSetTheoryKernel, createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("quotient operations, rings, and the domain characterization have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring/Quotient.g17"], ["lib"]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Algebra.Ring.QuotientCore.idealQuotient.domain_iff_prime"),
    "the quotient module must expose the complete quotient API");
  loadModuleGraph(kernel, ["examples/QuotientRingStarter.g17"], ["lib"]);
  const names = [
    ...["quotientBinaryValue.exists", "quotientBinaryValue.unique", "quotientBinary.function",
      "quotientUnaryValue.exists", "quotientUnaryValue.unique", "quotientUnary.function",
      "quotientProjection.surjective", "quotient.comm_ring"].map(n => `Grace.Cumulus.Relation.QuotientOperations.${n}`),
    ...["Congruent.mul", "idealRelation.equivalence", "idealQuotient.comm_ring",
      "idealClass.eq_zero", "idealQuotient.nontrivial_iff", "idealQuotient.domain_iff_prime",
      "idealQuotient.projection_kernel"].map(n => `Grace.Cumulus.Algebra.Ring.QuotientCore.${n}`),
    ...["quotient_is_ring", "domain_iff_prime", "rearrange_member", "proof_patterns"].map(n => `QuotientRingStarter.${n}`),
  ];
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("Zorn gives a domain quotient above any proper ideal, with explicit ordinary AC", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["examples/ZornApplications.g17"], ["lib"]);
  const audit = auditTheoremAxioms(kernel, "ZornApplications.exists_domain_quotient");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), ["set.choice"]);
  assert.ok(!audit.hereditary.some(a => /sorry/.test(a)));
});

test("quotient operation lifting does not invent compatibility", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Relation/QuotientOperations.g17"], ["lib"]);
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "MissingCompatibility.g17", source: `
module MissingCompatibility
import Grace.Cumulus.Relation.QuotientOperations
theorem invalid (A r op : Set)
  requires equivalence : Equivalence(A, r)
  requires closed : IsMagma(A, op)
  shows FunctionBetween(quotientBinary(A, r, op), (A ⧸ r) × (A ⧸ r), (A ⧸ r))
proof
  exact quotientBinary.function at A, r, op with *
` }], ["lib"]), /CompatibleBinary/);
});
