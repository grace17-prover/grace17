// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createSetTheoryKernel, createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("colon ideals, maximal implies prime, and the zero-ideal characterization are ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PrimeIdealStarter.g17"], ["lib"]);
  for (const name of [
    ...["colonIdeal.contains", "colonIdeal.ideal", "colonIdeal.proper",
      "IsMaximalIdeal.is_prime", "IsPrimeIdeal.proper", "IsPrimeIdeal.left_of_mul", "IsPrimeIdeal.colon_eq",
      "IsIntegralDomain.zero_prime", "IsPrimeIdeal.zero_iff_domain"].map(n => `Grace.Cumulus.Algebra.Ring.PrimeIdealCore.${n}`),
    ...["maximal_is_prime", "cancel_outside_factor", "zero_prime_iff_domain"].map(n => `PrimeIdealStarter.${n}`),
  ]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("prime-ideal existence and extension inherit ordinary Choice through Zorn", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["examples/ZornApplications.g17"], ["lib"]);
  for (const name of ["Grace.Cumulus.Algebra.Ring.MaximalIdeal.ProperIdeal.extends_prime",
    "Grace.Cumulus.Algebra.Ring.MaximalIdeal.PrimeIdeal.exists", "ZornApplications.extend_to_prime"]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), ["set.choice"], name);
    assert.ok(!audit.hereditary.some(a => /sorry/.test(a)), name);
  }
});

test("maximal implies prime requires commutativity; cancellation requires an outside factor", () => {
  const bodies = [
    `requires ring : IsRing(A, add, zero, neg, mul, one)
     requires maximal : IsMaximalIdeal(A, add, zero, neg, mul, one, I)
     shows IsPrimeIdeal(A, add, zero, neg, mul, one, I)
proof
  exact IsMaximalIdeal.is_prime at A, add, zero, neg, mul, one, I with *`,
    `requires prime : IsPrimeIdeal(A, add, zero, neg, mul, one, I)
     requires hx : x ∈ A
     requires hy : y ∈ A
     requires productIn : call2(mul, x, y) ∈ I
     shows x ∈ I
proof
  exact IsPrimeIdeal.left_of_mul at A, add, zero, neg, mul, one, I, x, y with *`,
  ];
  for (const body of bodies) {
    const kernel = createZfKernel();
    loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring.g17"], ["lib"]);
    assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "Missing.g17", source: `
module Missing
import Grace.Cumulus.Algebra.Ring
theorem invalid (A add zero neg mul one I x y : Set)
  ${body}
` }], ["lib"]), /surface|argument|proof|premise|requires|goal/i);
  }
});
