// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("generated subrings and their scoped examples have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel,["examples/GeneratedSubrings.g17"],["lib"]);
  const names=[...kernel.theorems.keys()].filter(n=> /^(Grace.Cumulus.Algebra.Ring.GeneratedSubring\.|GeneratedSubrings\.)/.test(n));
  assert.ok(names.length>=11);
  for(const name of names) {
    const audit=auditTheoremAxioms(kernel,name);
    assert.equal(audit.complete,true,name);
    assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[],name);
  }
});

test("generator inclusion retains ambient carrier membership", () => {
  assert.throws(()=>loadModuleSourceGraph(createZfKernel(),[{file:"Invalid.g17",source:`module Invalid
import Grace.Cumulus.Algebra.Ring.GeneratedSubring
section Rings
variable (A add zero neg mul one G : Set)
notation ring R := (A, add, zero, neg, mul, one)
hypothesis ring : IsCommRing(R)
theorem invalid
  shows G ⊆ generatedSubring(A, add, zero, neg, mul, one, G)
proof
  exact generatedSubring.contains at A, add, zero, neg, mul, one, G with *
end Rings
`}],["lib"]),/G ⊆ A/);
});
