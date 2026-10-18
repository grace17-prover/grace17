// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("ideal correspondence and quotient round trips are exposed through their defining module with complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring/Correspondence.g17"], ["lib"]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Algebra.Ring.Correspondence.IsRingHom.ideal_correspondence"));
  loadModuleGraph(kernel, ["examples/IdealCorrespondenceStarter.g17"], ["lib"]);
  for (const name of [
    ...["idealComap.monotone", "idealMap.monotone", "idealMap.galois", "idealMap.comap_eq",
      "IsRingHom.comap_ideal", "IsRingHom.kernel_subset_comap", "IsRingHom.comap_map_eq", "IsRingHom.map_ideal",
      "IsRingHom.ideal_correspondence", "idealQuotient.kernel_eq", "idealQuotient.comap_map_eq"].map(n => `Grace.Cumulus.Algebra.Ring.Correspondence.${n}`),
    ...["inverse_image", "recover_source", "image", "inclusion_equivalence"].map(n => `IdealCorrespondenceStarter.${n}`),
  ]) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

const header = `module Missing
import Grace.Cumulus.Algebra.Ring
section Maps
variable (f A add zero neg mul one B plus z minus times unit I : Set)
hypothesis source : IsCommRing(A, add, zero, neg, mul, one)
hypothesis target : IsCommRing(B, plus, z, minus, times, unit)
hypothesis hom : IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)
hypothesis ideal : IsIdeal(A, add, zero, neg, mul, I)
`;

test("direct ideal images require surjectivity onto the target ring", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source: header + `
theorem invalid
  shows IsIdeal(B, plus, z, minus, times, idealMap(f, B, I))
proof
  exact IsRingHom.map_ideal at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
end Maps
` }], ["lib"]), /SurjectiveBetween/);
});

test("source ideal recovery requires containment of the kernel", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source: header + `
theorem invalid
  shows idealComap(f, A, idealMap(f, B, I)) = I
proof
  exact IsRingHom.comap_map_eq at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
end Maps
` }], ["lib"]), /Subset|⊆/);
});

test("target round trip requires surjectivity even when a function graph is available", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source: `
module Missing
import Grace.Cumulus.Algebra.Ring
theorem invalid (f A B J : Set)
  requires function : FunctionBetween(f, A, B)
  requires bounded : J ⊆ B
  shows idealMap(f, B, idealComap(f, A, J)) = J
proof
  exact idealMap.comap_eq at f, A, B, J with *
` }], ["lib"]), /SurjectiveBetween/);
});
