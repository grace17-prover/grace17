// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("prime and maximal correspondence are public, with complete choice-free audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PrimeCorrespondenceStarter.g17"], ["lib"]);
  const names = [
    ...["comap_proper", "comap_prime", "map_proper", "prime_of_comap", "comap_prime_iff", "map_prime",
      "comap_maximal", "maximal_of_comap", "comap_maximal_iff", "map_maximal"]
      .map(n => `Grace.Cumulus.Algebra.Ring.PrimeCorrespondence.IsRingHom.${n}`),
    ...["proper", "ideal"].map(n => `Grace.Cumulus.Algebra.Ring.IdealCore.IsMaximalIdeal.${n}`),
    ...["proper", "ideal"].map(n => `Grace.Cumulus.Algebra.Ring.PrimeIdealCore.IsPrimeIdeal.${n}`),
    ...["pullback_prime", "prime_equivalence", "maximal_equivalence", "pushforward_maximal"]
      .map(n => `PrimeCorrespondenceStarter.${n}`),
  ];
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
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
`;
for (const [kind, theorem] of [["IsPrimeIdeal", "map_prime"], ["IsMaximalIdeal", "map_maximal"]]) {
  test(`${theorem} rejects a missing kernel-containment hypothesis`, () => {
    const source = header + `hypothesis onto : SurjectiveBetween(f, A, B)
hypothesis property : ${kind}(A, add, zero, neg, mul, one, I)
theorem invalid
  shows ${kind}(B, plus, z, minus, times, unit, idealMap(f, B, I))
proof
  exact IsRingHom.${theorem} at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
end Maps
`;
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source }], ["lib"]), /Subset|⊆/);
  });
}
test("maximal inverse images require surjectivity", () => {
  const source = header + `hypothesis maximal : IsMaximalIdeal(B, plus, z, minus, times, unit, I)
theorem invalid
  shows IsMaximalIdeal(A, add, zero, neg, mul, one, idealComap(f, A, I))
proof
  exact IsRingHom.comap_maximal at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
end Maps
`;
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source }], ["lib"]), /SurjectiveBetween/);
});
test("reflecting primality through an inverse image requires surjectivity", () => {
  const source = header + `hypothesis ideal : IsIdeal(B, plus, z, minus, times, I)
hypothesis prime : IsPrimeIdeal(A, add, zero, neg, mul, one, idealComap(f, A, I))
theorem invalid
  shows IsPrimeIdeal(B, plus, z, minus, times, unit, I)
proof
  exact IsRingHom.prime_of_comap at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
end Maps
`;
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Missing.g17", source }], ["lib"]), /SurjectiveBetween/);
});
