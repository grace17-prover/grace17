// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("image rings, inclusion maps, inverse isomorphisms, and the general image theorem are public and ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring/Image.g17"], ["lib"]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Algebra.Ring.Image.IsRingHom.first_isomorphism_image"));
  loadModuleGraph(kernel, ["examples/ImageRingStarter.g17"], ["lib"]);
  const names = [
    ...["restrict.relates", "restrict.function", "restrict.apply", "functionImage.corestrict", "functionImage.surjective",
      "Bijective.inverse_apply", "Bijective.apply_inverse"].map(n => `Grace.Cumulus.Set.Function.${n}`),
    ...["restrictBinary.function", "restrictBinary.value", "restrictBinary.associative", "restrictBinary.distributive",
      "restrictUnary.function", "restrictUnary.inverse"].map(n => `Grace.Cumulus.Algebra.Restriction.${n}`),
    ...["IsSubring.comm_ring", "IsSubring.inclusion_function", "IsSubring.inclusion_hom", "IsSubring.inclusion_injective"].map(n => `Grace.Cumulus.Algebra.Ring.SubringCore.${n}`),
    "Grace.Cumulus.Algebra.Ring.HomomorphismCore.IsRingIso.inverse",
    ...["IsRingHom.image_subring", "IsRingHom.image_comm_ring", "IsRingHom.corestrict", "IsRingHom.first_isomorphism_image",
      "IsRingHom.image_factorization"].map(n => `Grace.Cumulus.Algebra.Ring.Image.${n}`),
    ...["image_comm_ring", "first_isomorphism_image", "image_factorization", "inverse_isomorphism"].map(n => `ImageRingStarter.${n}`),
  ];
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("restricting a graph requires both a valid subdomain and closure in the requested codomain", () => {
  for (const [name, guards, missing] of [
    ["Closure", "requires subset : S ⊆ A", /∀|forall/],
    ["Subdomain", "requires closed : ∀ x ∈ S, f(x) ∈ C", /Subset|⊆/],
  ] as const) {
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: `Missing${name}.g17`, source: `
module Missing${name}
import Grace.Cumulus.Set.Function
theorem invalid (f A B S C : Set)
  requires function : FunctionBetween(f, A, B)
  ${guards}
  shows FunctionBetween(restrict(f, S), S, C)
proof
  exact restrict.function at f, A, B, S, C with *
` }], ["lib"]), missing);
  }
});

test("a subset is not automatically a unital subring", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "MissingSubring.g17", source: `
module MissingSubring
import Grace.Cumulus.Algebra.Ring.Subring
theorem invalid (A add zero neg mul one S : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires subset : S ⊆ A
  shows IsCommRing(S, restrict(add, S × S), zero, restrict(neg, S), restrict(mul, S × S), one)
proof
  exact IsSubring.comm_ring at A, add, zero, neg, mul, one, S with *
` }], ["lib"]), /Subring/);
});

test("the image corestriction does not assert surjectivity onto the original codomain", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "WrongCodomain.g17", source: `
module WrongCodomain
import Grace.Cumulus.Set.Function
theorem invalid (f A B : Set)
  requires function : FunctionBetween(f, A, B)
  shows SurjectiveBetween(f, A, B)
proof
  exact functionImage.surjective with function
` }], ["lib"]), /goal|expected|prove/);
});
