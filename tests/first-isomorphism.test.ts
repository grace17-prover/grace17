// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("ring maps, quotient universality, and first isomorphism are public with complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Ring.g17"], ["lib"]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Algebra.Ring.FirstIsomorphism.RingHom.first_isomorphism"));
  loadModuleGraph(kernel, ["examples/FirstIsomorphismStarter.g17"], ["lib"]);
  const names = [
    "Grace.Cumulus.Set.Function.FunctionBetween.ext",
    ...["quotientMapValue.exists", "quotientMapValue.unique", "quotientMap.function", "quotientMap.class",
      "quotientMap.injective", "quotientMap.surjective", "quotientMap.unique", "quotientMap.factorization",
      "quotientMap.binary", "quotientMap.unary"].map(n => `Grace.Cumulus.Relation.QuotientMap.${n}`),
    ...["IsRingHom.kernel_ideal", "IsRingHom.kernel_congruent", "IsRingHom.respects_ideal", "IsRingHom.identity",
      "IsRingHom.compose", "IsRingHom.of_add_mul_one", "IsRingIso.hom", "IsRingIso.bijective"].map(n => `Grace.Cumulus.Algebra.Ring.HomomorphismCore.${n}`),
    ...["idealQuotient.projection_hom", "IsRingHom.quotient", "IsRingHom.factorization", "IsRingHom.factor_unique",
      "idealQuotient.first_isomorphism"].map(n => `Grace.Cumulus.Algebra.Ring.FirstIsomorphism.${n}`),
    ...["first_isomorphism", "equal_mod_kernel", "unique_descent"].map(n => `FirstIsomorphismStarter.${n}`),
  ];
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("descent cannot manufacture compatibility, reflection, or surjectivity", () => {
  for (const [name, guards, goal, rule, missing] of [
    ["Respects", "", "FunctionBetween(quotientMap(f, A, B, r), (A ⧸ r), B)", "quotientMap.function", /Respects/],
    ["Reflects", "requires respects : Respects(f, A, r)", "InjectiveBetween(quotientMap(f, A, B, r), (A ⧸ r), B)", "quotientMap.injective", /relates/],
    ["Onto", "requires respects : Respects(f, A, r)", "SurjectiveBetween(quotientMap(f, A, B, r), (A ⧸ r), B)", "quotientMap.surjective", /SurjectiveBetween/],
  ] as const) {
    const kernel = createZfKernel();
    assert.throws(() => loadModuleSourceGraph(kernel, [{ file: `Missing${name}.g17`, source: `
module Missing${name}
import Grace.Cumulus.Relation.QuotientMap
theorem invalid (f A B r : Set)
  requires function : FunctionBetween(f, A, B)
  requires equivalence : Equivalence(A, r)
  ${guards}
  shows ${goal}
proof
  exact ${rule} at f, A, B, r with *
` }], ["lib"]), missing);
  }
});

test("factorization cannot discard the kernel containment hypothesis", () => {
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "MissingKernel.g17", source: `
module MissingKernel
import Grace.Cumulus.Algebra.Ring
theorem invalid (f A add zero neg mul one B plus z minus times unit I : Set)
  requires source : IsCommRing(A, add, zero, neg, mul, one)
  requires target : IsCommRing(B, plus, z, minus, times, unit)
  requires hom : IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)
  requires ideal : IsIdeal(A, add, zero, neg, mul, I)
  shows Respects(f, A, idealRelation(A, add, neg, I))
proof
  exact IsRingHom.respects_ideal at f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, I with *
` }], ["lib"]), /Subset|⊆/);
});

test("function extensionality requires equality on the entire common domain", () => {
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "MissingPointwise.g17", source: `
module MissingPointwise
import Grace.Cumulus.Set.Function
theorem invalid (f g A B x : Set)
  requires hf : FunctionBetween(f, A, B)
  requires hg : FunctionBetween(g, A, B)
  requires hx : x ∈ A
  requires oneValue : f(x) = g(x)
  shows f = g
proof
  exact FunctionBetween.ext at f, g, A, B with *
` }], ["lib"]), /∀|forall/);
});
