// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("Dickson, finite monomial ideals, and the finite-slice proof have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/Dickson.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Polynomial.Divisibility.", "Grace.Cumulus.Algebra.Polynomial.Dickson.", "Grace.Cumulus.Algebra.Polynomial.MonomialIdeal.", "Grace.Cumulus.Algebra.Polynomial.monomialIdealPolynomials.", "DicksonExamples."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  names.push("Grace.Cumulus.Nat.Order.Less.successor_upper");
  assert.ok(names.length >= 50, `expected all new proof boundaries, got ${names.length}`);
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("Dickson finite generation cannot omit finite dimension", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.MonomialIdeal
theorem invalid (V U : Set)
  requires ideal : MonomialIdeal(V, U)
  shows ∃ B, Finite(B) ∧ B ⊆ U ∧ U = monomialSpan(V, B)
proof
  exact MonomialIdeal.finite_generated at V, U with *
` }], ["lib"]), /Finite/);
});

test("finite antichains cannot omit the antichain hypothesis", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.MonomialIdeal
theorem invalid (V S : Set)
  requires variables : Finite(V)
  requires subset : S ⊆ monomials(V)
  shows Finite(S)
proof
  exact Dickson.antichains_finite at V, S with *
` }], ["lib"]), /MonomialAntichain/);
});

test("quotient monomials retain coordinatewise divisibility", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.Divisibility
theorem invalid (V m n : Set)
  requires memberM : m ∈ monomials(V)
  requires memberN : n ∈ monomials(V)
  shows monomialProduct(V, m, monomialQuotient(V, m, n)) = n
proof
  exact monomialQuotient.product at V, m, n with *
` }], ["lib"]), /MonomialDivides/);
});
