// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("finite supports, coefficient operations, and their example have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Cardinal.g17", "examples/FiniteSupportCoefficients.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Cardinal.ListSupport.", "Grace.Cumulus.Algebra.Coefficients.", "FiniteSupportCoefficients."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  assert.ok(names.length >= 53, `expected the new public proofs, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("a function into a ring does not automatically have finite support", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Coefficients
theorem invalid (f I A z : Set)
  requires function : FunctionBetween(f, I, A)
  shows CoefficientMap(f, I, A, z)
proof
  unfold CoefficientMap
  refine ⟨function, ?_⟩
  assumption
` }], ["lib"]), /assumption|Finite/);
});

test("finiteness cannot be transported to an unrelated set", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Cardinal.ListSupport
theorem invalid (S T : Set)
  requires finite : Finite(T)
  shows Finite(S)
proof
  exact Finite.subset at S, T with *
` }], ["lib"]), /Subset|⊆/);
});

test("scalar closure requires the scalar to belong to the coefficient ring", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Coefficients
theorem invalid (I A add zero neg mul one a f : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires map : CoefficientMap(f, I, A, zero)
  shows CoefficientMap(coefficientScale(I, A, add, zero, neg, mul, one, a, f), I, A, zero)
proof
  exact CoefficientMap.scale at I, A, add, zero, neg, mul, one, a, f with *
` }], ["lib"]), /a ∈ A/);
});
