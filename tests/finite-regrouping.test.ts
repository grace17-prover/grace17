// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("finite-set interchange and arbitrary-fiber regrouping have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/FiniteRegrouping.g17"], ["lib"]);
  const prefixes = ["Grace.Cumulus.Algebra.Ring.FiniteDoubleSum.", "Grace.Cumulus.Algebra.Ring.Regrouping.", "FiniteRegrouping."];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  names.push("Grace.Cumulus.Algebra.Ring.SumSupport.finiteRingSum.singleton", "Grace.Cumulus.Algebra.Ring.SumSupport.finiteRingSum.single", "Grace.Cumulus.Cardinal.Finite.Finite.enumeration", "Grace.Cumulus.Cardinal.Product.productMap.apply");
  assert.ok(names.length >= 39, `expected all new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.Regrouping
${source}` }], ["lib"]), pattern);
}

test("regrouping cannot silently drop outputs outside the target groups", () => {
  rejects(`theorem invalid (D C A add zero neg mul one h w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires weights : FunctionBetween(w, D, A)
  requires finiteD : Finite(D)
  requires finiteC : Finite(C)
  shows finiteRingSum(C, A, add, zero, neg, mul, one, finitePushforward(D, C, A, add, zero, neg, mul, one, h, w)) = finiteRingSum(D, A, add, zero, neg, mul, one, w)
proof
  exact finitePushforward.sum at D, C, A, add, zero, neg, mul, one, h, w with *
`, /FunctionBetween\(h/);
});

test("finite-set interchange retains both finiteness hypotheses", () => {
  rejects(`theorem invalid (D E A add zero neg mul one w : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finiteD : Finite(D)
  requires matrix : FunctionBetween(w, D × E, A)
  shows finiteDoubleSum(D, E, A, add, zero, neg, mul, one, w) = finiteDoubleSum(E, D, A, add, zero, neg, mul, one, transposedMatrix(D, E, A, w))
proof
  exact finiteDoubleSum.interchange at D, E, A, add, zero, neg, mul, one, w with *
`, /Finite\(E\)/);
});

test("a single supported coefficient contributes only if its index is included", () => {
  rejects(`theorem invalid (C A add zero neg mul one a c : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires finite : Finite(C)
  requires coefficient : a ∈ A
  shows finiteRingSum(C, A, add, zero, neg, mul, one, coefficientSingle(C, A, zero, a, c)) = a
proof
  exact finiteRingSum.single at C, A, add, zero, neg, mul, one, a, c with *
`, /c ∈ C/);
});
