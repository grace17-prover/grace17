// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("arbitrary rectangular sum interchange and transpose involution have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/DoubleSums.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n => n.startsWith("Grace.Cumulus.Algebra.Ring.DoubleSum.") || n.startsWith("DoubleSums."));
  assert.ok(names.length >= 20, `expected all new boundaries, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("sum interchange retains matrix carrier closure", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.DoubleSum
theorem invalid (A add zero neg mul one w : Set, m n : Nat)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  shows ringDoubleSum(w, add, zero, m, n) = ringDoubleSum(transposedMatrix(m, n, A, w), add, zero, n, m)
proof
  exact ringDoubleSum.interchange at A, add, zero, neg, mul, one, w, m, n with *
` }], ["lib"]), /FunctionBetween/);
});

test("different matrices cannot be interchanged without the transpose equation", () => {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Ring.DoubleSum
theorem invalid (A add zero neg mul one w v : Set, m n : Nat)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires valuesW : RingMatrixValues(w, A, m, n)
  requires valuesV : RingMatrixValues(v, A, n, m)
  shows ringDoubleSum(w, add, zero, m, n) = ringDoubleSum(v, add, zero, n, m)
proof
  have rule := ringDoubleSum.transpose at A, add, zero, neg, mul, one, w, v, m, n with *
  exact rule with valuesW, valuesV
` }], ["lib"]), /TransposedValues/);
});
