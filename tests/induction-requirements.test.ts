// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, elaborateModule, forkSurfaceEnvironment, formatFormula, exportTheorem, verifyExportedProof } from "../src/index.ts";

const source = `
datatype Peano
  | zero
  | succ(pred : self)
define copy (n : Peano) -> Peano
  | Peano.zero => Peano.zero
  | Peano.succ(k) => Peano.succ(copy(k))
  descends n

theorem dependent (a : Set, n : Peano, b : Set)
  requires first : a = a
  requires dependent : n = n
  requires last : b = b
  shows copy(n) = n
proof
  induction n
  | Peano.zero =>
    intro dependent
    rw copy
    rfl
  | Peano.succ(k) using ih =>
    intro dependent
    have same : k = k
      rfl
    have smaller := ih with same
    rw copy
    rw smaller
    rfl
`;

test("plain induction reverts dependent requirements and preserves public binder and premise order", () => {
  const base = createZfgKernel();
  elaborateModule(base, "");
  const cold = base.fork();
  forkSurfaceEnvironment(base, cold);
  elaborateModule(cold, source);
  assert.ok(cold.theorems.has("dependent.generalized_induction_aux"));
  const statement = formatFormula(cold.theorems.get("dependent")!);
  assert.match(statement, /∀ a.*∀ n.*∀ b/);
  assert.match(statement, /a = a.*n = n.*b = b.*copy\(n\) = n/);
  verifyExportedProof(cold, exportTheorem(cold, "dependent"));
  const step = cold.theoremTacticTraces.get("dependent")!.steps[0]!;
  assert.match(formatFormula(step.after.goals[0]!.goal), /zero = zero.*→/);
  const warm = base.fork();
  forkSurfaceEnvironment(base, warm);
  elaborateModule(warm, source);
  assert.ok(warm.theorems.has("dependent.generalized_induction_aux"));
  assert.equal(warm.theoremProofs.get("dependent"), cold.theoremProofs.get("dependent"));
  verifyExportedProof(warm, exportTheorem(warm, "dependent"));
});

test("dependent requirements cannot be discarded or leaked into the induction hypothesis", () => {
  const bad = `
datatype Peano
  | zero
  | succ(pred : self)
theorem invalid (n : Peano)
  requires impossible : n ≠ n
  shows False
proof
  induction n
  | Peano.zero => exact impossible
  | Peano.succ(k) using ih => exact ih
`;
  assert.throws(() => elaborateModule(createZfgKernel(), bad));
  // The hypothesis for k is still conditional: it cannot prove False without k ≠ k.
  assert.throws(() => elaborateModule(createZfgKernel(), bad.replace(
    "| Peano.zero => exact impossible", "| Peano.zero =>\n    intro impossible\n    have same : Peano.zero = Peano.zero\n      rfl\n    exact impossible with same")));
});
