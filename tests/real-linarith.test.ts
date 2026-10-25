// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

const library = fileURLToPath(new URL("../lib", import.meta.url));
const header = "module User.RealLinarith\nnamespace User.RealLinarith\nimport Grace.Cumulus.Real.Ring\n\n";

test("real linarith decides linear consequences of local comparisons", () => {
  const source = header + `
theorem doubled (U : Real)
  requires h : 0 ≤ U
  shows 0 ≤ U + U
proof
  linarith

theorem mixed_chain (A B C : Real)
  requires ab : A ≤ B
  requires bc : B < C
  shows A < C
proof
  linarith

theorem shift_by_one (X : Real)
  shows X < X + 1
proof
  linarith

theorem negated_bound (A P : Real)
  requires h : -P ≤ A
  shows 0 ≤ A + P
proof
  linarith

theorem product_atom (U X : Real)
  requires h : U * U < X
  shows 0 < X - U * U
proof
  linarith

theorem inconsistent_context (S T : Real)
  requires h1 : S + S ≤ S
  requires h2 : 0 < S
  shows T ≤ T + 1
proof
  linarith

theorem two_hypotheses (A B C : Real)
  requires h1 : A ≤ B
  requires h2 : C ≤ A - B
  shows C ≤ 0
proof
  linarith

theorem antisymmetry (D W : Real)
  requires h1 : D ≤ W
  requires h2 : W ≤ D + 0
  shows D = W
proof
  linarith

theorem negated_goal (A B : Real)
  requires h : A < B
  shows ¬(B ≤ A)
proof
  linarith

theorem contradiction_goal (A B : Real)
  requires h1 : A < B
  requires h2 : B < A
  shows ⊥
proof
  linarith

theorem equality_fact (A B C : Real)
  requires h1 : A = B + C
  requires h2 : 0 ≤ C
  shows B ≤ A
proof
  linarith

theorem conjunction_fact (A B : Real)
  requires h : A ≤ B ∧ B ≤ A + A
  shows 0 ≤ A
proof
  linarith

theorem scaled (A B : Real)
  requires h : A ≤ B
  shows A + A + A ≤ B + B + B
proof
  linarith

end User.RealLinarith
`;
  const loaded = loadModuleSourceGraph(createZfKernel(), [{ file: "RealLinarith.g17", source }], [library]);
  assert.equal(loaded.at(-1)?.theorems.length, 13);
  assert.equal(loaded.at(-1)?.sorries.length, 0);
});

test("real linarith rejects goals that do not follow linearly", () => {
  for (const body of [
    `theorem wrong (A B : Real)
  requires h : A ≤ B
  shows B ≤ A
proof
  linarith`,
    `theorem nonlinear (X Y : Real)
  requires hx : 0 ≤ X
  requires hy : 0 ≤ Y
  shows 0 ≤ X * Y
proof
  linarith`,
  ]) {
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Wrong.g17", source: header + body + "\nend User.RealLinarith\n" }], [library]),
      /linarith|arith/);
  }
});

test("linarith reads numeral scalar multiples", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Scalars.g17", source: `module Scalars
import Grace.Cumulus.Real.Natural

theorem doubled (x y : Real)
  requires bound : x ≤ y
  shows (2:R) * x ≤ y * 2
proof
  linarith

theorem cancel (x y : Real)
  requires scaled : (16:R) * x = (16:R) * y
  shows x = y
proof
  linarith
` }], [library]);
  assert.ok(kernel.theorems.has("Scalars.doubled") && kernel.theorems.has("Scalars.cancel"));
});

test("linarith refutes an equation of real literals, with or without intro", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Literals.g17", source: `module Literals
import Grace.Cumulus.Real.Natural

theorem two_nonzero
  shows (2:R) ≠ 0
proof
  intro zero
  linarith

theorem five_nonzero
  shows (5:R) ≠ 0
proof
  linarith
` }], [library]);
  assert.ok(kernel.theorems.has("Literals.two_nonzero") && kernel.theorems.has("Literals.five_nonzero"));
});
