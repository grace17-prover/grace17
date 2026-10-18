// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { performance } from "node:perf_hooks";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module CauchyRegression\nimport Grace.Cumulus.LinearAlgebra.CauchySchwarz\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "CauchyRegression.g17", source }]);

test("the public Cauchy–Schwarz and scalar-equality example checks", () => {
  assert.equal(checkWorkbenchFiles([{ name: "CauchySchwarzStarter.g17", source: readFileSync("examples/CauchySchwarzStarter.g17", "utf8") }]).ok, true);
});

test("the arbitrary-dimensional theorem specializes to empty and larger dimensions", () => {
  let source = header;
  for (const n of [0, 1, 7, 32]) source += `theorem dimension_${n} (u v : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows (dotProduct(u, v, ${n}):R) * (dotProduct(u, v, ${n}):R) ≤ (squaredNorm(u, ${n}):R) * (squaredNorm(v, ${n}):R)
proof
  exact dotProduct.cauchy_schwarz at u, v, ${n} with *
`;
  assert.equal(check(source).ok, true);
});

test("scalar equality includes zero and negative coefficients", () => {
  let source = header;
  for (const [i, c] of ["(0:R)", "-(1:R)"].entries()) source += `theorem scalar_${i} (v : Set, n : Nat)
  requires sequence : RealSequence(v)
  shows (dotProduct(mulSequence(constantSequence(${c}), v), v, n):R) * (dotProduct(mulSequence(constantSequence(${c}), v), v, n):R) = (squaredNorm(mulSequence(constantSequence(${c}), v), n):R) * (squaredNorm(v, n):R)
proof
  exact dotProduct.cauchy_schwarz_scalar_equality at v, ${c}, n with *
`;
  assert.equal(check(source).ok, true);
});

test("wrong inequality directions and missing sequence evidence are rejected", () => {
  const source = readFileSync("examples/CauchySchwarzStarter.g17", "utf8");
  assert.throws(() => checkWorkbenchFiles([{ name: "CauchySchwarzStarter.g17", source: source.replace("≤", "≥") }]));
  assert.throws(() => checkWorkbenchFiles([{ name: "CauchySchwarzStarter.g17", source: source.replace("  requires sequenceV : RealSequence(v)\n", "") }]));
});

test("zero-norm and positive-factor cancellation require their hypotheses", () => {
  assert.throws(() => check(header + `theorem invalid (A B C : Real)
  requires multiplied : A * C ≤ B * C
  shows A ≤ B
proof
  exact realLe.mul_right_cancel_positive at A, B, C with *
`));
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows dotProduct(u, v, n) = (0:R)
proof
  exact dotProduct.zero_of_squaredNorm_zero at u, v, n with *
`));
});

test("Cauchy–Schwarz and equality retain intermediate goal states after editing", () => {
  const file = { name: "LinearAlgebra/CauchySchwarz.g17", source: readFileSync("lib/Grace/Cumulus/LinearAlgebra/CauchySchwarz.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const start = performance.now();
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    for (const name of ["dotProduct.cauchy_schwarz", "dotProduct.cauchy_schwarz_equality_iff", "squaredNorm.zero_prefix"]) {
      const proof = result.theorems.find(t => t.name.endsWith(name));
      assert.ok(proof?.steps.some(s => s.after.goals.length > 0), name);
      assert.equal(proof?.steps.at(-1)?.after.goals.length, 0, name);
    }
    console.log(`Cauchy–Schwarz ${suffix ? "edited" : "cold leaf"}: ${(performance.now() - start).toFixed(1)} ms`);
  }
});

test("equality characterization and zero-norm criterion include the empty prefix", () => {
  let source = header;
  for (const n of [0, 1, 9]) source += `theorem equality_${n} (u v : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows (dotProduct(u, v, ${n}):R) * (dotProduct(u, v, ${n}):R) =
      (squaredNorm(u, ${n}):R) * (squaredNorm(v, ${n}):R) ↔
    (squaredNorm(v, ${n}) = (0:R) ∨
      (∃ C ∈ ℝ, (∀ i ∈ ℕ, i < ${n} → u[i] = C * (v[i]:R))))
proof
  exact dotProduct.cauchy_schwarz_equality_iff at u, v, ${n} with *
theorem zero_${n} (u : Set)
  requires sequence : RealSequence(u)
  shows squaredNorm(u, ${n}) = (0:R) ↔ (∀ i ∈ ℕ, i < ${n} → u[i] = (0:R))
proof
  exact squaredNorm.eq_zero_iff at u, ${n} with *
`;
  assert.equal(check(source).ok, true);
});

test("equality cannot omit the zero-vector alternative or extend beyond the prefix", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows (dotProduct(u, v, n):R) * (dotProduct(u, v, n):R) =
      (squaredNorm(u, n):R) * (squaredNorm(v, n):R) ↔
    (∃ C ∈ ℝ, (∀ i ∈ ℕ, i < n → u[i] = C * (v[i]:R)))
proof
  exact dotProduct.cauchy_schwarz_equality_iff at u, v, n with *
`));
  assert.throws(() => check(header + `theorem invalid (u : Set, n : Nat)
  requires sequence : RealSequence(u)
  shows squaredNorm(u, n) = (0:R) → ∀ i ∈ ℕ, u[i] = (0:R)
proof
  exact squaredNorm.zero_prefix at u, n with *
`));
});

test("the equality residual requires equality, not merely Cauchy–Schwarz", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires inequality : (dotProduct(u, v, n):R) * (dotProduct(u, v, n):R) ≤
    (squaredNorm(u, n):R) * (squaredNorm(v, n):R)
  shows squaredNorm(subSequence(mulSequence(constantSequence(squaredNorm(v, n)), u),
    mulSequence(constantSequence(dotProduct(u, v, n)), v)), n) = (0:R)
proof
  exact dotProduct.cauchy_schwarz_equality_residual at u, v, n with *
`));
});
