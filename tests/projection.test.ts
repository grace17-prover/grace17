// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module ProjectionRegression\nimport Grace.Cumulus.LinearAlgebra.Projection\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "ProjectionRegression.g17", source }]);

test("public projection example checks orthogonality, minimality, and uniqueness", () => {
  assert.equal(checkWorkbenchFiles([{ name: "ProjectionStarter.g17", source: readFileSync("examples/ProjectionStarter.g17", "utf8") }]).ok, true);
});

test("line projection specializes to arbitrary dimensions and signed coefficients", () => {
  let source = header;
  for (const [index, [n, c]] of [[1, "-(1:R)"], [4, "(0:R)"], [17, "(1:R)"]].entries()) source += `theorem minimum_${index} (u v : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, ${n}) ≠ (0:R)
  shows (lineDistanceSquared(u, v, projectionCoefficient(u, v, ${n}), ${n}):R) ≤
    (lineDistanceSquared(u, v, ${c}, ${n}):R)
proof
  exact lineProjection.minimum at u, v, ${c}, ${n} with *
`;
  assert.equal(check(source).ok, true);
});

test("empty-dimensional distances tie for all coefficients", () => {
  assert.equal(check(header + `theorem empty (u v : Set, C D : Real)
  shows lineDistanceSquared(u, v, C, 0) = lineDistanceSquared(u, v, D, 0)
proof
  unfold lineDistanceSquared
  unfold squaredNorm
  simp [dotProduct.zero]
`).ok, true);
});

test("projection uniqueness requires a nonzero direction and a minimizing candidate", () => {
  const example = readFileSync("examples/ProjectionStarter.g17", "utf8");
  const last = example.slice(example.indexOf("theorem unique_best_coefficient"));
  assert.throws(() => check(header + last.replace("  requires nonzero : squaredNorm(v, n) ≠ 0\n", "")));
  assert.throws(() => check(header + last.replace(/  requires minimizing :[^]*?  shows/, "  shows")));
});

test("strict minimality requires a different coefficient", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, C : Real, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, n) ≠ (0:R)
  shows (lineDistanceSquared(u, v, projectionCoefficient(u, v, n), n):R) <
    (lineDistanceSquared(u, v, C, n):R)
proof
  exact lineProjection.strict_minimum at u, v, C, n with *
`));
});

test("orthogonality and distance decomposition reject incorrect formulas", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, n) ≠ (0:R)
  shows Orthogonal(u, v, n)
proof
  exact lineProjection.orthogonal at u, v, n with *
`));
  assert.throws(() => check(header + `theorem invalid (u v : Set, C : Real, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, n) ≠ (0:R)
  shows lineDistanceSquared(u, v, C, n) =
    (lineDistanceSquared(u, v, projectionCoefficient(u, v, n), n):R) -
    (C - (projectionCoefficient(u, v, n):R)) * (C - (projectionCoefficient(u, v, n):R)) * (squaredNorm(v, n):R)
proof
  exact lineProjection.distance_decomposition at u, v, C, n with *
`));
});

test("projection proofs retain intermediate goal states cold and after editing", () => {
  const file = { name: "LinearAlgebra/Projection.g17", source: readFileSync("lib/Grace/Cumulus/LinearAlgebra/Projection.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    for (const name of ["lineProjection.orthogonal", "lineProjection.distance_decomposition", "lineProjection.unique_minimizer", "orthogonalResidual.pythagorean", "lineProjection.idempotent"]) {
      const proof = result.theorems.find(t => t.name.endsWith(name));
      assert.ok(proof?.steps.some(s => s.after.goals.length > 0), name);
      assert.equal(proof?.steps.at(-1)?.after.goals.length, 0, name);
    }
  }
});

test("orthogonalization reconstructs every coordinate, including outside the prefix", () => {
  assert.equal(check(header + `theorem reconstruct (u v : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows u[17] = (lineProjection(u, v, 2)[17]:R) + (orthogonalResidual(u, v, 2)[17]:R)
proof
  exact orthogonalResidual.reconstruction at u, v, 2, 17 with *
`).ok, true);
});

test("coefficient linearity includes empty dimensions and negative scalars", () => {
  assert.equal(check(header + `theorem linear (u w v : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceW : RealSequence(w)
  requires sequenceV : RealSequence(v)
  shows projectionCoefficient(addSequence(u, w), v, 0) =
    (projectionCoefficient(u, v, 0):R) + (projectionCoefficient(w, v, 0):R)
proof
  exact projectionCoefficient.add at u, w, v, 0 with *
theorem negative (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  shows projectionCoefficient(mulSequence(constantSequence(-(1:R)), u), v, n) =
    (-(1:R)) * (projectionCoefficient(u, v, n):R)
proof
  exact projectionCoefficient.scale at u, v, -(1:R), n with *
`).ok, true);
});

test("orthogonal residual has zero projection coefficient", () => {
  assert.equal(check(header + `theorem residual (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, n) ≠ (0:R)
  shows projectionCoefficient(orthogonalResidual(u, v, n), v, n) = (0:R)
proof
  exact orthogonalResidual.projection_coefficient at u, v, n with *
`).ok, true);
});

test("orthogonalization rejects wrong norm signs and an omitted on-line premise", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires nonzero : squaredNorm(v, n) ≠ (0:R)
  shows squaredNorm(u, n) = (squaredNorm(lineProjection(u, v, n), n):R) -
    (squaredNorm(orthogonalResidual(u, v, n), n):R)
proof
  exact orthogonalResidual.pythagorean at u, v, n with *
`));
  assert.throws(() => check(header + `theorem invalid (v : Set, C : Real, n : Nat)
  requires sequence : RealSequence(v)
  shows projectionCoefficient(mulSequence(constantSequence(C), v), v, n) = C
proof
  exact projectionCoefficient.on_line at v, C, n with *
`));
});
