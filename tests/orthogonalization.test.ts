// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module OrthogonalizationRegression\nimport Grace.Cumulus.LinearAlgebra.Orthogonalization\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "OrthogonalizationRegression.g17", source }]);

test("public orthogonalization example checks invariants, commutation, and energy", () => {
  assert.equal(checkWorkbenchFiles([{ name: "OrthogonalizationStarter.g17", source: readFileSync("examples/OrthogonalizationStarter.g17", "utf8") }]).ok, true);
});

test("commutation includes the empty dimension without nonzero premises", () => {
  assert.equal(check(header + `theorem empty (u v w : Set, i : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires sequenceW : RealSequence(w)
  shows orthogonalResidual(orthogonalResidual(u, v, 0), w, 0)[i] =
    orthogonalResidual(orthogonalResidual(u, w, 0), v, 0)[i]
proof
  have perpendicular : Orthogonal(v, w, 0)
  . unfold Orthogonal
    exact dotProduct.zero at v, w
  exact orthogonalResidual.commute at u, v, w, 0, i with *
`).ok, true);
});

test("commutation holds at coordinates beyond the finite inner-product prefix", () => {
  assert.equal(check(header + `theorem outside (u v w : Set)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires sequenceW : RealSequence(w)
  requires perpendicular : Orthogonal(v, w, 3)
  shows orthogonalResidual(orthogonalResidual(u, v, 3), w, 3)[17] =
    orthogonalResidual(orthogonalResidual(u, w, 3), v, 3)[17]
proof
  exact orthogonalResidual.commute at u, v, w, 3, 17 with *
`).ok, true);
});

test("component removal cannot preserve arbitrary nonperpendicular directions", () => {
  assert.throws(() => check(header + `theorem invalid (u v w : Set, n : Nat)
  requires sequenceU : RealSequence(u)
  requires sequenceV : RealSequence(v)
  requires sequenceW : RealSequence(w)
  shows dotProduct(orthogonalResidual(u, v, n), w, n) = dotProduct(u, w, n)
proof
  exact dotProduct.after_orthogonal_removal at u, v, w, n with *
`));
});

test("three-part energy rejects an incorrect subtraction", () => {
  const source = readFileSync("examples/OrthogonalizationStarter.g17", "utf8");
  assert.throws(() => checkWorkbenchFiles([{ name: "OrthogonalizationStarter.g17", source: source.replace(
    "squaredNorm(lineProjection(u, w, n), n) +",
    "squaredNorm(lineProjection(u, w, n), n) -") }]));
});

test("successive residuals retain intermediate goals cold and after editing", () => {
  const file = { name: "LinearAlgebra/Orthogonalization.g17", source: readFileSync("lib/Grace/Cumulus/LinearAlgebra/Orthogonalization.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    for (const name of ["orthogonalResidual.orthogonal_pair", "orthogonalResidual.two_step_pythagorean", "orthogonalResidual.commute"]) {
      const proof = result.theorems.find(t => t.name.endsWith(name));
      assert.ok(proof?.steps.some(s => s.after.goals.length > 0), name);
      assert.equal(proof?.steps.at(-1)?.after.goals.length, 0, name);
    }
  }
});

test("Bessel's pair bound requires the stated orthogonality evidence", () => {
  const source = header + `theorem invalid (u v w : RealSequence, n : Nat)
  requires nonzeroV : squaredNorm(v, n) ≠ 0
  requires nonzeroW : squaredNorm(w, n) ≠ 0
  shows squaredNorm(lineProjection(u, v, n), n) +
    squaredNorm(lineProjection(u, w, n), n) ≤ squaredNorm(u, n)
proof
  exact lineProjection.bessel_pair at u, v, w, n with *
`;
  assert.throws(() => check(source));
});

test("Bessel's bound does not assert that the residual vanishes", () => {
  const source = readFileSync("examples/OrthogonalizationStarter.g17", "utf8");
  const statement = "squaredNorm(lineProjection(u, w, n), n) ≤ squaredNorm(u, n)";
  assert.ok(source.includes(statement));
  assert.throws(() => checkWorkbenchFiles([{ name: "OrthogonalizationStarter.g17",
    source: source.replace(statement, "squaredNorm(lineProjection(u, w, n), n) = squaredNorm(u, n)") }]));
});

test("generated projection types cannot create missing sequence evidence", () => {
  assert.throws(() => check(header + `theorem invalid (u v : Set, n : Nat)
  shows Real(projectionCoefficient(u, v, n))
proof
  exact projectionCoefficient.type at u, v, n with *
`));
});
