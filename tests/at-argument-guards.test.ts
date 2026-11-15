// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

function load(name: string, source: string): void {
  loadModuleSourceGraph(createZfKernel(), [{ file: `${name}.g17`, source: `module ${name}\n${source}` }], ["lib"]);
}

function failure(name: string, source: string): string {
  try {
    load(name, source);
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
  throw new Error(`${name} was expected to fail`);
}

const sqrt = "import Grace.Cumulus.Real.Sqrt\n";

test("the guard of a compound at argument is discharged as typecheck discharges it", () => {
  load("AtGuard", `${sqrt}
theorem root.of_square (s : Real)
  requires nonneg : (0:R) ≤ s
  shows realSqrt(s * s) = s
proof
  have squareNonneg := realMulValue.square_nonnegative at s
  have squareReal : Real(s * s) by typecheck
  obtain ⟨_, rootNonneg, rootSquare⟩ :=
    realSqrt.selected at s * s with squareReal, squareNonneg
  have equal := realMulValue.eq_of_square_eq at realSqrt(s * s), s
    with rootNonneg, nonneg, rootSquare
  exact equal
`);
});

test("a with entry that restates a discharged guard through its definition is accepted", () => {
  load("AtGuardNamed", `${sqrt}
theorem root.of_square (s : Real)
  requires nonneg : (0:R) ≤ s
  shows realSqrt(s * s) = s
proof
  have squareNonneg := realMulValue.square_nonnegative at s
  have squareReal : Real(s * s) by typecheck
  obtain ⟨rootReal, rootNonneg, rootSquare⟩ :=
    realSqrt.selected at s * s with squareReal, squareNonneg
  have equal := realMulValue.eq_of_square_eq at realSqrt(s * s), s
    with rootReal, rootNonneg, nonneg, rootSquare
  exact equal
`);
});

test("a guard nothing establishes keeps the application report", () => {
  const message = failure("AtGuardMissing", `${sqrt}
theorem root.unknown (s : Real)
  requires nonneg : (0:R) ≤ s
  requires rootNonneg : (0:R) ≤ s
  shows realSqrt(s) = s
proof
  have equal := realMulValue.eq_of_square_eq at realSqrt(s), s
    with rootNonneg, nonneg, nonneg
  exact equal
`);
  assert.match(message, /application needs realSqrt\(s\) : ℝ|cannot resolve|needs/u);
});
