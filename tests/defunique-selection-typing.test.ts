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

test("the realness of a defunique value follows from its selection law without naming the component", () => {
  load("SelectionTyping", `import Grace.Cumulus.Real.Sqrt

theorem root.real (s : Real)
  requires nonneg : (0:R) ≤ s * s
  shows realSqrt(s * s) ∈ ℝ
proof
  typecheck

theorem root.product (s : Real)
  requires nonneg : (0:R) ≤ s
  shows realSqrt(s * s) * realSqrt(s * s) = s * s
proof
  have squareNonneg := realMulValue.square_nonnegative at s
  have squareReal : Real(s * s) by typecheck
  obtain ⟨_, _, rootSquare⟩ :=
    realSqrt.selected at s * s with squareReal, squareNonneg
  have stated : realSqrt(s * s) * realSqrt(s * s) = s * s
    exact rootSquare
  exact stated
`);
});

test("a conjunct over bare variables is not a rule, and the premise of the law is still required", () => {
  const message = failure("SelectionPremise", `import Grace.Cumulus.Real.Sqrt

theorem root.unknown (s : Real)
  shows realSqrt(s) ∈ ℝ
proof
  typecheck
`);
  assert.match(message, /typecheck could not infer/u);
});
