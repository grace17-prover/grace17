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

const reals = "import Grace.Cumulus.Real.Inverse\nimport Grace.Cumulus.Real.Natural\n";

test("ring and linear_combination read division by a numeral literal as multiplication by its inverse", () => {
  load("NumeralDivision", `${reals}
theorem solve (x : Real)
  requires h : (8:R) * x = 1
  shows x = (1:R) / (8:R)
proof
  linear_combination ((1:R) / (8:R)) * h

theorem halves (x : Real)
  shows x / (2:R) + x / (2:R) = x
proof
  ring

theorem scaled (x : Real)
  shows -(3:R) / (4:R) * x = -(6:R) / (8:R) * x
proof
  ring

theorem cubic (x : Real)
  requires equation : (8:R) * (x * x * x) - (6:R) * x - (1:R) = 0
  shows x * x * x + (-(3:R) / (4:R)) * x + (-(1:R) / (8:R)) = 0
proof
  linear_combination ((1:R) / (8:R)) * equation
`);
});

test("a quotient by zero stays an atom and a false identity keeps the report", () => {
  load("ZeroDivisor", `${reals}
theorem atom (x : Real)
  shows x / (0:R) = x / (0:R)
proof
  ring
`);
  const message = failure("NumeralDivisionWrong", `${reals}
theorem wrong (x : Real)
  shows x / (2:R) = x
proof
  ring
`);
  assert.match(message, /the two ring polynomials have different normal forms; a quotient t \/ u by a term is an atom for ring, and t \/ k by a numeral literal is t \* k⁻¹/u);
});
