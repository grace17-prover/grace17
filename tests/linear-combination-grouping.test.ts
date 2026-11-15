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

test("a coefficient distributes over a parenthesized combination of hypotheses", () => {
  load("Grouping", `${reals}
theorem distribute (x y z : Real)
  requires h1 : x = y
  requires h2 : y = z
  shows (2:R) * x - (2:R) * y = (2:R) * y - (2:R) * z
proof
  linear_combination (2:R) * (h1 - h2)

theorem nested (x y z : Real)
  requires h1 : x = y
  requires h2 : y = z
  shows (3:R) * ((2:R) * x) - (3:R) * ((2:R) * y) = 0
proof
  linear_combination (3:R) * ((2:R) * h1 - (2:R) * h2) + (6:R) * h2

theorem bare (x y : Real)
  requires h1 : x = y
  shows x = y
proof
  linear_combination (h1)

theorem negated (x y : Real)
  requires h1 : x = y
  shows y = x
proof
  linear_combination -(h1)
`);
});

test("a malformed piece is still reported", () => {
  const message = failure("GroupingMalformed", `${reals}
theorem broken (x y : Real)
  requires h1 : x = y
  shows x = y
proof
  linear_combination (2:R) * (h1 h2)
`);
  assert.match(message, /malformed linear combination/u);
});
