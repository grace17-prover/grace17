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

test("a real numeral is nonzero by arith and by linarith alone", () => {
  load("NumeralNonzero", `${reals}
theorem four.nonzero
  shows (4:R) ≠ 0
proof
  arith

theorem one.nonzero
  shows (1:R) ≠ 0
proof
  linarith

theorem positive.nonzero (x : Real)
  requires pos : (0:R) < x
  shows x ≠ 0
proof
  arith
`);
});

test("arith keeps its report when neither refutation applies", () => {
  const message = failure("NumeralNonzeroOpen", `${reals}
theorem open.nonzero (x : Real)
  shows x ≠ 0
proof
  arith
`);
  assert.match(message, /arith found no linear arithmetic contradiction/u);
});
