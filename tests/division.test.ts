// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module DivisionRegression\nimport Grace.Cumulus.Nat.Division\n";

test("computed division and coefficient transport check through the public import", () => {
  const source = readFileSync("examples/DivisionStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "DivisionStarter.g17", source }]).ok, true);
});

test("quotient computation covers zero, boundary, exact, and inexact division", () => {
  for (const [n, d, q] of [[0, 0, 0], [37, 0, 0], [0, 5, 0], [6, 7, 0], [7, 7, 1], [8, 7, 1], [98, 7, 14], [100, 7, 14], [1234, 37, 33]]) {
    const source = header + `theorem value\n  shows quotientNat(${n}, ${d}) = ${q}\nproof\n  compute\n`;
    assert.equal(checkWorkbenchFiles([{ name: "DivisionRegression.g17", source }]).ok, true);
  }
});

test("division rejects a wrong quotient and a missing nonzero divisor", () => {
  for (const body of [
    `theorem incorrect\n  shows quotientNat(100, 7) = 15\nproof\n  compute\n`,
    `theorem zero_bound (n : Nat)\n  shows Nat(quotientNat(n, 0)) ∧ n = 0 * quotientNat(n, 0) + n % 0 ∧ n % 0 < 0\nproof\n  exact quotientNat.division at n, 0 with *\n`,
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "DivisionRegression.g17", source: header + body }]));
});
