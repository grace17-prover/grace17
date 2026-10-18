// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

function check(name: string, body: string) {
  const source = `module Tighten.${name}\nimport Grace.Cumulus.Nat\n\n${body}\n`;
  return checkWorkbenchFiles([{ name: `${name}.g17`, source }], "ZFG", [`${name}.g17`], { includeKernelDetails: false });
}

// Integer tightening: a comparison whose atom coefficients share a factor is
// divided through with a rounded constant, so arith refutes problems that are
// feasible over the rationals but not over the naturals.
test("arith closes parity and divisibility contradictions through tightening", () => {
  const cases: [string, string][] = [
    ["halfParity", `theorem probe (x : Nat)
  requires h1 : 1 ≤ 2 * x
  requires h2 : 2 * x ≤ 1
  shows x < x
proof
  arith`],
    ["oddEven", `theorem probe (x y : Nat)
  requires h : 2 * x = 2 * y + 1
  shows y < y
proof
  arith`],
    ["threeSplit", `theorem probe (x y z : Nat)
  requires h : 3 * x + 3 * y = 3 * z + 2
  shows z < z
proof
  arith`],
    ["floorHalf", `theorem probe (x y : Nat)
  requires h : 6 * x ≤ 4 * y + 3
  shows 3 * x ≤ 2 * y + 1
proof
  arith`],
    ["ceilFour", `theorem probe (x y : Nat)
  requires h : 4 * x + 5 ≤ 4 * y
  shows x + 2 ≤ y
proof
  arith`],
    ["mixed", `theorem probe (x y : Nat)
  requires h1 : 2 * x + 1 ≤ 2 * y
  requires h2 : 2 * y ≤ 2 * x + 1
  shows x < x
proof
  arith`],
  ];
  for (const [name, body] of cases) {
    const result = check(name, body);
    assert.equal(result.ok, true, `${name}: ${result.message}`);
  }
});

test("arith still reports a goal its facts do not entail", () => {
  assert.throws(() => check("open", `theorem probe (x y : Nat)
  requires h : 2 * x ≤ 2 * y + 1
  shows x < y
proof
  arith`), /arith/);
});
