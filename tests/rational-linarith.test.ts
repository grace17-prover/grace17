// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// Over ℚ, linarith runs the same elimination as over the reals, with the
// strict order only: equalities stand in for non-strict comparisons, and
// comparison or equality goals are settled by trichotomy.
test("linarith decides linear consequences over the rationals", () => {
  const source = `module RationalLinarith
import Grace.Cumulus.Rat

theorem chain (x y z : Rational)
  requires xy : x < y
  requires yz : y < z
  shows x < z
proof
  linarith

theorem sums (a b p q r : Rational)
  requires rab : r < a + b
  requires ap : a < p
  requires bq : b < q
  shows r < p + q
proof
  linarith

theorem cycle (x y : Rational)
  requires xy : x < y
  requires yx : y < x
  shows ⊥
proof
  linarith

theorem negated (x y : Rational)
  requires xy : x < y
  shows ¬(y < x)
proof
  linarith

theorem along_equality (x y z : Rational)
  requires xy : x < y
  requires yz : y = z
  shows x < z
proof
  linarith

theorem cancel (x y z : Rational)
  requires h : x + z = y + z
  shows x = y
proof
  linarith

theorem shifted (x y : Rational)
  requires xy : x < y
  shows x - y < 0
proof
  linarith

theorem reversed (x y : Rational)
  requires xy : x < y
  shows -y < -x
proof
  linarith

theorem successor (x : Rational)
  requires positive : 0 < x
  shows 0 < x + 1
proof
  linarith
`;
  const result = checkWorkbenchFiles([{ name: "RationalLinarith.g17", source }], "ZF", ["RationalLinarith.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
  assert.equal(result.theorems.length, 9);
});

// A goal outside the linear fragment is reported, not silently admitted.
test("linarith over the rationals rejects what the facts do not entail", () => {
  const source = `module RationalLinarithFails
import Grace.Cumulus.Rat

theorem unsupported (x y : Rational)
  requires xy : x < y
  shows y < x
proof
  linarith
`;
  assert.throws(
    () => checkWorkbenchFiles([{ name: "RationalLinarithFails.g17", source }], "ZF", ["RationalLinarithFails.g17"], { includeKernelDetails: false }),
    /line 8: linarith found no checked rational-order derivation/);
});
