// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// With the natural and the integer orders both in scope, `<` on naturals
// still resolves: a typed operand decides for an untyped one, a refinement
// such as Prime(p) selects the carrier it proves, and operands with no
// carrier information at all take the natural reading.

import assert from "node:assert/strict";
import test from "node:test";
import { checkWorkbenchFiles } from "../src/workbench.ts";

test("the natural order resolves beside the integer order", () => {
  const source = `module OrderResolution
import Grace.Cumulus.NumberTheory
import Grace.Cumulus.Int

theorem typed_side (i : Nat)
  shows 0 < succ(i)
proof
  arith

theorem refined_side (p : Set)
  requires prime : Prime(p)
  shows 1 < p
proof
  exact Prime.greater_than_one with prime

theorem untyped_sides (a b : Set)
  requires h : a < b
  shows a < b
proof
  exact h

theorem integer_side (z : Set)
  requires hz : Integer(z)
  requires h : z < z
  shows ⊥
proof
  exact integerLess.irreflexive with hz, h
`;
  const result = checkWorkbenchFiles([{ name: "OrderResolution.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 400));
});
