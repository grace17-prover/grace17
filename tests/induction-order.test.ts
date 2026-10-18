// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// A top-level induction on a parameter that is not the last one still
// publishes the theorem with the declared parameter and guard order, so
// `at` lists and positional premises follow the header.
test("induction on an earlier parameter keeps the declared binder order", () => {
  const source = `module InductionOrder
import Grace.Core.Nat.Algebra

theorem add.self_first (m n : Nat)
  shows add(m, n) = add(m, n)
proof
  induction m
  | zero => rfl
  | succ(k) using ih => rfl

theorem use_in_order (a b : Nat)
  shows add(a, b) = add(a, b)
proof
  exact add.self_first at a, b with *

theorem guards_in_order (a b : Nat)
  shows add(a, b) = add(a, b)
proof
  have aNat : Nat(a)
    typecheck
  have bNat : Nat(b)
    typecheck
  exact add.self_first at a, b with aNat, bNat
`;
  const result = checkWorkbenchFiles([{ name: "InductionOrder.g17", source }], "ZF", ["InductionOrder.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
  const statement = result.theorems.find(theorem => theorem.name.endsWith("add.self_first"))?.statement ?? "";
  assert.ok(statement.startsWith("∀ m n : ℕ,"), statement);
});

// A supplied premise list fills every generated guard, whichever guard the
// named evidence happens to match.
test("a named guard premise does not stop the remaining guards from being inferred", () => {
  const source = `module GuardFill
import Grace.Core.Nat.Algebra

theorem closed_use (a b : Nat)
  shows Nat(add(a, b))
proof
  have bNat : Nat(b)
    typecheck
  exact add.closed at b, a with bNat
`;
  const result = checkWorkbenchFiles([{ name: "GuardFill.g17", source }], "ZF", ["GuardFill.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
});

// Number-system glyphs stand for their declared names in every segment of a
// dotted reference.
test("glyphs resolve inside dotted names", () => {
  const source = `module Glyphs
namespace Glyphs

def ℚ : Set := ∅

theorem dotted (q : Set)
  requires member : q ∈ Glyphs.ℚ
  shows q ∈ Glyphs.rationals
proof
  exact member

end Glyphs
`;
  const result = checkWorkbenchFiles([{ name: "Glyphs.g17", source }], "ZF", ["Glyphs.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, result.message);
});
