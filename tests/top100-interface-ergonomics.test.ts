// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Ergonomics requested while proving Top 100 theorems through the machine
// interface: `by_cases` splits on a proposition, `∃ m n : ℕ` reads typed
// binders without parentheses, `ring` expands literal powers, `compute`
// certifies closed order goals over ℕ, any numeral literal is typed at
// once, natural subtraction and remainder evaluate natively, a `with` list
// supplies the conjuncts of a conjunction requirement in order, and a step
// in a closed bullet branch is reported with the line that closed it.

import assert from "node:assert/strict";
import test from "node:test";
import { app, createZfKernel, evaluateNative, loadModuleSourceGraph, nat, SurfaceError } from "../src/index.ts";

const main = "module Top100Ergonomics\nimport Grace.Cumulus.Main\n";

function check(source: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Top100Ergonomics.g17", source }], ["lib"]);
  return kernel;
}

function failure(source: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "Top100Ergonomics.g17", source }], ["lib"]);
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    return error.message;
  }
  assert.fail("the module should not check");
}

test("by_cases h : P opens the cases h : P and h : ¬P with bullets", () => {
  check(main + `
theorem split (x y : Set)
  shows x = y ∨ ¬(x = y)
proof
  by_cases h : x = y
  . left
    exact h
  . right
    exact h

theorem unnamed (x y : Set)
  shows x = y ∨ x ≠ y
proof
  by_cases x = y
  . left; exact h
  . right; exact h
`);
  const message = failure(main + `
theorem taken (x y : Set)
  requires h : x = x
  shows x = y ∨ ¬(x = y)
proof
  by_cases h : x = y
  . left; exact h
  . right; exact h
`);
  assert.match(message, /local proof h already exists/u);
});

test("typed binders without parentheses parse in ∃ and ∀, in statements, have types, and witness targets", () => {
  check(main + `
theorem existsTyped
  shows ∃ m n : ℕ, m + n = 3
proof
  witness 1
  witness 2
  compute

theorem forallTyped
  shows ∀ m n : ℕ, m + n = n + m
proof
  intros m hm n hn
  ring

theorem haveTyped (k : Nat)
  shows ∃ m : ℕ, m = k
proof
  have inner : ∃ m n : ℕ, m = k ∧ n = k
    witness k
    witness k
    constructor
    . rfl
    . rfl
  obtain ⟨m, mNat, n, nNat, mk, nk⟩ := inner
  witness m
  exact mk
`);
});

test("ring and ring_nf expand a literal power over ℕ, ℝ, ℤ, and a bundled ring", () => {
  check(`module Top100Ergonomics
import Grace.Cumulus.Nat.PowLemmas
import Grace.Cumulus.Real.Power
import Grace.Cumulus.Real.Natural

theorem natSquare (a b : Nat)
  shows (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2
proof
  ring

theorem natSixteen (a : Nat)
  shows a ^ 16 = a * a ^ 15
proof
  ring

theorem realSquare (a b : Real)
  shows (a + b) ^ 2 = a ^ 2 + (2:R) * a * b + b ^ 2
proof
  ring

theorem realNormalForm (a : Real)
  requires h : a ^ 3 = 8
  shows a * (a * a) = 8
proof
  ring_nf at h
  ring_nf
  exact h
`);
  check(`module Top100Ergonomics
import Grace.Cumulus.Int.Pow

theorem intSquare (z w : Integer)
  shows integerPow(z + w, 2) = integerPow(z, 2) + z * w + w * z + integerPow(w, 2)
proof
  ring
`);
  check(`module Top100Ergonomics
import Grace.Cumulus.Algebra.Ring
import Grace.Cumulus.Algebra.Group.Power

section S
variable (R : Set)
hypothesis ring : CommRing(R)

theorem bundledSquare (x y : R)
  shows monoidPow(Ring.mul(R), Ring.one(R), x + y, 2) = x * x + R[2] * (x * y) + y * y
proof
  ring
end S
`);
  // Above the bound the power stays an atom.
  const message = failure(`module Top100Ergonomics
import Grace.Cumulus.Nat.PowLemmas

theorem natSeventeen (a : Nat)
  shows a ^ 17 = a * a ^ 16
proof
  ring
`);
  assert.match(message, /pow\(a, 17\)/u);
});

const arithmetic = `module Top100Ergonomics
import Grace.Cumulus.Nat.Pow
import Grace.Cumulus.Nat.Subtraction
import Grace.Cumulus.Nat.Division

def falling (n m : Nat) → Nat
  | n, zero => 1
  | n, succ(m) => mul(falling(n, m), sub(n, m))
  descends m
`;

test("compute certifies closed order goals over ℕ and reports a false comparison with the values", () => {
  check(arithmetic + `
theorem orderCompute
  shows 2 * falling(365, 23) < 365 ^ 23
proof
  compute

theorem leCompute
  shows 2 * 3 ≤ 7
proof
  compute

theorem leEqual
  shows 2 * 3 ≤ 6
proof
  compute

theorem neCompute
  shows 2 * 3 ≠ 7
proof
  compute

theorem neReversed
  shows 7 ≠ 2 * 3
proof
  compute

theorem positive
  shows 0 < 12345678901234567890123456789012345678901234567890
proof
  compute
`);
  const message = failure(arithmetic + `
theorem wrong
  shows 7 < 2 * 3
proof
  compute
`);
  assert.match(message, /compute: 7 < 2 \* 3 is false; the sides evaluate to 7 and 6/u);
  const open = failure(main + `
theorem open (n : Nat)
  shows n < n + 1
proof
  compute
`);
  assert.match(open, /compute requires an equality goal, or a closed natural-number order goal/u);
});

test("typecheck types a numeral literal of any length at once, as Nat(k) and as k ∈ ℕ", () => {
  const digits = (count: number): string => Array.from({ length: count }, (_, index) => String((index * 7) % 9 + 1)).join("");
  check(main + `
theorem fifty
  shows Nat(${digits(50)})
proof
  typecheck

theorem mersenne
  shows Nat(340282366920938463463374607431768211455)
proof
  typecheck

theorem twoHundred
  shows Nat(${digits(200)})
proof
  typecheck

theorem member
  shows ${digits(50)} ∈ ℕ
proof
  typecheck
`);
});

test("natural subtraction, predecessor, remainder, and quotient evaluate natively", () => {
  const kernel = check(arithmetic + `
theorem gapCompute
  shows 365 ^ 23 - (2 * falling(365, 23) + 1) = 1250040748965601492022941694577238181855100962491293453124
proof
  compute

theorem remainderCompute
  shows 1000000007 % 97 = 1000000007 - 97 * quotientNat(1000000007, 97)
proof
  compute

theorem remainderByZero
  shows 5 % 0 = 5 ∧ quotientNat(5, 0) = 0
proof
  constructor
  . compute
  . compute

theorem predecessorOfZero
  shows predecessor(0) = 0 ∧ 3 - 5 = 0
proof
  constructor
  . compute
  . compute
`);
  const big = 123456789012345678901234567890n;
  const subtraction = evaluateNative(kernel, app("Grace.Cumulus.Nat.Subtraction.sub", nat(big), nat(1n)));
  assert.equal(subtraction.value, big - 1n);
  assert.ok(subtraction.stats.reductions < 10, `subtraction took ${subtraction.stats.reductions} reductions`);
  assert.ok(subtraction.definitions.includes("Grace.Cumulus.Nat.Subtraction.sub"));
  assert.ok(subtraction.definitions.includes("Grace.Core.Nat.Rec.predecessor"));
  const remainder = evaluateNative(kernel, app("Grace.Cumulus.Nat.Mod.mod", nat(big), nat(1000003n)));
  assert.equal(remainder.value, big % 1000003n);
  assert.ok(remainder.stats.reductions < 10, `remainder took ${remainder.stats.reductions} reductions`);
  const quotient = evaluateNative(kernel, app("Grace.Cumulus.Nat.Division.quotientNat", nat(big), nat(1000003n)));
  assert.equal(quotient.value, big / 1000003n);
  assert.ok(quotient.stats.reductions < 10, `quotient took ${quotient.stats.reductions} reductions`);
  const predecessor = evaluateNative(kernel, app("Grace.Core.Nat.Rec.predecessor", nat(big)));
  assert.equal(predecessor.value, big - 1n);
  assert.ok(predecessor.stats.reductions < 10, `predecessor took ${predecessor.stats.reductions} reductions`);
});

test("a with list supplies the conjuncts of a conjunction requirement in order", () => {
  check(main + `
theorem withConjunction (x A B : Set)
  requires inSpace : x ∈ A
  requires notInjective : ¬(x ∈ B)
  shows x ∈ A ∖ B
proof
  exact difference.membership.backward with inSpace, notInjective

theorem withConjunctionAt (x A B : Set)
  requires inSpace : x ∈ A
  requires notInjective : ¬(x ∈ B)
  shows x ∈ A ∖ B
proof
  have member := difference.membership.backward at
    A, B, x with inSpace, notInjective
  exact member
`);
  const message = failure(main + `
theorem withMismatch (x A B : Set)
  requires inSpace : x ∈ A
  requires other : x = x
  shows x ∈ A ∖ B
proof
  exact difference.membership.backward with inSpace, other
`);
  assert.match(message, /named premise inSpace \(x ∈ A\) matches no requirement; requirement 1 is x ∈ A ∧ x ∉ B/u);
});

test("a step in a bullet whose goal is already closed names the line that closed it", () => {
  const message = failure(`module Top100Ergonomics
import Grace.Cumulus.Nat.PowLemmas

theorem closedBullet (a : Nat)
  shows a ^ 2 = a * a ∧ a = a
proof
  constructor
  . simp [pow.two]
    exact pow.two
  . rfl
`);
  assert.match(message, /line 9: no goals remain in this case; line 8 \(simp \[pow\.two\]\) closed it, and the step does not apply to the next goal: pow\.two/u);
  // A step that does apply to the next goal still closes it, as library
  // proofs rely on.
  check(main + `
theorem fallthrough (x : Set)
  requires h : x = x
  shows x = x ∧ x = x
proof
  constructor
  . exact h
    exact h
`);
});
