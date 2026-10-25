// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A third round of simp and arith semantics met while proving graph
// theory: closed numerals are evaluated inside any subformula and after a
// rule list; a rule list that makes progress leaves its residue as the
// goal; a fact named among the rules rewrites its atom to ⊤ and its
// negation to ⊥ everywhere, under binders and inside opened set-builder
// bodies, and the truth values are absorbed; a fact simplified to ⊥
// closes the goal; and arith proves an equality from two opposite bounds
// after substituting local equations into them, with succ read inside
// comparisons.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { formatFormula } from "../src/pretty.ts";

const header = `module SimpRoundThree
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Set.Powerset
import Grace.Cumulus.Nat.Parity
import Grace.Cumulus.Nat.ParityLemmas
import Grace.Cumulus.Cardinal.Counting
import Grace.Cumulus.Cardinal.Pigeonhole
import Grace.Cumulus.Nat.Order

predicate Linked (F a b : Set) := a ∈ F ∧ b ∈ F
def inside (F X : Set) : Set := { e ∈ F | e ∈ X }
def insideTwice (F X : Set) : Set := { e ∈ F | e ∈ X ∧ e ∈ F }
def shortIn (V : Set, k : Nat) : Set := { w ∈ V | k ≤ k + 1 }
def longIn (V : Set, k : Nat) : Set := { w ∈ V | k ≤ k + 2 }
`;

function check(body: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "SimpRoundThree.g17", source: header + body }], ["lib"]);
  return kernel;
}

function failure(body: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "SimpRoundThree.g17", source: header + body }], ["lib"]);
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    return error.message;
  }
  assert.fail("the module should not check");
}

/** The goals after the step at `index` of a theorem's trace, printed. */
function goalsAfter(kernel: ReturnType<typeof createZfKernel>, theorem: string, index: number): string[] {
  const trace = kernel.theoremTacticTraces.get(theorem);
  assert.ok(trace, `no trace for ${theorem}`);
  const step = trace.steps[index];
  assert.ok(step, `no step ${index} in ${theorem}`);
  return step.after.goals.map(goal => formatFormula(goal.goal));
}

test("closed numerals are evaluated after a rule list and inside any subformula", () => {
  check(`
theorem numeral.after_rule (x : Nat)
  requires h : x = 2
  shows x = 1 + 1
proof
  simp [h]

theorem numeral.under_iff (a b X : Set)
  requires ha : a ∈ X
  requires hb : b ∈ X
  shows 1 + 1 = 1 ↔ (a ∈ X ∧ b ∉ X) ∨ (b ∈ X ∧ a ∉ X)
proof
  simp [ha, hb]

theorem numeral.under_or (a X : Set)
  requires ha : a ∈ X
  shows 1 + 1 = 3 ∨ (a ∈ X ∧ ¬(2 = 1 + 2))
proof
  simp [ha]
`);
});

test("simp with rules leaves its residue as the goal when it made progress", () => {
  const kernel = check(`
theorem residue.kept (V e leftEnd rightEnd : Set, k : Nat)
  requires leftV : leftEnd(e) ∈ V
  requires rightV : rightEnd(e) ∈ V
  shows leftEnd(e) ∈ V ∧ k ≤ k + 1 ↔ rightEnd(e) ∈ V ∧ k ≤ k + 2
proof
  simp [leftV, rightV]
  constructor
  . intro bound
    linarith
  . intro bound
    linarith

theorem residue.opened (V e leftEnd rightEnd : Set, k : Nat)
  requires leftV : leftEnd(e) ∈ V
  requires rightV : rightEnd(e) ∈ V
  shows leftEnd(e) ∈ shortIn(V, k) ↔ rightEnd(e) ∈ longIn(V, k)
proof
  simp [shortIn, longIn, leftV, rightV]
  constructor
  . intro bound
    linarith
  . intro bound
    linarith
`);
  assert.deepEqual(goalsAfter(kernel, "SimpRoundThree.residue.kept", 0), ["k ≤ k + 1 ↔ k ≤ k + 2"]);
  assert.deepEqual(goalsAfter(kernel, "SimpRoundThree.residue.opened", 0), ["k ≤ k + 1 ↔ k ≤ k + 2"]);
  assert.match(failure(`
theorem residue.none (F e u : Set)
  requires other : e ∈ F
  shows Linked(F, e, u) ↔ Linked(F, u, e)
proof
  simp [other]
`), /settle did not close the logical goal/);
});

test("a fact in the rule list rewrites its atom to ⊤ inside opened bodies and under binders", () => {
  const kernel = check(`
theorem truth.opened (F X e : Set)
  requires he : e ∈ F
  shows e ∈ inside(F, X) ↔ e ∈ insideTwice(F, X)
proof
  simp [inside, insideTwice, he]

theorem truth.negative (F X e : Set)
  requires he : e ∉ F
  shows e ∈ inside(F, X) ↔ e ∈ insideTwice(F, X)
proof
  simp [inside, insideTwice, he]

theorem truth.under_binder (F X : Set)
  requires all : ∀ x, x ∈ F
  shows ∀ y, y ∈ inside(F, X) ↔ y ∈ X
proof
  simp [inside, all]

theorem truth.residue (F e : Set, k : Nat)
  requires he : e ∈ F
  shows e ∈ shortIn(F, k) ↔ e ∈ longIn(F, k)
proof
  simp [shortIn, longIn, he]
  constructor
  . intro bound
    linarith
  . intro bound
    linarith

theorem truth.implication (F e : Set, P : Set)
  requires he : e ∈ F
  requires hp : P ∈ F
  shows (e ∈ F → P ∈ F) ∧ (P ∈ F ↔ e ∈ F)
proof
  simp [he, hp]
`);
  assert.deepEqual(goalsAfter(kernel, "SimpRoundThree.truth.residue", 0), ["k ≤ k + 1 ↔ k ≤ k + 2"]);
});

test("a fact simplified to ⊥ closes the goal, and parity facts decide a goal", () => {
  const kernel = check(`
theorem bottom.disequality (F e : Set)
  requires h : e ∈ F ∖ {e}
  shows ⊥
proof
  simp [difference.singleton_membership] at h

theorem bottom.empty (a b : Set)
  requires sides : a ∈ ∅ ∧ b = b
  shows b ∈ {a}
proof
  simp [set.empty] at sides

theorem bottom.conjunct (F e : Set)
  requires h : e ∈ F ∧ e ≠ e
  shows e ∈ ∅
proof
  simp at h

theorem parity.decided
  shows Even(0) ∧ ¬Even(1) ∧ (Even(1) ↔ ¬Even(0))
proof
  simp [Even.zero, Even.not_one]
`);
  assert.deepEqual(goalsAfter(kernel, "SimpRoundThree.bottom.disequality", 0), []);
});

test("arith proves an equality from opposite bounds after substituting a local equation", () => {
  check(`
theorem bounds.substituted (T V : Set, c : Nat)
  requires finiteT : Finite(T)
  requires finiteV : Finite(V)
  requires upper : cardinality(T) + c ≤ cardinality(V)
  requires lower : cardinality(V) ≤ cardinality(T) + c
  requires one : c = 1
  shows cardinality(T) + 1 = cardinality(V)
proof
  arith

theorem bounds.opaque (T V c : Set)
  requires finiteT : Finite(T)
  requires finiteV : Finite(V)
  requires upper : cardinality(T) + c ≤ cardinality(V)
  requires lower : cardinality(V) ≤ cardinality(T) + c
  requires one : c = 1
  shows cardinality(T) + 1 = cardinality(V)
proof
  arith
`);
});

test("arith and linarith read succ inside comparisons", () => {
  check(`
theorem succ.arith (k n : Nat)
  requires below : k < succ(n)
  shows k + 1 ≤ n + 1
proof
  arith

theorem succ.linarith (k n : Nat)
  requires below : k < succ(n)
  shows k + 1 ≤ n + 1
proof
  linarith

theorem succ.goal (k n : Nat)
  requires below : k ≤ n
  shows succ(k) ≤ succ(n)
proof
  linarith
`);
});
