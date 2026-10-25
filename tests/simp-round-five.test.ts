// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A fifth round of simp, arith, and tauto semantics met while proving the
// cycle double cover theorem: an equation between distinct closed literals,
// and an equation of ordered pairs with distinct literal coordinates, is
// decided in a fact and in a goal, in every position; arith and linarith
// use disequalities between the atoms of the comparison facts as case
// splits over the naturals; the cost of simp depends on the goal and the
// named rules rather than on the number of unrelated hypotheses; and tauto
// opens set-builder membership and a bounded existential over a union.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";

const header = `module SimpRoundFive
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Set.Powerset
import Grace.Cumulus.Set.Relation
import Grace.Cumulus.Nat.Order
import Grace.Cumulus.Nat.OrderLemmas
import Grace.Cumulus.Cardinal.Counting
import Grace.Cumulus.Cardinal.Pigeonhole
import Grace.Cumulus.Cardinal.DoubleCounting

def rowSet (y e : Set) : Set := { i ∈ 3 | (e, i) ∈ y }
def covered (P S G : Set) : Set := { x ∈ S | ∃ i ∈ G, (i, x) ∈ P }
`;

function check(body: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "SimpRoundFive.g17", source: header + body }], ["lib"]);
  return kernel;
}

function failure(body: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "SimpRoundFive.g17", source: header + body }], ["lib"]);
  } catch (error) {
    assert.ok(error instanceof SurfaceError, String(error));
    return error.message;
  }
  assert.fail("the module should not check");
}

test("an equation between distinct closed literals is decided in facts and goals", () => {
  check(`
theorem literal.at_fact (x A : Set)
  requires h : 0 = 1
  shows x ∈ A
proof
  simp at h

theorem literal.at_fact_mirror (x A : Set)
  requires h : 1 = 0
  shows x ∈ A
proof
  simp at h

theorem literal.at_fact_inside (x A : Set)
  requires h : x ∈ A ∧ (1 = 0 ∨ 2 = 2 ∧ 0 = 1)
  shows x ∉ A
proof
  simp at h

theorem literal.in_residue (x A : Set)
  requires hx : x ∈ A
  shows (x ∈ A ∧ ¬(0 = 1)) ∨ 1 = 0
proof
  simp [hx]

theorem literal.goal
  shows 1 ≠ 0 ∧ ¬(0 = 1) ∧ 0 = 0
proof
  simp
`);
});

test("an equation of ordered pairs with distinct literal coordinates is false by default", () => {
  check(`
theorem pair.at_fact (e k x A : Set)
  requires h : (0, e) = (1, k)
  shows x ∈ A
proof
  simp at h

theorem pair.at_fact_second (e k x A : Set)
  requires h : (e, 1) = (k, 0)
  shows x ∈ A
proof
  simp at h

theorem pair.goal (e k : Set)
  shows (0, e) ≠ (1, k)
proof
  simp

theorem pair.in_residue (e k x A : Set)
  requires hx : x ∈ A
  shows (x ∈ A ∧ (e, 0) ≠ (k, 1)) ∨ (0, e) = (1, k)
proof
  simp [hx]

theorem pair.nested (e k x A : Set)
  requires hx : x ∈ A
  shows x ∈ A ∧ ((e, 0), k) ≠ ((e, 1), k)
proof
  simp [hx]
`);
  assert.match(failure(`
theorem pair.open (e k x A : Set)
  requires h : (0, e) = (0, k)
  shows x ∈ A
proof
  simp at h
`), /goal remains/);
});

test("arith and linarith use disequalities of the comparison atoms as case splits", () => {
  check(`
theorem two_of_ne (d : Nat)
  requires notZero : d ≠ 0
  requires notOne : d ≠ 1
  shows 2 ≤ d
proof
  arith

theorem two_of_ne.linarith (d : Nat)
  requires notZero : d ≠ 0
  requires notOne : d ≠ 1
  shows 2 ≤ d
proof
  linarith

theorem two_of_ne.cardinality (F : Set)
  requires finite : Finite(F)
  requires notZero : cardinality(F) ≠ 0
  requires notOne : cardinality(F) ≠ 1
  shows 2 ≤ cardinality(F)
proof
  arith

theorem one_of_bounds (a b : Nat)
  requires lower : a ≤ b
  requires upper : b ≤ a + 1
  requires apart : a ≠ b
  shows b = a + 1
proof
  arith

theorem absurd_of_ne (d : Nat)
  requires small : d < 2
  requires notZero : d ≠ 0
  requires notOne : d ≠ 1
  shows ⊥
proof
  arith
`);
  assert.match(failure(`
theorem two_of_ne.unrelated (d x y : Nat)
  requires notZero : d ≠ 0
  requires apart : x ≠ y
  shows 2 ≤ d
proof
  arith
`), /no linear arithmetic contradiction/);
});

test("simp's cost depends on the goal and the rules, not on unrelated hypotheses", () => {
  const unrelated = Array.from({ length: 40 }, (_, index) =>
    `  requires h${index} : ∀ x ∈ A${index}, x ∈ B${index} ∧ (x ∈ C${index} ∨ x ∉ D${index})`).join("\n");
  const sets = Array.from({ length: 40 }, (_, index) => `A${index} B${index} C${index} D${index}`).join(" ");
  const started = performance.now();
  check(`
theorem disjoint.fresh (Q C e f ${sets} : Set)
  requires eFresh : ¬e ∈ Q
  requires QsubC : Q ⊆ C
  requires he : e ∈ C
  requires hf : f ∈ C
${unrelated}
  shows Disjoint(Q, {e}) ∧ (Q ∪ {e}) ∪ {f} ⊆ C
proof
  constructor
  . simp [Disjoint.iff, eFresh]
  . simp [QsubC, he, hf]
`);
  const elapsed = performance.now() - started;
  assert.ok(elapsed < 8_000, `the large context took ${Math.round(elapsed)} ms`);
});

test("tauto opens set-builder membership and a bounded existential over a union", () => {
  check(`
theorem fiber.atom (A C r c : Set)
  requires h : c ∈ fiber(A, C, r) ∨ (c ∈ C ∧ (r, c) ∈ A)
  shows (r, c) ∈ A ∧ c ∈ C
proof
  tauto

theorem fiber.atom_backward (A C r c : Set)
  requires hc : c ∈ C
  requires h : (r, c) ∈ A
  shows c ∈ fiber(A, C, r)
proof
  tauto

theorem union.witness (P G a x : Set)
  requires h : (a, x) ∈ P
  shows ∃ i ∈ G ∪ {a}, (i, x) ∈ P
proof
  tauto

theorem covered.member (P S G a x : Set)
  requires hs : x ∈ S
  requires h : (a, x) ∈ P
  shows x ∈ covered(P, S, G ∪ {a})
proof
  tauto
`);
});
