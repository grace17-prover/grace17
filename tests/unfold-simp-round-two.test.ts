// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A second round of unfold and simp semantics met while proving graph
// theory: set-builder definitions open at their membership instances and
// report precisely otherwise; membership rules reach under binders in a
// fact; a comprehension may stand as an argument in a definition body; a
// rewrite that leaves a reflexive equivalence closes its bullet; `simp at`
// applies its rules as thoroughly as on the goal, with the empty-set law,
// and a fact brought to ⊥ closes the goal;
// `simp` finishes a propositional residue and evaluates closed numerals;
// and a `by` clause may follow a wrapped `have` proposition.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { formatFormula } from "../src/pretty.ts";

const header = `module UnfoldRoundTwo
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Set.Powerset
import Grace.Cumulus.Nat.Parity

def classesContaining (P v : Set) : Set := { X ∈ P | v ∈ X }
def classOf (P v : Set) : Set := ⋃(classesContaining(P, v))
`;

function check(body: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "UnfoldRoundTwo.g17", source: header + body }], ["lib"]);
  return kernel;
}

function failure(body: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "UnfoldRoundTwo.g17", source: header + body }], ["lib"]);
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

test("unfold of a set-builder opens its membership instances in a goal and a fact", () => {
  check(`
theorem builder.fact (P v z : Set)
  requires h : z ∈ classesContaining(P, v)
  shows z ∈ P ∧ v ∈ z
proof
  unfold classesContaining at h
  exact h

theorem builder.goal (P v z : Set)
  requires h : z ∈ P ∧ v ∈ z
  shows z ∈ classesContaining(P, v)
proof
  unfold classesContaining
  exact h

theorem builder.under_exists (P v z : Set)
  requires h : ∃ A ∈ classesContaining(P, v), z ∈ A
  shows ∃ X ∈ P, v ∈ X ∧ z ∈ X
proof
  unfold classesContaining at h
  obtain ⟨X, ⟨inP, vX⟩, zX⟩ := h
  exact ⟨X, inP, vX, zX⟩
`);
});

test("unfold of a set-builder with no membership instance names the idiom", () => {
  assert.match(failure(`
theorem builder.subset (P v : Set)
  shows classesContaining(P, v) ⊆ P
proof
  unfold classesContaining
  intro x hx
  exact hx.left
`), /classesContaining is a set-builder; unfold opens x ∈ classesContaining\(…\) instances, use ext to reason about classesContaining\(…\) as a set/);
});

test("simp [f] at h with a set-builder opens its membership under an existential", () => {
  check(`
theorem builder.simp_at (P v z : Set)
  requires h : ∃ A ∈ classesContaining(P, v), z ∈ A
  shows ∃ X ∈ P, v ∈ X ∧ z ∈ X
proof
  simp [classesContaining] at h
  obtain ⟨X, ⟨inP, vX⟩, zX⟩ := h
  exact ⟨X, inP, vX, zX⟩

theorem builder.membership_at (P v z : Set)
  requires h : ∃ A ∈ classesContaining(P, v), z ∈ A
  shows ∃ X ∈ P, v ∈ X ∧ z ∈ X
proof
  simp [classesContaining.membership] at h
  obtain ⟨X, ⟨inP, vX⟩, zX⟩ := h
  exact ⟨X, inP, vX, zX⟩

theorem classOf.membership (P v z : Set)
  shows z ∈ classOf(P, v) ↔ ∃ X ∈ P, v ∈ X ∧ z ∈ X
proof
  simp [classOf, union.membership, classesContaining.membership]
`);
});

test("a comprehension as an argument in a definition body becomes a named helper set", () => {
  const kernel = check(`
def classOf2 (P v : Set) : Set := ⋃({ X ∈ P | v ∈ X })

theorem classOf2.membership (P v z : Set)
  shows z ∈ classOf2(P, v) ↔ ∃ X ∈ P, v ∈ X ∧ z ∈ X
proof
  simp [classOf2, union.membership, classOf2.family.membership]
`);
  assert.ok(kernel.definitions.has("UnfoldRoundTwo.classOf2.family"));
});

test("rw leaving a reflexive equivalence closes its bullet branch", () => {
  check(`
theorem rewrite.iff_refl (X Y : Set)
  requires loop : X = Y
  shows (X ∈ X ↔ Y ∈ X) ∧ (X ∈ X ↔ Y ∈ X)
proof
  constructor
  . rw loop
  . rw [loop]
`);
});

test("simp at applies every rule at depth, with the empty-set law", () => {
  const kernel = check(`
theorem simp_at.union (a b x : Set)
  requires hf : x ∈ {a} ∪ {b}
  shows x = a ∨ x = b
proof
  simp [union2.membership, singleton.membership] at hf
  exact hf

theorem simp_at.nested (x a b c : Set)
  requires h : x ∈ ({a} ∪ {b}) ∩ {c}
  shows (x = a ∨ x = b) ∧ x = c
proof
  simp [intersection.membership, union2.membership, singleton.membership] at h
  exact h

theorem simp_at.empty (a b : Set)
  requires sides : a ∈ ∅ ∧ b = b
  shows ⊥
proof
  simp [set.empty] at sides

theorem simp_goal.empty (a b : Set)
  shows a ∈ {b} ∩ ∅ ↔ ⊥
proof
  simp [intersection.membership]
`);
  assert.deepEqual(goalsAfter(kernel, "UnfoldRoundTwo.simp_at.empty", 0), []);
});

test("simp finishes a propositional residue and evaluates closed numerals", () => {
  check(`
theorem simp.residue (x a b c : Set)
  requires h : x ∈ ({a} ∪ {b}) ∩ {c}
  shows (x = a ∧ x = c) ∨ (x = b ∧ x = c)
proof
  simp [intersection.membership, union2.membership, singleton.membership] at h
  simp [h]

theorem simp.numerals
  shows 1 + 1 = 0 ∨ 1 + 1 = 1 ∨ 1 + 1 = 2
proof
  simp
`);
});

test("a by clause may begin the line after a wrapped have proposition", () => {
  check(`
theorem wrapped.by (P v z : Set)
  requires h : z ∈ P
  shows z ∈ P ∨ v ∈ P ∨ z ∈ P ∨ v ∈ P
proof
  have k : z ∈ P ∨ v ∈ P ∨
    z ∈ P ∨ v ∈ P
    by left; exact h
  exact k
`);
});
