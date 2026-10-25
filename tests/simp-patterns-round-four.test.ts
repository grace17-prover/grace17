// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A fourth round of simp and pattern semantics met while proving graph
// theory: a bare `simp` opens a difference and a singleton everywhere and
// settles the atoms from the context; destructuring, projections, `refine`,
// and `intro` go through the membership law of a set-builder definition;
// and a local fact whose predicate has an `iff` law applies through its
// universal side when the direct application fails.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { formatFormula } from "../src/pretty.ts";

const header = `module PatternsRoundFour
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Set.Powerset
import Grace.Cumulus.Nat.Parity

def reached (V F u : Set) : Set := { w ∈ V | w = u ∨ ∃ P ⊆ F, w ∈ P }
def guarded (V u : Set) : Set := { w ∈ V | w ∈ V → w = u }
`;

function check(body: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PatternsRoundFour.g17", source: header + body }], ["lib"]);
  return kernel;
}

function failure(body: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "PatternsRoundFour.g17", source: header + body }], ["lib"]);
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

test("a bare simp opens a difference by a singleton under a union and settles from the context", () => {
  check(`
theorem difference.under_union (C T e f : Set)
  requires inside : C ⊆ T ∪ {e}
  requires different : f ≠ e
  shows C ∖ {f} ⊆ (T ∖ {f}) ∪ {e}
proof
  simp

theorem difference.restored (T e f : Set)
  shows T ⊆ ((T ∖ {f}) ∪ {e}) ∪ {f}
proof
  simp

theorem difference.pointwise (T e f g : Set)
  requires inT : g ∈ T
  requires different : g ≠ f
  shows g ∈ T ∖ {f} ∨ g = e
proof
  simp

theorem difference.fact_closes (F e : Set)
  requires inRest : e ∈ F ∖ {e}
  shows ⊥
proof
  simp at inRest

theorem intersection.opened (A B x : Set)
  requires inA : x ∈ A
  requires inB : x ∈ B
  shows x ∈ A ∩ B ∖ {x} ∨ x ∈ A ∩ B
proof
  simp
`);
});

test("a bare simp closes a union with a singleton from a subset fact, and symmetric difference", () => {
  check(`
theorem union.singleton_goal (A B x a : Set)
  requires sub : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B ∪ {a}
proof
  simp

theorem union.singleton_subset (A B a : Set)
  requires sub : A ⊆ B
  shows A ⊆ B ∪ {a}
proof
  simp

theorem symmetric.membership_goal (A B x : Set)
  requires hA : x ∈ A
  requires hB : x ∉ B
  shows x ∈ A △ B
proof
  simp

theorem symmetric.membership_fact (A B x : Set)
  requires h : x ∈ A △ B
  requires hA : x ∈ A
  shows x ∉ B
proof
  simp at h
  intro hB
  simp [hB] at h
`);
});

test("rcases, obtain, cases, and projections open a set-builder membership through its law", () => {
  const kernel = check(`
theorem builder.rcases (V F u a : Set)
  requires member : a ∈ reached(V, F, u)
  shows a ∈ V
proof
  rcases member with ⟨vertex, _⟩
  exact vertex

theorem builder.obtain (V F u a : Set)
  requires member : a ∈ reached(V, F, u)
  shows a = u ∨ ∃ P ⊆ F, a ∈ P
proof
  obtain ⟨_, rest⟩ := member
  exact rest

theorem builder.rcases_deep (V F u a : Set)
  requires member : a ∈ reached(V, F, u)
  requires away : a ≠ u
  shows ∃ P ⊆ F, a ∈ P
proof
  rcases member with ⟨_, same | ⟨P, subset, inP⟩⟩
  . contradiction
  exact ⟨P, subset, inP⟩

theorem builder.projection (V F u a : Set)
  requires member : a ∈ reached(V, F, u)
  shows a ∈ V
proof
  exact member.left

theorem builder.projection_right (V F u a : Set)
  requires member : a ∈ reached(V, F, u)
  shows a = u ∨ ∃ P ⊆ F, a ∈ P
proof
  exact member.right
`);
  assert.deepEqual(goalsAfter(kernel, "PatternsRoundFour.builder.rcases", 0), ["a ∈ V"]);
});

test("refine, exact, and intro build a set-builder membership through its law", () => {
  check(`
theorem builder.refine (V F u a : Set)
  requires vertex : a ∈ V
  requires start : a = u
  shows a ∈ reached(V, F, u)
proof
  refine ⟨vertex, _⟩
  left
  exact start

theorem builder.exact (V F u a : Set)
  requires vertex : a ∈ V
  requires rest : a = u ∨ ∃ P ⊆ F, a ∈ P
  shows a ∈ reached(V, F, u)
proof
  exact ⟨vertex, rest⟩

theorem builder.intro (V u a : Set)
  requires vertex : a ∈ V
  requires start : a = u
  shows a ∈ guarded(V, u)
proof
  refine ⟨vertex, _⟩
  intro _
  exact start
`);
});

test("a local fact with an iff law applies through its universal side", () => {
  check(`
theorem disjoint.applied (X Y v : Set)
  requires disjoint : Disjoint(X, Y)
  requires inX : v ∈ X
  requires inY : v ∈ Y
  shows ⊥
proof
  exact disjoint with v, inX, inY

theorem disjoint.have (X Y v : Set)
  requires disjoint : Disjoint(X, Y)
  requires inX : v ∈ X
  shows v ∉ Y
proof
  have apart := disjoint with v, inX
  exact apart
`);
  assert.match(failure(`
theorem disjoint.misapplied (X Y v : Set)
  requires disjoint : Disjoint(X, Y)
  requires inX : v ∈ X
  shows ⊥
proof
  exact disjoint with v, inX, inX
`), /inX|argument|expected/);
});
