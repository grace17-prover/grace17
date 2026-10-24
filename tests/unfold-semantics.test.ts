// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The rule `unfold` follows: the named definition is opened at every
// instance of the goal or the fact named by `at`, under any connective or
// relation and inside arguments, in one call, and nothing else changes; in
// particular local equalities are never applied, so a proof is not
// sensitive to which equalities happen to be in context. `simp [P] at h`
// with a predicate definition P opens it wherever h mentions it, and
// `exact` bridges a predicate definition nested under the connectives.
// Each case was met while proving graph theory.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { formatFormula } from "../src/pretty.ts";

const header = `module UnfoldSemantics
import Grace.Cumulus.Nat.Parity
import Grace.Cumulus.Set.Algebra
import Grace.Cumulus.Cardinal.Enumeration

predicate EvenSet (A : Set) := Even(cardinality(A))
def incidentEnds (leftEnd rightEnd F v : Set) : Set := (F ∩ {v}) ∪ (leftEnd ∩ rightEnd)
def degreeIn (leftEnd rightEnd F v : Set) : Set := cardinality(incidentEnds(leftEnd, rightEnd, F, v))
`;

function check(body: string): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "UnfoldSemantics.g17", source: header + body }], ["lib"]);
  return kernel;
}

function failure(body: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "UnfoldSemantics.g17", source: header + body }], ["lib"]);
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

test("unfold P at h opens every occurrence of P in one call, under ↔ included", () => {
  const kernel = check(`
theorem parity.unfolded (X Y : Set)
  requires parity : EvenSet(X △ Y) ↔ (EvenSet(X) ↔ EvenSet(Y))
  shows Even(cardinality(X △ Y)) ↔ (Even(cardinality(X)) ↔ Even(cardinality(Y)))
proof
  unfold EvenSet at parity
  exact parity
`);
  const trace = kernel.theoremTacticTraces.get("UnfoldSemantics.parity.unfolded");
  assert.deepEqual(trace?.steps.map(step => step.command), ["unfold EvenSet at parity", "exact parity"]);
});

test("unfold opens every occurrence in the goal, under ≤ and inside arguments", () => {
  const kernel = check(`
theorem degree.monotone (l r F G v : Set)
  requires h : cardinality(incidentEnds(l, r, F, v)) ≤ cardinality(incidentEnds(l, r, G, v))
  shows degreeIn(l, r, F, v) ≤ degreeIn(l, r, G, v)
proof
  unfold degreeIn
  exact h
`);
  assert.deepEqual(goalsAfter(kernel, "UnfoldSemantics.degree.monotone", 0),
    ["cardinality(incidentEnds(l, r, F, v)) ≤ cardinality(incidentEnds(l, r, G, v))"]);
});

test("unfold never rewrites with local equalities, so a following rw finds its instance", () => {
  const kernel = check(`
theorem degree.empty (l r v : Set)
  requires none : incidentEnds(l, r, ∅, v) = ∅
  shows degreeIn(l, r, ∅, v) = cardinality(∅)
proof
  unfold degreeIn
  rw none

theorem degree.split (l r F G v : Set)
  requires split : incidentEnds(l, r, F △ G, v) = incidentEnds(l, r, F, v) △ incidentEnds(l, r, G, v)
  shows degreeIn(l, r, F △ G, v) = cardinality(incidentEnds(l, r, F, v) △ incidentEnds(l, r, G, v))
proof
  unfold degreeIn
  rw split
`);
  // The equality in context is not applied: the exposed body still names
  // the instance `none` rewrites.
  assert.deepEqual(goalsAfter(kernel, "UnfoldSemantics.degree.empty", 0),
    ["cardinality(incidentEnds(l, r, ∅, v)) = cardinality(∅)"]);
  assert.deepEqual(goalsAfter(kernel, "UnfoldSemantics.degree.split", 0),
    ["cardinality(incidentEnds(l, r, symmetricDifference(F, G), v)) = " +
      "cardinality(symmetricDifference(incidentEnds(l, r, F, v), incidentEnds(l, r, G, v)))"]);
});

test("simp with a local equality remains the explicit way to use context facts after unfold", () => {
  check(`
theorem degree.empty_by_simp (l r v : Set)
  requires none : incidentEnds(l, r, ∅, v) = ∅
  shows degreeIn(l, r, ∅, v) = cardinality(∅)
proof
  simp [degreeIn, none]
`);
});

test("unfold reports a definition the goal or fact does not mention", () => {
  assert.match(failure(`
theorem degree.nothing (l r F v : Set)
  requires h : cardinality(incidentEnds(l, r, F, v)) = cardinality(incidentEnds(l, r, F, v))
  shows cardinality(incidentEnds(l, r, F, v)) = cardinality(incidentEnds(l, r, F, v))
proof
  unfold degreeIn
  exact h
`), /unfold degreeIn finds nothing to unfold in the goal/);
  assert.match(failure(`
theorem degree.nothing_at (l r F v : Set)
  requires h : cardinality(incidentEnds(l, r, F, v)) = cardinality(incidentEnds(l, r, F, v))
  shows cardinality(incidentEnds(l, r, F, v)) = cardinality(incidentEnds(l, r, F, v))
proof
  unfold degreeIn at h
  exact h
`), /unfold degreeIn finds nothing to unfold in h : /);
});

test("simp [P] at h with a predicate definition opens it wherever h mentions it", () => {
  const kernel = check(`
theorem parity.simplified (X Y : Set)
  requires parity : EvenSet(X △ Y) ↔ (EvenSet(X) ↔ EvenSet(Y))
  shows Even(cardinality(X △ Y)) ↔ (Even(cardinality(X)) ↔ Even(cardinality(Y)))
proof
  simp [EvenSet] at parity
  exact parity

theorem parity.goal (X Y : Set)
  requires parity : Even(cardinality(X △ Y)) ↔ (Even(cardinality(X)) ↔ Even(cardinality(Y)))
  shows EvenSet(X △ Y) ↔ (EvenSet(X) ↔ EvenSet(Y))
proof
  simp [EvenSet]
`);
  const trace = kernel.theoremTacticTraces.get("UnfoldSemantics.parity.simplified");
  assert.deepEqual(trace?.steps.map(step => step.command), ["simp [EvenSet] at parity", "exact parity"]);
});

test("exact bridges a predicate definition nested under ↔", () => {
  check(`
theorem parity.exact (X Y : Set)
  requires parity : EvenSet(X △ Y) ↔ (EvenSet(X) ↔ EvenSet(Y))
  shows Even(cardinality(X △ Y)) ↔ (Even(cardinality(X)) ↔ Even(cardinality(Y)))
proof
  exact parity

theorem parity.exact_folded (X Y : Set)
  requires parity : Even(cardinality(X △ Y)) ↔ (Even(cardinality(X)) ↔ Even(cardinality(Y)))
  shows EvenSet(X △ Y) ↔ (EvenSet(X) ↔ EvenSet(Y))
proof
  exact parity
`);
});

test("unfold reaches an instance under a binder that mentions the bound variable, in goals and facts", () => {
  check(`
theorem evenSet.all (𝒜 : Set)
  requires h : ∀ A ∈ 𝒜, EvenSet(A) ∨ ¬EvenSet(A)
  shows ∀ A ∈ 𝒜, Even(cardinality(A)) ∨ ¬Even(cardinality(A))
proof
  unfold EvenSet at h
  exact h

theorem evenSet.all_goal (𝒜 : Set)
  requires h : ∀ A ∈ 𝒜, Even(cardinality(A)) → Even(cardinality(A))
  shows ∀ A ∈ 𝒜, EvenSet(A) → EvenSet(A)
proof
  unfold EvenSet
  exact h
`);
});
