// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Perfect sets of reals (Topology/Real): a nonempty perfect subset of ℝ is
// uncountable, by Cantor's nested intervals chosen through a choice
// function, so every closed set of reals is countable or contains an
// uncountable perfect set. The modules are checked through the machine
// interface's check method with the audit attached: every theorem is
// proved, the statements print as written, the nested-interval machinery
// is ZF, and the uncountability theorems use the axiom of choice and
// nothing beyond ZF.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.Topology.Real.";
const modules = [
  "Topology/Real/NestedChoice",
  "Topology/Real/PerfectSets",
];

interface Audit {
  complete: boolean;
  hereditary: string[];
}

interface Theorem {
  name: string;
  status: string;
  statement?: string;
  sorries: unknown[];
  audit?: Audit;
}

interface CheckResult {
  status: string;
  theorems: Theorem[];
  sorries: unknown[];
}

// One workspace holds both modules, so the environment is loaded once and
// every theorem of the two files is reported with its audit.
let checked: CheckResult | undefined;

function perfectSets(): CheckResult {
  if (!checked) {
    checked = callMachineMethod("check", {
      files: modules.map(module => ({ name: `lib/Grace/Cumulus/${module}.g17` })),
      audit: true,
    }) as CheckResult;
  }
  return checked;
}

function theorem(name: string): Theorem {
  const found = perfectSets().theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of the perfect-set development`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;
const choiceAxiom = "set.choice";

test("the perfect-set modules check with every theorem proved", t => {
  const result = perfectSets();
  assert.equal(result.status, "checked");
  assert.deepEqual(result.sorries, []);
  const unproved = result.theorems.filter(item => item.status !== "proved").map(item => item.name);
  assert.deepEqual(unproved, []);
  const admitted = result.theorems.filter(item => item.sorries.length > 0).map(item => item.name);
  assert.deepEqual(admitted, []);
  t.diagnostic(`${result.theorems.length} declarations checked across ${modules.length} modules`);
});

test("the statements print as written", () => {
  const expected: Record<string, string> = {
    "NestedChoice.centeredInterval.dist_membership":
      "∀ X, ∀ C E : ℝ, X ∈ centeredInterval(C, E) ↔ X ∈ ℝ ∧ dist(X, C) ≤ E",
    "NestedChoice.shrinkStage.equation":
      "∀ P f c, ∀ n : ℕ, shrinkStage(P, f, c, n) = c(shrinkCandidates(P, f, shrinkRegion(P, f, c, n), n))",
    "NestedChoice.shrinkStage.member":
      "∀ P f c, ∀ n : ℕ, SubsetChoice(c, ℝ × ℝ) → ShrinkSteps(P, f) → " +
      "shrinkStage(P, f, c, n) ∈ shrinkCandidates(P, f, shrinkRegion(P, f, c, n), n)",
    "NestedChoice.shrink.nested":
      "∀ P, ∀ f, ∀ c, SubsetChoice(c, ℝ × ℝ) → ShrinkSteps(P, f) → NestedClosedIntervals(shrinkLeft(P, f, c), shrinkRight(P, f, c))",
    "NestedChoice.shrink.common_point":
      "∀ P, ∀ f, ∀ c, SubsetChoice(c, ℝ × ℝ) → ShrinkSteps(P, f) → ∃ L ∈ ℝ, ∀ n ∈ ℕ, L ∈ shrinkInterval(P, f, c, n)",
    "NestedChoice.shrink.escapes":
      "∀ P, ∀ (f : P → ℕ), ∀ c L, SubsetChoice(c, ℝ × ℝ) → ShrinkSteps(P, f) → " +
      "(∀ n ∈ ℕ, L ∈ shrinkInterval(P, f, c, n)) → L ∉ P",
    "NestedChoice.harmonicTerms.below": "∀ E : ℝ, 0 < E → ∃ n ∈ ℕ, harmonicTermsₙ < E",
    "PerfectSets.Perfect.ball_meets":
      "∀ P, ∀ C E : ℝ, Perfect(ℝ, realTopology, P) → C ∈ P → 0 < E → ∃ D ∈ P, D ∈ openBall(C, E) ∧ D ≠ C",
    "PerfectSets.Perfect.shrink_candidate":
      "∀ P f I, ∀ n : ℕ, ∀ C E : ℝ, Perfect(ℝ, realTopology, P) → InjectiveBetween(f, P, ℕ) → C ∈ P → 0 < E → " +
      "centeredInterval(C, E) ⊆ I → Nonempty(shrinkCandidates(P, f, I, n))",
    "PerfectSets.Perfect.shrink_steps":
      "∀ P, ∀ f, Perfect(ℝ, realTopology, P) → InjectiveBetween(f, P, ℕ) → Nonempty(P) → ShrinkSteps(P, f)",
    "PerfectSets.perfect.uncountable":
      "∀ P, Perfect(ℝ, realTopology, P) → Nonempty(P) → ¬Countable(P)",
    "PerfectSets.reals.kernel_uncountable":
      "∀ A, IsClosed(ℝ, realTopology, A) → Nonempty(perfectKernel(ℝ, realTopology, A)) → " +
      "¬Countable(perfectKernel(ℝ, realTopology, A))",
    "PerfectSets.closed.countable_or_uncountable_perfect":
      "∀ A, IsClosed(ℝ, realTopology, A) → Countable(A) ∨ " +
      "∃ P, Nonempty(P) ∧ Perfect(ℝ, realTopology, P) ∧ P ⊆ A ∧ ¬Countable(P)",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("the nested-interval machinery over a given choice function is ZF", t => {
  for (const name of [
    "NestedChoice.shrinkStage.member",
    "NestedChoice.shrink.nested",
    "NestedChoice.shrink.common_point",
    "NestedChoice.shrink.escapes",
    "NestedChoice.harmonicTerms.below",
    "PerfectSets.Perfect.shrink_candidate",
    "PerfectSets.Perfect.shrink_steps",
  ]) {
    assert.equal(theorem(name).status, "proved", name);
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => /sorry|globalChoice|choice/u.test(axiom)), [], name);
    assert.deepEqual(axioms.hereditary.filter(axiom => !zfAxioms.test(axiom)), [], name);
    t.diagnostic(`${name} axioms: ${axioms.hereditary.join(", ")}`);
  }
});

test("the uncountability theorems use the axiom of choice and nothing beyond ZF", t => {
  for (const name of [
    "PerfectSets.perfect.uncountable",
    "PerfectSets.reals.kernel_uncountable",
    "PerfectSets.closed.countable_or_uncountable_perfect",
  ]) {
    assert.equal(theorem(name).status, "proved", name);
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), [], name);
    assert.ok(axioms.hereditary.includes(choiceAxiom), `${name} selects the stage intervals by choice`);
    assert.deepEqual(axioms.hereditary.filter(axiom => axiom !== choiceAxiom && !zfAxioms.test(axiom)), [], name);
    t.diagnostic(`${name} axioms: ${axioms.hereditary.join(", ")}`);
  }
});
