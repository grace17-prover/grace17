// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Cantor–Bendixson on the real line (Topology/Real): ℚ is dense in ℝ
// (Real/Embedding), open intervals are open (Topology/Real), the open
// intervals with rational endpoints form a countable basis of the line, and the
// general theorem at that basis says that every closed set of reals is the
// disjoint union of a perfect set and a countable set, with a countable
// rank. The modules are checked through the machine interface's check
// method with the audit attached: every theorem is proved, the statements
// print as written, and the audits name no axiom beyond ZF.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.";
const modules = [
  "Real/Embedding",
  "Topology/Real",
  "Topology/Real/RationalBase",
  "Topology/Real/CantorBendixson",
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

function reals(): CheckResult {
  if (!checked) {
    checked = callMachineMethod("check", {
      files: modules.map(module => ({ name: `lib/Grace/Cumulus/${module}.g17` })),
      audit: true,
    }) as CheckResult;
  }
  return checked;
}

function theorem(name: string): Theorem {
  const found = reals().theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of the real-line development`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the real-line Cantor–Bendixson modules check with every theorem proved", t => {
  const result = reals();
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
    "Real.Embedding.rationalCut.between":
      "∀ x y : ℝ, x < y → ∃ q ∈ ℚ, x < rationalCut(q) ∧ rationalCut(q) < y",
    "Topology.Real.openInterval.open":
      "∀ A B : ℝ, openInterval(A, B) ∈ realTopology",
    "Topology.Real.RationalBase.rationalIntervals.membership":
      "∀ W, W ∈ rationalIntervals ↔ W ∈ 𝒫(ℝ) ∧ ∃ p ∈ ℚ, ∃ q ∈ ℚ, p < q ∧ W = openInterval(rationalCut(p), rationalCut(q))",
    "Topology.Real.RationalBase.rationalIntervals.open": "rationalIntervals ⊆ realTopology",
    "Topology.Real.RationalBase.rationalIntervals.basis": "Basis(ℝ, realTopology, rationalIntervals)",
    "Topology.Real.RationalBase.rationalIntervals.countable": "Countable(rationalIntervals)",
    "Topology.Real.CantorBendixson.reals.cantorBendixson":
      "∀ A, IsClosed(ℝ, realTopology, A) → Perfect(ℝ, realTopology, perfectKernel(ℝ, realTopology, A)) ∧ " +
      "perfectKernel(ℝ, realTopology, A) ⊆ A ∧ Countable(A ∖ perfectKernel(ℝ, realTopology, A))",
    "Topology.Real.CantorBendixson.reals.kernel_perfect":
      "∀ A, IsClosed(ℝ, realTopology, A) → Perfect(ℝ, realTopology, perfectKernel(ℝ, realTopology, A))",
    "Topology.Real.CantorBendixson.reals.scattered_countable":
      "∀ A, IsClosed(ℝ, realTopology, A) → Countable(A ∖ perfectKernel(ℝ, realTopology, A))",
    "Topology.Real.CantorBendixson.reals.rank_countable":
      "∀ A, IsClosed(ℝ, realTopology, A) → Countable(cantorBendixsonRank(ℝ, realTopology, A))",
    "Topology.Real.CantorBendixson.closed.countable_or_perfect_part":
      "∀ A, IsClosed(ℝ, realTopology, A) → Countable(A) ∨ ∃ P, Nonempty(P) ∧ Perfect(ℝ, realTopology, P) ∧ P ⊆ A",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("the rational basis and the real-line theorem are theorems of ZF", t => {
  for (const name of [
    "Real.Embedding.rationalCut.between",
    "Topology.Real.RationalBase.rationalIntervals.basis",
    "Topology.Real.RationalBase.rationalIntervals.countable",
    "Topology.Real.CantorBendixson.reals.cantorBendixson",
    "Topology.Real.CantorBendixson.reals.rank_countable",
    "Topology.Real.CantorBendixson.closed.countable_or_perfect_part",
  ]) {
    assert.equal(theorem(name).status, "proved", name);
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), [], name);
    assert.deepEqual(axioms.hereditary.filter(axiom => !zfAxioms.test(axiom)), [], name);
    t.diagnostic(`${name} axioms: ${axioms.hereditary.join(", ")}`);
  }
});
