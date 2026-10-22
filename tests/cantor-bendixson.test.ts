// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Cantor–Bendixson (Topology/CantorBendixson): the derived set of a closed
// set is closed, its transfinite iteration decreases and intersects at
// limits, a basic open set witnesses at most one removal, so the stages
// stabilise below the Hartogs bound of a countable base; the stage at the
// Cantor–Bendixson rank is perfect and the removed points are countable.
// The root and its modules are checked through the machine interface's
// check method with the audit attached: every theorem is proved, the four
// theorems and the three recursion laws print as written, and the audit of
// each Cantor–Bendixson theorem names the ZF axioms and nothing else, since
// every choice in the proof is the least code under an explicit injection
// (Cardinal/LeastCode).

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.Topology.CantorBendixson.";
const modules = [
  "Topology/CantorBendixson/Derived",
  "Topology/CantorBendixson/Iterate",
  "Topology/CantorBendixson/Stabilise",
  "Topology/CantorBendixson/Theorem",
  "Topology/CantorBendixson",
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

// One workspace holds the root and its modules, so the environment is
// loaded once and every theorem is reported with its audit.
let checked: CheckResult | undefined;

function cantorBendixson(): CheckResult {
  if (!checked) {
    checked = callMachineMethod("check", {
      files: modules.map(module => ({ name: `lib/Grace/Cumulus/${module}.g17` })),
      audit: true,
    }) as CheckResult;
  }
  return checked;
}

function theorem(name: string): Theorem {
  const found = cantorBendixson().theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of the Cantor–Bendixson development`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the Cantor–Bendixson modules check with every theorem proved", t => {
  const result = cantorBendixson();
  assert.equal(result.status, "checked");
  assert.deepEqual(result.sorries, []);
  const unproved = result.theorems.filter(item => item.status !== "proved").map(item => item.name);
  assert.deepEqual(unproved, []);
  const admitted = result.theorems.filter(item => item.sorries.length > 0).map(item => item.name);
  assert.deepEqual(admitted, []);
  t.diagnostic(`${result.theorems.length} declarations checked across ${modules.length} files`);
});

test("the recursion laws and the theorems print as written", () => {
  const hypotheses = "IsTopology(X, T) → Basis(X, T, B) → IsClosed(X, T, A) → Countable(B)";
  const expected: Record<string, string> = {
    "Iterate.derived.zero": "∀ X, ∀ T, ∀ A, derived(X, T, A, 0) = A",
    "Iterate.derived.next":
      "∀ X, ∀ T, ∀ A, ∀ α, α ∈ Ordinal → derived(X, T, A, next(α)) = derivedSet(X, T, derived(X, T, A, α))",
    "Iterate.derived.limit":
      "∀ X, ∀ T, ∀ A, ∀ λ, Limit(λ) → derived(X, T, A, λ) = ⋂ range(history(X, T, A, λ))",
    "Iterate.derived.limit_membership":
      "∀ X, ∀ T, ∀ A, ∀ x, ∀ λ, Limit(λ) → (x ∈ derived(X, T, A, λ) ↔ ∀ β ∈ λ, x ∈ derived(X, T, A, β))",
    "Iterate.derived.decreasing":
      "∀ X, ∀ T, ∀ A, ∀ α, ∀ β, IsTopology(X, T) → IsClosed(X, T, A) → α ∈ Ordinal → β ∈ Ordinal → " +
      "α ∈ next(β) → derived(X, T, A, β) ⊆ derived(X, T, A, α)",
    "Stabilise.derived.stabilises":
      `∀ X, ∀ T, ∀ A, ∀ B, ${hypotheses} → ∃ γ ∈ hartogsBound(B), derived(X, T, A, next(γ)) = derived(X, T, A, γ)`,
    "Theorem.cantorBendixson.kernel_perfect":
      `∀ X, ∀ T, ∀ B, ∀ A, ${hypotheses} → Perfect(X, T, perfectKernel(X, T, A))`,
    "Theorem.cantorBendixson.kernel_subset":
      `∀ X, ∀ T, ∀ B, ∀ A, ${hypotheses} → perfectKernel(X, T, A) ⊆ A`,
    "Theorem.cantorBendixson.scattered_countable":
      `∀ X, ∀ T, ∀ B, ∀ A, ${hypotheses} → Countable(A ∖ perfectKernel(X, T, A))`,
    "Theorem.cantorBendixson.rank_countable":
      `∀ X, ∀ T, ∀ B, ∀ A, ${hypotheses} → Countable(cantorBendixsonRank(X, T, A))`,
    "Theorem.cantorBendixson":
      `∀ X, ∀ T, ∀ B, ∀ A, ${hypotheses} → Perfect(X, T, perfectKernel(X, T, A)) ∧ ` +
      "perfectKernel(X, T, A) ⊆ A ∧ Countable(A ∖ perfectKernel(X, T, A))",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("the Cantor–Bendixson theorems are theorems of ZF", t => {
  const names = cantorBendixson().theorems
    .map(item => item.name)
    .filter(name => name.startsWith(`${prefix}Theorem.cantorBendixson`))
    .map(name => name.slice(prefix.length));
  assert.ok(names.includes("Theorem.cantorBendixson"));
  assert.ok(names.includes("Theorem.cantorBendixson.rank_countable"));
  for (const name of names) {
    assert.equal(theorem(name).status, "proved", name);
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => /sorry|choice/u.test(axiom)), [], name);
    assert.deepEqual(axioms.hereditary.filter(axiom => !zfAxioms.test(axiom)), [], name);
    t.diagnostic(`${name} axioms: ${axioms.hereditary.join(", ")}`);
  }
});
