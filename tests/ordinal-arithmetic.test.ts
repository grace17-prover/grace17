// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Ordinal arithmetic (Set/Ordinal/Monotone, ArithmeticLaws, Omega): the
// operations are strictly monotone and continuous in the right argument,
// addition and multiplication are associative, multiplication distributes
// on the left, the power laws hold for a positive base, every ordinal is
// zero, a successor, or a limit, and at ω the finite ordinals are absorbed
// on the left, so 1 + ω = ω ≠ ω + 1, 2 * ω = ω ≠ ω * 2, and 2 ^ ω = ω. The
// ordinal root and its modules are checked through the machine interface's
// check method with the audit attached: every theorem is proved, the laws
// print as written, and every audit names the ZF axioms and nothing else.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.Set.Ordinal.";
const modules = [
  "Set/Ordinal/Monotone",
  "Set/Ordinal/ArithmeticLaws",
  "Set/Ordinal/Omega",
  "Ordinal",
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

function arithmetic(): CheckResult {
  if (!checked) {
    checked = callMachineMethod("check", {
      files: modules.map(module => ({ name: `lib/Grace/Cumulus/${module}.g17` })),
      foundation: "ZF",
      audit: true,
    }) as CheckResult;
  }
  return checked;
}

function theorem(name: string): Theorem {
  const found = arithmetic().theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of ordinal arithmetic`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the ordinal arithmetic modules check under ZF with every theorem proved", t => {
  const result = arithmetic();
  assert.equal(result.status, "checked");
  assert.deepEqual(result.sorries, []);
  const unproved = result.theorems.filter(item => item.status !== "proved").map(item => item.name);
  assert.deepEqual(unproved, []);
  const admitted = result.theorems.filter(item => item.sorries.length > 0).map(item => item.name);
  assert.deepEqual(admitted, []);
  t.diagnostic(`${result.theorems.length} declarations checked across ${modules.length} files`);
});

test("the laws of ordinal arithmetic print as written", () => {
  const ordinals = "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → γ ∈ Ordinal";
  const expected: Record<string, string> = {
    "ArithmeticLaws.ordinalAdd.associative": `${ordinals} → α + β + γ = α + (β + γ)`,
    "ArithmeticLaws.ordinalMul.associative": `${ordinals} → α * β * γ = α * (β * γ)`,
    "ArithmeticLaws.ordinalMul.distributive": `${ordinals} → α * (β + γ) = α * β + α * γ`,
    "ArithmeticLaws.ordinalPow.add":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → ∅ ∈ α → γ ∈ Ordinal → α ^ (β + γ) = α ^ β * α ^ γ",
    "ArithmeticLaws.ordinalPow.mul":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → ∅ ∈ α → γ ∈ Ordinal → (α ^ β) ^ γ = α ^ (β * γ)",
    "ArithmeticLaws.ordinalPow.one_left": "∀ β, β ∈ Ordinal → 1 ^ β = 1",
    "Monotone.ordinalMul.zero_left": "∀ β, β ∈ Ordinal → 0 * β = 0",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("monotonicity, limits, and cancellation print as written", () => {
  const expected: Record<string, string> = {
    "Monotone.ordinalMul.monotone":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → ∅ ∈ α → γ ∈ Ordinal → β ∈ γ → α * β ∈ α * γ",
    "Monotone.ordinalPow.monotone":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → 1 ∈ α → γ ∈ Ordinal → β ∈ γ → α ^ β ∈ α ^ γ",
    "Monotone.ordinalAdd.cancel":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → γ ∈ Ordinal → α + β = α + γ → β = γ",
    "Monotone.ordinalMul.cancel":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → γ ∈ Ordinal → ∅ ∈ α → α * β = α * γ → β = γ",
    "Monotone.ordinalPow.cancel":
      "∀ α, ∀ β, ∀ γ, α ∈ Ordinal → β ∈ Ordinal → γ ∈ Ordinal → 1 ∈ α → α ^ β = α ^ γ → β = γ",
    "Monotone.ordinalAdd.limit_right": "∀ α, ∀ λ, α ∈ Ordinal → λ ∈ Ordinal → Limit(λ) → Limit(α + λ)",
    "Monotone.ordinalMul.limit_right":
      "∀ α, ∀ λ, α ∈ Ordinal → λ ∈ Ordinal → ∅ ∈ α → Limit(λ) → Limit(α * λ)",
    "Monotone.ordinalPow.limit_right":
      "∀ α, ∀ λ, α ∈ Ordinal → λ ∈ Ordinal → 1 ∈ α → Limit(λ) → Limit(α ^ λ)",
    "Monotone.Ordinal.zero_successor_or_limit":
      "∀ α, α ∈ Ordinal → α = 0 ∨ (∃ β, β ∈ Ordinal ∧ α = next(β)) ∨ Limit(α)",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("the failures of commutativity at ω print as written", () => {
  // ω is ℕ as a set, and the printer writes it so.
  const expected: Record<string, string> = {
    "Omega.ordinalAdd.natural_omega": "∀ n : ℕ, n + ℕ = ℕ",
    "Omega.ordinalAdd.one_omega": "1 + ℕ = ℕ",
    "Omega.ordinalAdd.not_commutative": "1 + ℕ ≠ ℕ + 1",
    "Omega.ordinalMul.natural_omega": "∀ n : ℕ, ∅ ∈ n → n * ℕ = ℕ",
    "Omega.ordinalMul.two": "∀ α, α ∈ Ordinal → α * 2 = α + α",
    "Omega.ordinalMul.two_omega": "2 * ℕ = ℕ",
    "Omega.ordinalMul.not_commutative": "2 * ℕ ≠ ℕ * 2",
    "Omega.ordinalPow.natural_omega": "∀ n : ℕ, 1 ∈ n → n ^ ℕ = ℕ",
    "Omega.ordinalPow.two_omega": "2 ^ ℕ = ℕ",
    "Omega.ordinalPow.not_commutative": "2 ^ ℕ ≠ ℕ ^ 2",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("every theorem of ordinal arithmetic is ZF: the audits name no other axiom", () => {
  const names = arithmetic().theorems
    .filter(item => item.name.startsWith(prefix + "Monotone.")
      || item.name.startsWith(prefix + "ArithmeticLaws.")
      || item.name.startsWith(prefix + "Omega."))
    .map(item => item.name.slice(prefix.length));
  assert.ok(names.length >= 45, `${names.length} theorems audited`);
  for (const name of names) {
    const found = audit(name);
    assert.equal(found.complete, true, `${name} audit is complete`);
    const others = found.hereditary.filter(axiom => !zfAxioms.test(axiom));
    assert.deepEqual(others, [], `${name} uses only ZF axioms`);
  }
});
