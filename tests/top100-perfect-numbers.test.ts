// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entry 70, the perfect number theorem: σ(n) is the sum of the
// divisors of n and n is perfect when σ(n) = 2n. Euclid: 2^(p−1) · (2^p − 1)
// is perfect when 2^p − 1 is prime. Euler: every even perfect number has this
// form. Underneath: σ is multiplicative on coprime arguments, σ(p) = p + 1
// characterises the primes above 1, and σ(2^k) = 2^(k+1) − 1. Each statement
// is restated in a workbench file as it is meant to be read, proved from the
// library theorem, and its printed form is pinned; the library theorems are
// audited admission-free in ZF.

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const header = "module Top100Perfect\nimport Grace.Cumulus.NumberTheory.PerfectNumbers\n\n";

function check(body: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Perfect.g17", source: header + body }], "ZFG",
    ["Top100Perfect.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 1200));
  assert.equal(result.sorries.length, 0);
  for (const theorem of result.theorems) assert.equal(theorem.sorries.length, 0, theorem.name);
  return new Map(result.theorems.map(item => [item.name.replace("Top100Perfect.", ""), item.statement]));
}

const euclidForm = "∃ p ∈ ℕ, Prime(2 ^ p - 1) ∧ n = 2 ^ (p - 1) * (2 ^ p - 1)";

test("σ(n) is the sum over divisors(n), a perfect number has σ(n) = 2n, and 6 is perfect", () => {
  const statements = check(`theorem sigmaDefinition (n : Nat)
  shows sigma(n) = natSum(divisors(n), identity(ℕ))
proof
  exact sigma.definition at n

theorem perfectDefinition (n : Nat)
  shows Perfect(n) ↔ 0 < n ∧ sigma(n) = 2 * n
proof
  simp [Perfect]

theorem six
  shows Perfect(6)
proof
  have prime : Prime(2 ^ 2 - 1)
    have three : 2 ^ 2 - 1 = 3 by compute
    rw three
    exact Prime.three
  have euclid := perfect.of_mersenne with prime
  have value : 2 ^ (2 - 1) * (2 ^ 2 - 1) = 6 by compute
  rw value at euclid
  exact euclid
`);
  assert.equal(statements.get("sigmaDefinition"), "∀ n : ℕ, sigma(n) = natSum(divisors(n), identity(ℕ))");
  assert.equal(statements.get("perfectDefinition"), "∀ n : ℕ, Perfect(n) ↔ 0 < n ∧ sigma(n) = 2 * n");
  assert.equal(statements.get("six"), "Perfect(6)");
});

test("σ is multiplicative on coprime arguments, σ(p) = p + 1 characterises primes, and σ(2^k) = 2^(k+1) − 1", () => {
  const statements = check(`theorem multiplicative (m n : Nat)
  requires coprime : gcd(m, n) = 1
  shows sigma(m * n) = sigma(m) * sigma(n)
proof
  exact sigma.multiplicative with *

theorem primeValue (p : Nat)
  requires prime : Prime(p)
  shows sigma(p) = p + 1
proof
  exact sigma.prime with *

theorem primeCharacterization (p : Nat)
  requires aboveOne : 1 < p
  shows Prime(p) ↔ sigma(p) = p + 1
proof
  exact sigma.prime_iff with *

theorem twoPow (k : Nat)
  shows sigma(2 ^ k) = 2 ^ (k + 1) - 1
proof
  exact sigma.two_pow at k
`);
  assert.equal(statements.get("multiplicative"), "∀ m n : ℕ, gcd(m, n) = 1 → sigma(m * n) = sigma(m) * sigma(n)");
  assert.equal(statements.get("primeValue"), "∀ p : ℕ, Prime(p) → sigma(p) = p + 1");
  assert.equal(statements.get("primeCharacterization"), "∀ p : ℕ, 1 < p → (Prime(p) ↔ sigma(p) = p + 1)");
  assert.equal(statements.get("twoPow"), "∀ k : ℕ, sigma(2 ^ k) = 2 ^ (k + 1) - 1");
});

test("multiplicativity needs coprime arguments: without the hypothesis the restatement is rejected", () => {
  assert.throws(() => check(`theorem unrestricted (m n : Nat)
  shows sigma(m * n) = sigma(m) * sigma(n)
proof
  exact sigma.multiplicative with *
`));
});

test("Euclid: 2^(p−1)(2^p − 1) is perfect when 2^p − 1 is prime; Euler: every even perfect number has this form", () => {
  const statements = check(`theorem euclid (p : Nat)
  requires prime : Prime(2 ^ p - 1)
  shows Perfect(2 ^ (p - 1) * (2 ^ p - 1))
proof
  exact perfect.of_mersenne with *

theorem euler (n : Nat)
  requires perfect : Perfect(n)
  requires even : Even(n)
  shows ${euclidForm}
proof
  exact perfect.even_form with *

theorem evenIff (n : Nat)
  requires even : Even(n)
  shows Perfect(n) ↔ ${euclidForm}
proof
  exact perfect.even_iff with *
`);
  assert.equal(statements.get("euclid"), "∀ p : ℕ, Prime(2 ^ p - 1) → Perfect(2 ^ (p - 1) * (2 ^ p - 1))");
  assert.equal(statements.get("euler"), `∀ n : ℕ, Perfect(n) → Even(n) → ${euclidForm}`);
  assert.equal(statements.get("evenIff"), `∀ n : ℕ, Even(n) → (Perfect(n) ↔ ${euclidForm})`);
});

test("Euler's direction needs evenness: without it the restatement is rejected", () => {
  assert.throws(() => check(`theorem oddCase (n : Nat)
  requires perfect : Perfect(n)
  shows ${euclidForm}
proof
  exact perfect.even_form with *
`));
});

test("the perfect number modules are admission-free ZF", t => {
  const kernel = createZfKernel();
  const file = "lib/Grace/Cumulus/NumberTheory/PerfectNumbers.g17";
  const modules = loadModuleSourceGraph(kernel, [{ file, source: readFileSync(file, "utf8") }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.NumberTheory\.(NaturalSums|DivisorSum|PerfectNumbers)\./.test(name));
  for (const expected of ["natSum.reindex", "natSum.product", "sigma.multiplicative", "sigma.prime",
    "sigma.prime_iff", "sigma.two_pow", "perfect.of_mersenne", "perfect.even_form", "perfect.even_iff"]) {
    assert.ok(names.some(name => name.endsWith(`.${expected}`)), expected);
  }
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited`);
});
