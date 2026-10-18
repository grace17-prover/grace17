// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entry 23, the formula for Pythagorean triples: the parametrization
// (m² − n², 2mn, m² + n²) gives Pythagorean triples, primitive ones for
// coprime m, n of opposite parity; every primitive triple with an even leg
// arises this way; every triple is gcd(a, b) times a primitive one; and the
// lemma underneath, that coprime factors of a square are squares. Each
// statement is restated in a workbench file as it is meant to be read, proved
// from the library theorem, and its printed form is pinned; the library
// theorems are audited admission-free in ZF.

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const header = "module Top100Pythagorean\nimport Grace.Cumulus.NumberTheory.PythagoreanTriples\n\n";

function check(body: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Pythagorean.g17", source: header + body }], "ZFG",
    ["Top100Pythagorean.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 1200));
  assert.equal(result.sorries.length, 0);
  for (const theorem of result.theorems) assert.equal(theorem.sorries.length, 0, theorem.name);
  return new Map(result.theorems.map(item => [item.name.replace("Top100Pythagorean.", ""), item.statement]));
}

test("the parametrization (m² − n², 2mn, m² + n²) gives Pythagorean triples, primitive for coprime m, n of opposite parity", () => {
  const statements = check(`theorem parametrization (m n : Nat)
  requires positive : 0 < n
  requires below : n < m
  shows Pythagorean(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)
proof
  exact pythagorean.of_parameters with *

theorem primitiveParametrization (m n : Nat)
  requires positive : 0 < n
  requires below : n < m
  requires coprime : gcd(m, n) = 1
  requires parity : Odd(m + n)
  shows PrimitivePythagorean(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)
proof
  exact pythagorean.primitive_of_parameters with *

theorem threeFourFive
  shows PrimitivePythagorean(3, 4, 5)
proof
  have positive : 0 < 1 by arith
  have below : 1 < 2 by arith
  have coprime : gcd(2, 1) = 1 by compute
  have parity : Odd(2 + 1)
    have three : 2 + 1 = 3 by compute
    rw three
    exact Odd.three
  have triple := pythagorean.primitive_of_parameters at 2, 1
    with positive, below, coprime, parity
  have first : 2 ^ 2 - 1 ^ 2 = 3 by compute
  have second : 2 * 2 * 1 = 4 by compute
  have third : 2 ^ 2 + 1 ^ 2 = 5 by compute
  rw [first, second, third] at triple
  exact triple
`);
  assert.equal(statements.get("parametrization"),
    "∀ m n : ℕ, 0 < n → n < m → Pythagorean(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)");
  assert.equal(statements.get("primitiveParametrization"),
    "∀ m n : ℕ, 0 < n → n < m → gcd(m, n) = 1 → Odd(m + n) → " +
    "PrimitivePythagorean(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)");
  assert.equal(statements.get("threeFourFive"), "PrimitivePythagorean(3, 4, 5)");
});

test("the parametrization needs n > 0: without it the restatement is rejected", () => {
  assert.throws(() => check(`theorem degenerate (m n : Nat)
  requires below : n < m
  shows Pythagorean(m ^ 2 - n ^ 2, 2 * m * n, m ^ 2 + n ^ 2)
proof
  exact pythagorean.of_parameters with *
`));
});

test("a primitive triple has exactly one even leg, and with b even it is (m² − n², 2mn, m² + n²) for coprime m > n > 0 of opposite parity", () => {
  const statements = check(`theorem oneEven (a b c : Nat)
  requires primitive : PrimitivePythagorean(a, b, c)
  shows Odd(a + b)
proof
  exact pythagorean.one_even with *

theorem primitiveForm (a b c : Nat)
  requires primitive : PrimitivePythagorean(a, b, c)
  requires even : Even(b)
  shows ∃ m, Nat(m) ∧ ∃ n, Nat(n) ∧
    0 < n ∧ n < m ∧ gcd(m, n) = 1 ∧ Odd(m + n) ∧
    a = m ^ 2 - n ^ 2 ∧ b = 2 * m * n ∧ c = m ^ 2 + n ^ 2
proof
  exact pythagorean.primitive_form with *
`);
  assert.equal(statements.get("oneEven"), "∀ a b c : ℕ, PrimitivePythagorean(a, b, c) → Odd(a + b)");
  assert.equal(statements.get("primitiveForm"),
    "∀ a b c : ℕ, PrimitivePythagorean(a, b, c) → Even(b) → ∃ m : ℕ, ∃ n : ℕ, " +
    "0 < n ∧ n < m ∧ gcd(m, n) = 1 ∧ Odd(m + n) ∧ a = m ^ 2 - n ^ 2 ∧ b = 2 * m * n ∧ c = m ^ 2 + n ^ 2");
});

test("every Pythagorean triple is gcd(a, b) times a primitive one", () => {
  const statements = check(`theorem form (a b c : Nat)
  requires triple : Pythagorean(a, b, c)
  shows ∃ x, Nat(x) ∧ ∃ y, Nat(y) ∧ ∃ z, Nat(z) ∧
    PrimitivePythagorean(x, y, z) ∧
    a = gcd(a, b) * x ∧ b = gcd(a, b) * y ∧ c = gcd(a, b) * z
proof
  exact pythagorean.form with *
`);
  assert.equal(statements.get("form"),
    "∀ a b c : ℕ, Pythagorean(a, b, c) → ∃ x : ℕ, ∃ y : ℕ, ∃ z : ℕ, PrimitivePythagorean(x, y, z) ∧ " +
    "a = gcd(a, b) * x ∧ b = gcd(a, b) * y ∧ c = gcd(a, b) * z");
});

test("coprime factors of a square are squares, and a divisor whose square divides a square divides its root", () => {
  const statements = check(`theorem coprimeSquares (a b c : Nat)
  requires coprime : gcd(a, b) = 1
  requires product : a * b = c * c
  shows IsSquare(a) ∧ IsSquare(b)
proof
  exact IsSquare.of_coprime_mul with *

theorem rootDivides (d c : Nat)
  requires squares : d * d ∣ c * c
  shows d ∣ c
proof
  exact divides.of_mul_self with *
`);
  assert.equal(statements.get("coprimeSquares"),
    "∀ a b c : ℕ, gcd(a, b) = 1 → a * b = c * c → IsSquare(a) ∧ IsSquare(b)");
  assert.equal(statements.get("rootDivides"), "∀ d c : ℕ, d * d ∣ c * c → d ∣ c");
});

test("the Pythagorean triple and coprime square modules are admission-free ZF", t => {
  const kernel = createZfKernel();
  const file = "lib/Grace/Cumulus/NumberTheory/PythagoreanTriples.g17";
  const modules = loadModuleSourceGraph(kernel, [{ file, source: readFileSync(file, "utf8") }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.NumberTheory\.(PythagoreanTriples|CoprimeSquares)\./.test(name));
  for (const expected of ["pythagorean.of_parameters", "pythagorean.primitive_of_parameters", "pythagorean.one_even",
    "pythagorean.primitive_form", "pythagorean.form", "IsSquare.of_coprime_mul", "divides.of_mul_self"]) {
    assert.ok(names.some(name => name.endsWith(`.${expected}`)), expected);
  }
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited`);
});
