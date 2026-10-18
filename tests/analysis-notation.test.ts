// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Analysis written as on a board: derivatives with primes and superscript
// indices, functions typed by their codomain, natural numbers coerced into
// real positions, inclusive sums with their bodies written out, and
// bounded quantifiers over natural numbers, each read and printed back.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfgKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module AnalysisNotation\nimport Grace.Cumulus.Real.Analysis\n";

function load(source: string) {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "AnalysisNotation.g17", source }], ["lib"]);
  return kernel;
}

function statements(source: string): Map<string, string> {
  const result = checkWorkbenchFiles([{ name: "AnalysisNotation.g17", source }], "ZFG", ["AnalysisNotation.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return new Map(result.theorems.map(item => [item.name.split(".").at(-1)!, item.statement]));
}

test("f′, f″, and f⁽ᵏ⁾ are the derivative, its iterate, and the k-th derivative, applied as functions", () => {
  const written = header + `
theorem primes (f : ℝ → ℝ) (A B : Real, n : Nat)
  shows f′(A) * f″(B) = f⁽²⁾(B) * f′(A) ∧ f⁽ⁿ⁺¹⁾(A) = f⁽ⁿ⁺¹⁾(A) ∧ f⁽ᵏ⁾′ = f⁽ᵏ⁾′
proof
  sorry
`.replace("f⁽ᵏ⁾′ = f⁽ᵏ⁾′", "f⁽ⁿ⁾′ = (f′)⁽ⁿ⁾");
  const spelled = header + `
theorem primes (f : ℝ → ℝ) (A B : Real, n : Nat)
  shows derivative(f)(A) * derivative(derivative(f))(B) = iteratedDerivative(f, 2)(B) * derivative(f)(A) ∧
    iteratedDerivative(f, n + 1)(A) = iteratedDerivative(f, n + 1)(A) ∧
    derivative(iteratedDerivative(f, n)) = iteratedDerivative(derivative(f), n)
proof
  sorry
`;
  assert.ok(formulaEquals(load(written).theorems.get("AnalysisNotation.primes")!, load(spelled).theorems.get("AnalysisNotation.primes")!));
  const printed = statements(written);
  assert.equal(printed.get("primes"),
    "∀ (f : ℝ → ℝ), ∀ A B : ℝ, ∀ n : ℕ, f′(A) * f″(B) = f⁽²⁾(B) * f′(A) ∧ f⁽ⁿ⁺¹⁾(A) = f⁽ⁿ⁺¹⁾(A) ∧ f⁽ⁿ⁾′ = (f′)⁽ⁿ⁾");
});

test("a function typed by its codomain makes its values real for the notation around them", () => {
  const written = header + `
theorem values (f : ℝ → ℝ) (A : Real)
  shows f(A) = 0 → f′(A) ≠ 0 → f(A) - f′(A) = 0
proof
  sorry
`;
  const spelled = header + `
theorem values (f : ℝ → ℝ) (A : Real)
  shows f(A) = (0:R) → derivative(f)(A) ≠ (0:R) → (f(A):R) - (derivative(f)(A):R) = (0:R)
proof
  sorry
`;
  assert.ok(formulaEquals(load(written).theorems.get("AnalysisNotation.values")!, load(spelled).theorems.get("AnalysisNotation.values")!));
  assert.equal(statements(written).get("values"), "∀ (f : ℝ → ℝ), ∀ A : ℝ, f(A) = 0 → f′(A) ≠ 0 → f(A) - f′(A) = 0");
});

test("a natural number in a real position is coerced by realNat and prints without the cast", () => {
  const source = header + `
theorem product (X : Real, n : Nat)
  shows n! * X = X * realNat(n!) ∧ (n + 1) * X = realNat(n + 1) * X ∧ n < X ∧ n! = X
proof
  sorry

theorem natural (n : Nat)
  shows n + 1 = succ(n) ∧ n! = n!
proof
  sorry

theorem cast (n : Nat)
  shows realNat(succ(n)) = realNat(n) + 1
proof
  sorry
`;
  const spelled = header + `
theorem product (X : Real, n : Nat)
  shows (realNat(n!):R) * X = X * (realNat(n!):R) ∧
    (realNat(n + 1):R) * X = (realNat(n + 1):R) * X ∧
    (realNat(n):R) < X ∧ realNat(n!) = X
proof
  sorry

theorem natural (n : Nat)
  shows add(n, 1) = succ(n) ∧ factorial(n) = factorial(n)
proof
  sorry

theorem cast (n : Nat)
  shows realNat(succ(n)) = (realNat(n):R) + 1
proof
  sorry
`;
  const written = load(source);
  const raw = load(spelled);
  for (const name of ["product", "natural", "cast"]) {
    assert.ok(formulaEquals(written.theorems.get(`AnalysisNotation.${name}`)!, raw.theorems.get(`AnalysisNotation.${name}`)!), name);
  }
  const printed = statements(source);
  assert.equal(printed.get("product"), "∀ X : ℝ, ∀ n : ℕ, n! * X = X * n! ∧ (n + 1) * X = (n + 1) * X ∧ n < X ∧ n! = X");
  assert.equal(printed.get("natural"), "∀ n : ℕ, n + 1 = succ(n) ∧ n! = n!");
  // Beside a numeral the cast stays, since `n + 1` would read back as a natural sum.
  assert.equal(printed.get("cast"), "∀ n : ℕ, realNat(succ(n)) = realNat(n) + 1");
});

test("∑ k ≤ n is the sum below n + 1, its body extends over a product, and a declared sequence is written out", () => {
  const source = header + `
theorem inclusive (u : Set, n : Nat)
  shows ∑ k ≤ n, u(k) = realPartialSum(u, n + 1)
proof
  rfl

theorem summand (u : Set, n : Nat) (X : Real)
  shows ∑ k < n, u(k) + X = (∑ k < n, uₖ) + X
proof
  rfl

theorem taylorSum (f : ℝ → ℝ) (A B : Real, n : Nat)
  shows ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k! = ∑ k < n + 1, taylorTerms(f, A, B)(k)
proof
  rfl
`;
  const printed = statements(source);
  assert.equal(printed.get("inclusive"), "∀ u, ∀ n : ℕ, ∑ k ≤ n, uₖ = ∑ k ≤ n, uₖ");
  assert.equal(printed.get("summand"), "∀ u, ∀ n : ℕ, ∀ X : ℝ, ∑ k < n, uₖ + X = ∑ k < n, uₖ + X");
  assert.equal(printed.get("taylorSum"),
    "∀ (f : ℝ → ℝ), ∀ A B : ℝ, ∀ n : ℕ, ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k! = ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k!");
  assert.throws(() => load(header + `
theorem bad (n : Nat)
  shows ∑ k < n, k! = realPartialSum(n, n)
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError && /value of a graph declared as a sequence/u.test(error.message));
});

test("∀ k ≤ n binds a natural number below the bound and prints back in that form", () => {
  const written = header + `
theorem bounded (n : Nat) (X : Real)
  shows (∀ k ≤ n, k ≤ n) ∧ (∃ k < n + 1, k ≤ n ∧ k < X + 1)
proof
  sorry
`;
  const spelled = header + `
theorem bounded (n : Nat) (X : Real)
  shows (∀ k, Nat(k) → k ≤ n → k ≤ n) ∧ (∃ k, Nat(k) ∧ k < n + 1 ∧ k ≤ n ∧ (realNat(k):R) < X + 1)
proof
  sorry
`;
  assert.ok(formulaEquals(load(written).theorems.get("AnalysisNotation.bounded")!, load(spelled).theorems.get("AnalysisNotation.bounded")!));
  assert.equal(statements(written).get("bounded"), "∀ n : ℕ, ∀ X : ℝ, (∀ k ≤ n, k ≤ n) ∧ ∃ k < n + 1, k ≤ n ∧ k < X + 1");
});
