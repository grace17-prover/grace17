// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entries on real analysis: Taylor's theorem with the Lagrange
// remainder (35) and L'Hôpital's rule (64), with the Cauchy mean value
// theorem underneath. The library theorems are restated as they are written
// on a board, with primes for derivatives, the sum written out, and the
// factorials read as reals, closed by the library proofs, and the
// statements are checked to print as written.

import assert from "node:assert/strict";
import test from "node:test";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module Top100Analysis\nimport Grace.Cumulus.Real.Analysis\n";

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Analysis.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

function statement(result: ReturnType<typeof checkWorkbenchFiles>, name: string): string {
  const theorem = result.theorems.find(item => item.name === `Top100Analysis.${name}`);
  assert.ok(theorem, `theorem ${name} is missing`);
  return theorem.statement;
}

test("Taylor's theorem with the Lagrange remainder is stated and proved in textbook form", () => {
  const result = check(header + `
theorem taylor (f : ℝ → ℝ) (A B : Real, n : Nat)
  requires ordered : A < B
  requires smooth : ∀ k ≤ n, ∀ X ∈ closedInterval(A, B), DifferentiableAt(f⁽ᵏ⁾, X)
  shows ∃ C ∈ ℝ, A < C ∧ C < B ∧
    f(B) = ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k! + f⁽ⁿ⁺¹⁾(C) * (B - A) ^ (n + 1) / (n + 1)!
proof
  exact Taylor.theorem with *

theorem taylorTerm (f : ℝ → ℝ) (X B : Real, k : Nat)
  shows taylorTerms(f, X, B)(k) = f⁽ᵏ⁾(X) * (B - X) ^ k / k!
proof
  exact taylorTerms.value with *

theorem iterated (f : Set, k : Nat)
  shows f⁽ᵏ⁺¹⁾ = f⁽ᵏ⁾′
proof
  exact iteratedDerivative.succ with *

theorem meanValueCase (f : ℝ → ℝ) (A B : Real)
  requires ordered : A < B
  requires differentiable : ∀ X ∈ closedInterval(A, B), DifferentiableAt(f, X)
  shows ∃ C ∈ ℝ, A < C ∧ C < B ∧ f(B) = f(A) + f′(C) * (B - A)
proof
  exact Taylor.mean_value with *

theorem derivativeValue (f : Set) (D X : Real)
  requires hasDerivative : HasDerivativeAt(f, D, X)
  shows f′(X) = D
proof
  exact derivative.of_has_derivative with *
`);
  assert.equal(statement(result, "taylor"),
    "∀ (f : ℝ → ℝ), ∀ A B : ℝ, ∀ n : ℕ, A < B → (∀ k ≤ n, ∀ X ∈ closedInterval(A, B), DifferentiableAt(f⁽ᵏ⁾, X)) → ∃ C ∈ ℝ, A < C ∧ C < B ∧ f(B) = ∑ k ≤ n, f⁽ᵏ⁾(A) * (B - A) ^ k / k! + f⁽ⁿ⁺¹⁾(C) * (B - A) ^ (n + 1) / (n + 1)!");
  assert.equal(statement(result, "taylorTerm"),
    "∀ (f : ℝ → ℝ), ∀ X B : ℝ, ∀ k : ℕ, taylorTerms(f, X, B)(k) = f⁽ᵏ⁾(X) * (B - X) ^ k / k!");
  assert.equal(statement(result, "iterated"), "∀ f, ∀ k : ℕ, f⁽ᵏ⁺¹⁾ = f⁽ᵏ⁾′");
  assert.equal(statement(result, "meanValueCase"),
    "∀ (f : ℝ → ℝ), ∀ A B : ℝ, A < B → (∀ X ∈ closedInterval(A, B), DifferentiableAt(f, X)) → ∃ C ∈ ℝ, A < C ∧ C < B ∧ f(B) = f(A) + f′(C) * (B - A)");
  assert.equal(statement(result, "derivativeValue"),
    "∀ f, ∀ D X : ℝ, HasDerivativeAt(f, D, X) → f′(X) = D");
});

test("L'Hôpital's rule in the 0/0 form and the Cauchy mean value theorem are stated and proved in textbook form", () => {
  const result = check(header + `
theorem lhopital (f g : ℝ → ℝ) (A L W : Real)
  requires radius : 0 < W
  requires differentiableF : ∀ X ∈ openBall(A, W), DifferentiableAt(f, X)
  requires differentiableG : ∀ X ∈ openBall(A, W), DifferentiableAt(g, X)
  requires nonzero : ∀ X ∈ openBall(A, W), X ≠ A → g′(X) ≠ (0:R)
  requires zeroF : f(A) = 0
  requires zeroG : g(A) = 0
  requires limit : TendsToAt(pointwiseDiv(f′, g′), L, A)
  shows TendsToAt(pointwiseDiv(f, g), L, A)
proof
  exact LHopital.theorem with *

theorem cauchy (f g : ℝ → ℝ) (A B : Real)
  requires ordered : A < B
  requires continuousF : ContinuousOn(f, closedInterval(A, B))
  requires continuousG : ContinuousOn(g, closedInterval(A, B))
  requires differentiableF : ∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(f, C)
  requires differentiableG : ∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(g, C)
  shows ∃ C ∈ ℝ, A < C ∧ C < B ∧ f′(C) * (g(B) - g(A)) = g′(C) * (f(B) - f(A))
proof
  exact CauchyMeanValue.theorem with *

theorem meanValue (f : ℝ → ℝ) (A B : Real)
  requires ordered : A < B
  requires continuous : ContinuousOn(f, closedInterval(A, B))
  requires differentiable : ∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(f, C)
  shows ∃ C ∈ ℝ, A < C ∧ C < B ∧ f′(C) * (B - A) = f(B) - f(A)
proof
  exact MeanValue.derivative with *
`);
  assert.equal(statement(result, "lhopital"),
    "∀ (f g : ℝ → ℝ), ∀ A L W : ℝ, 0 < W → (∀ X ∈ openBall(A, W), DifferentiableAt(f, X)) → (∀ X ∈ openBall(A, W), DifferentiableAt(g, X)) → (∀ X ∈ openBall(A, W), X ≠ A → g′(X) ≠ 0) → f(A) = 0 → g(A) = 0 → TendsToAt(pointwiseDiv(f′, g′), L, A) → TendsToAt(pointwiseDiv(f, g), L, A)");
  assert.equal(statement(result, "cauchy"),
    "∀ (f g : ℝ → ℝ), ∀ A B : ℝ, A < B → ContinuousOn(f, closedInterval(A, B)) → ContinuousOn(g, closedInterval(A, B)) → (∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(f, C)) → (∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(g, C)) → ∃ C ∈ ℝ, A < C ∧ C < B ∧ f′(C) * (g(B) - g(A)) = g′(C) * (f(B) - f(A))");
  assert.equal(statement(result, "meanValue"),
    "∀ (f : ℝ → ℝ), ∀ A B : ℝ, A < B → ContinuousOn(f, closedInterval(A, B)) → (∀ C ∈ ℝ, A < C → C < B → DifferentiableAt(f, C)) → ∃ C ∈ ℝ, A < C ∧ C < B ∧ f′(C) * (B - A) = f(B) - f(A)");
});

test("the hypotheses of L'Hôpital's rule are all needed: dropping the vanishing of g at A is rejected", () => {
  assert.throws(() => check(header + `
theorem invalid (f g : ℝ → ℝ) (A L W : Real)
  requires radius : 0 < W
  requires differentiableF : ∀ X ∈ openBall(A, W), DifferentiableAt(f, X)
  requires differentiableG : ∀ X ∈ openBall(A, W), DifferentiableAt(g, X)
  requires nonzero : ∀ X ∈ openBall(A, W), X ≠ A → g′(X) ≠ (0:R)
  requires zeroF : f(A) = 0
  requires limit : TendsToAt(pointwiseDiv(f′, g′), L, A)
  shows TendsToAt(pointwiseDiv(f, g), L, A)
proof
  exact LHopital.theorem with *
`));
});
