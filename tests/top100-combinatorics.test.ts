// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entries from combinatorics and graph theory: the Erdős–Szekeres
// theorem, the number of derangements with its recurrence and
// inclusion–exclusion formula, and the combinatorial half of the friendship
// theorem. Each statement is restated in a workbench file exactly as it is
// meant to be read, proved from the library theorem, and its printed form
// is pinned.

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module Top100Combinatorics\nimport Grace.Cumulus.Combinatorics\nimport Grace.Cumulus.GraphTheory\nimport Grace.Cumulus.GraphTheory.Friendship\n\n";

function check(body: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Combinatorics.g17", source: header + body }], "ZFG",
    ["Top100Combinatorics.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 1200));
  return new Map(result.theorems.map(item => [item.name.replace("Top100Combinatorics.", ""), item.statement]));
}

test("Erdős–Szekeres: m·n + 1 distinct points of a linear order hold a monotone run of length m + 1 or n + 1", () => {
  const statements = check(`theorem erdosSzekeres (P f : Set) (m n : Nat)
  requires order : LinearOrder(P)
  requires distinct : InjectiveBetween(f, m * n + 1, points(P))
  shows (∃ S ∈ subsetsOfSize(m * n + 1, m + 1), IncreasingOn(P, f, S)) ∨
    (∃ S ∈ subsetsOfSize(m * n + 1, n + 1), DecreasingOn(P, f, S))
proof
  exact erdos_szekeres with *
`);
  assert.equal(statements.get("erdosSzekeres"),
    "∀ P f, ∀ m n : ℕ, LinearOrder(P) → InjectiveBetween(f, m * n + 1, P.points) → " +
    "(∃ S ∈ subsetsOfSize(m * n + 1, m + 1), IncreasingOn(P, f, S)) ∨ " +
    "∃ S ∈ subsetsOfSize(m * n + 1, n + 1), DecreasingOn(P, f, S)");
});

test("Erdős–Szekeres needs the full m·n + 1 points", () => {
  assert.throws(() => check(`theorem short (P f : Set) (m n : Nat)
  requires order : LinearOrder(P)
  requires distinct : InjectiveBetween(f, m * n, points(P))
  shows (∃ S ∈ subsetsOfSize(m * n, m + 1), IncreasingOn(P, f, S)) ∨
    (∃ S ∈ subsetsOfSize(m * n, n + 1), DecreasingOn(P, f, S))
proof
  exact erdos_szekeres with *
`));
});

test("derangements: the fixed-point-free permutations of n points number d(n), with the recurrence and the alternating formula", () => {
  const statements = check(`theorem derangementCount (n : Nat)
  shows cardinality(derangements(n)) = derangement(n)
proof
  exact derangements.natural_count at n

theorem derangementRecurrence (n : Nat)
  shows cardinality(derangements(n + 2)) =
    (n + 1) * (cardinality(derangements(n + 1)) + cardinality(derangements(n)))
proof
  exact derangements.recurrence at n

theorem derangementFormula (n : Nat)
  shows integerOfNat(cardinality(derangements(n))) = derangementSum(n, n + 1)
proof
  exact derangements.formula at n

theorem derangementSumStep (n k : Nat)
  shows derangementSum(n, k + 1) = derangementSum(n, k) +
    integerPow(-1, k) * integerOfNat((n choose k) * (n - k)!)
proof
  exact derangementSum.succ at n, k

theorem derangementsOfThree
  shows cardinality(derangements(3)) = 2
proof
  rw derangements.natural_count
  exact derangement.three

theorem derangementMembership (I p : Set)
  shows p ∈ derangements(I) ↔ p ∈ permutations(I) ∧ ∀ x ∈ I, p(x) ≠ x
proof
  exact derangements.membership at I, p
`);
  assert.equal(statements.get("derangementCount"), "∀ n : ℕ, cardinality(derangements(n)) = derangement(n)");
  assert.equal(statements.get("derangementRecurrence"),
    "∀ n : ℕ, cardinality(derangements(n + 2)) = (n + 1) * (cardinality(derangements(n + 1)) + cardinality(derangements(n)))");
  assert.equal(statements.get("derangementFormula"),
    "∀ n : ℕ, integerOfNat(cardinality(derangements(n))) = derangementSum(n, n + 1)");
  assert.equal(statements.get("derangementSumStep"),
    "∀ n k : ℕ, derangementSum(n, k + 1) = derangementSum(n, k) + integerPow(-1, k) * integerOfNat((n choose k) * (n - k)!)");
  assert.equal(statements.get("derangementsOfThree"), "cardinality(derangements(3)) = 2");
  assert.equal(statements.get("derangementMembership"),
    "∀ I, ∀ p, p ∈ derangements(I) ↔ p ∈ permutations(I) ∧ ∀ x ∈ I, p(x) ≠ x");
});

test("friendship graphs: non-adjacent vertices share a degree, and unequal degrees force a universal vertex", () => {
  const statements = check(`theorem friendshipIrregular (V E x y : Set)
  requires friendship : Friendship(V, E)
  requires finite : Finite(V)
  requires hx : x ∈ V
  requires hy : y ∈ V
  requires different :
    cardinality(neighbors(V, E, x)) ≠ cardinality(neighbors(V, E, y))
  shows ∃ u ∈ V, ∀ w ∈ V, w ≠ u → Adjacent(E, u, w)
proof
  exact Friendship.universal_of_irregular with *

theorem friendshipDegrees (V E u v : Set)
  requires friendship : Friendship(V, E)
  requires finite : Finite(V)
  requires hu : u ∈ V
  requires hv : v ∈ V
  requires apart : ¬Adjacent(E, u, v)
  shows cardinality(neighbors(V, E, u)) = cardinality(neighbors(V, E, v))
proof
  exact Friendship.degree_eq_of_not_adjacent with *

theorem friendshipRegular (V E : Set)
  requires friendship : Friendship(V, E)
  requires finite : Finite(V)
  requires noUniversal : ∀ x ∈ V, ∃ y ∈ V, y ≠ x ∧ ¬Adjacent(E, x, y)
  shows ∀ x ∈ V, ∀ y ∈ V,
    cardinality(neighbors(V, E, x)) = cardinality(neighbors(V, E, y))
proof
  exact Friendship.regular with *

theorem friendshipVertexCount (V E x : Set)
  requires friendship : Friendship(V, E)
  requires finite : Finite(V)
  requires hx : x ∈ V
  requires regular : ∀ y ∈ V,
    cardinality(neighbors(V, E, y)) = cardinality(neighbors(V, E, x))
  shows cardinality(V) =
    cardinality(neighbors(V, E, x)) * (cardinality(neighbors(V, E, x)) - 1) + 1
proof
  exact Friendship.vertex_count with *
`);
  assert.equal(statements.get("friendshipIrregular"),
    "∀ V, ∀ E, ∀ x, ∀ y, Friendship(V, E) → Finite(V) → x ∈ V → y ∈ V → " +
    "cardinality(neighbors(V, E, x)) ≠ cardinality(neighbors(V, E, y)) → ∃ u ∈ V, ∀ w ∈ V, w ≠ u → Adjacent(E, u, w)");
  assert.equal(statements.get("friendshipDegrees"),
    "∀ V, ∀ E, ∀ u, ∀ v, Friendship(V, E) → Finite(V) → u ∈ V → v ∈ V → ¬Adjacent(E, u, v) → " +
    "cardinality(neighbors(V, E, u)) = cardinality(neighbors(V, E, v))");
  assert.equal(statements.get("friendshipRegular"),
    "∀ V, ∀ E, Friendship(V, E) → Finite(V) → (∀ x ∈ V, ∃ y ∈ V, y ≠ x ∧ ¬Adjacent(E, x, y)) → " +
    "∀ x ∈ V, ∀ y ∈ V, cardinality(neighbors(V, E, x)) = cardinality(neighbors(V, E, y))");
  assert.equal(statements.get("friendshipVertexCount"),
    "∀ V, ∀ E, ∀ x, Friendship(V, E) → Finite(V) → x ∈ V → " +
    "(∀ y ∈ V, cardinality(neighbors(V, E, y)) = cardinality(neighbors(V, E, x))) → " +
    "cardinality(V) = cardinality(neighbors(V, E, x)) * (cardinality(neighbors(V, E, x)) - 1) + 1");
});
