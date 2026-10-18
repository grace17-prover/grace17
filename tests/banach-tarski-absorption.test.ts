// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The absorption layer of the Banach–Tarski development: the rational
// rotations turn(t) about the z-axis, their injectivity, membership in SO3
// and infinite order off a countable set, the absorption theorem for a
// group action, the separation of a countable subset of the sphere from
// itself by some turn(t), and the SO3-equidecomposability of S² with S² ∖ D. The statements are pinned as the Workbench prints
// them and every proof must check without admissions.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const modules = [
  "Geometry/Absorption/CountableUnion.g17",
  "Geometry/Absorption/Absorb.g17",
  "Geometry/Absorption/Turn.g17",
  "Geometry/Absorption/Order.g17",
  "Geometry/Absorption/TurnRotation.g17",
  "Geometry/Absorption/Separation.g17",
  "Geometry/Absorption/Sphere.g17",
  "Geometry/Absorption/Pieces.g17",
  "Geometry/Absorption/Final.g17",
];
const files = modules.map(name => ({ name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8") }));

const expected: Record<string, string> = {
  "Grace.Cumulus.Geometry.Absorption.CountableUnion.Countable.union":
    "∀ S, Countable(S) → (∀ A ∈ S, Countable(A)) → Countable(⋃ S)",
  "Grace.Cumulus.Geometry.Absorption.Absorb.absorption":
    "∀ act G X, ∀ (ρ : G), ∀ D, Action(act, G, X) → D ⊆ X → (∀ n ∈ ℕ, Disjoint(actImage(act, ρ ^ (n + 1), D), D)) → " +
    "∃ U ∈ 𝒫(X), Disjoint(U, X ∖ U) ∧ U ∪ X ∖ U = X ∧ Disjoint(actImage(act, ρ, U), X ∖ U) ∧ actImage(act, ρ, U) ∪ X ∖ U = X ∖ D",
  "Grace.Cumulus.Geometry.Absorption.Turn.planeTurn.mul":
    "∀ a b c d : ℝ, planeTurn(a, b) * planeTurn(c, d) = planeTurn(a * c - b * d, a * d + b * c)",
  "Grace.Cumulus.Geometry.Absorption.Turn.turn.circle":
    "∀ t : ℝ, turnCos(t) * turnCos(t) + turnSin(t) * turnSin(t) = 1",
  "Grace.Cumulus.Geometry.Absorption.Turn.turn.injective":
    "∀ s t : ℝ, turn(s) = turn(t) → s = t",
  "Grace.Cumulus.Geometry.Absorption.Order.turn.infinite_order":
    "Countable(turnOrders)",
  "Grace.Cumulus.Geometry.Absorption.TurnRotation.turn.rotation":
    "∀ t : ℝ, turn(t) ∈ so3Matrices",
  "Grace.Cumulus.Geometry.Absorption.Separation.turnBad.finite":
    "∀ k : ℕ, ∀ (d e : 3 → ℝ), vectorPoint(d) ≠ complexZero → Finite(turnBad(k + 1, d, e))",
  "Grace.Cumulus.Geometry.Absorption.Sphere.turn.separates":
    "∀ D, Countable(D) → D ⊆ S² → (∀ d ∈ D, vectorPoint(d) ≠ complexZero) → " +
    "∃ t ∈ ℝ, ∀ n ∈ ℕ, Disjoint(actImage(sphereAction, turn(t) ^ (n + 1), D), D)",
  "Grace.Cumulus.Geometry.Absorption.Final.sphere.exists_separating":
    "∀ D, Countable(D) → D ⊆ S² → (∀ d ∈ D, vectorPoint(d) ≠ complexZero) → " +
    "∃ ρ ∈ SO3.carrier, ∀ n ∈ ℕ, Disjoint(actImage(sphereAction, ρ ^ (n + 1), D), D)",
  "Grace.Cumulus.Geometry.Absorption.Final.sphere.absorb_countable":
    "∀ D, Countable(D) → D ⊆ S² → (∀ d ∈ D, vectorPoint(d) ≠ complexZero) → Equidecomposable(sphereAction, SO3, S², S², S² ∖ D)",
};

test("the absorption layer checks without admissions and prints its statements as written", t => {
  const result = checkWorkbenchFiles(files, "ZFG", modules, { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  const statements = new Map(result.theorems.map(item => [item.name, item]));
  for (const [name, statement] of Object.entries(expected)) {
    const theorem = statements.get(name);
    assert.ok(theorem, `${name} is missing`);
    assert.deepEqual(theorem.sorries, [], name);
    assert.equal(theorem.statement, statement, name);
  }
  const admitted = result.theorems.filter(item => item.sorries.length > 0).map(item => item.name);
  assert.deepEqual(admitted, []);
  assert.deepEqual(result.sorries, []);
  t.diagnostic(`${result.theorems.length} declarations checked across ${modules.length} modules`);
});
