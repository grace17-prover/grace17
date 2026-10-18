// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The rotation layer of the Banach–Tarski campaign: the group SO3 and its
// actions, the generating rotations, and the freeness of nonempty reduced
// words, each stated as on a board and printed back the same way.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module BanachTarskiRotations\nimport Grace.Cumulus.Rotation\n";

function statements(source: string): Map<string, string> {
  const result = checkWorkbenchFiles([{ name: "BanachTarskiRotations.g17", source }], "ZFG", ["BanachTarskiRotations.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return new Map(result.theorems.map(item => [item.name.split(".").at(-1)!, item.statement]));
}

test("SO3, its actions, the generators, and the freeness theorem print as written", () => {
  const printed = statements(header + `
theorem group
  shows Group(SO3)
proof
  exact SO3.group

theorem sphere
  shows sphereAction : SO3 ↷ S²
proof
  exact sphereAction.action

theorem space
  shows spaceAction : SO3 ↷ ℝ³
proof
  exact spaceAction.action

theorem generators
  shows rotA ∈ so3Matrices ∧ rotB ∈ so3Matrices
proof
  exact ⟨rotA.so3, rotB.so3⟩

theorem inverses
  shows so3Inverse(rotA) = transpose(rotA) ∧ so3Inverse(rotB) = transpose(rotB)
proof
  exact ⟨rotA.inverse, rotB.inverse⟩

theorem norm (M : realRing ^ 3 × 3) (v : Set)
  requires orthogonal : Orthogonal(M)
  requires vector : v : 3 → ℝ
  shows normSq(M · v) = normSq(v)
proof
  exact Orthogonal.normSq with orthogonal, vector

theorem freeness (w : List(4))
  requires reduced : Reduced(w)
  requires nonempty : w ≠ []
  shows wordRotation(w) ≠ SO3.one
proof
  exact wordRotation.ne_unit with reduced, nonempty

theorem sample
  shows wordRotation([0, 2]) ≠ Ring.one(matrixRing(realRing, 3))
proof
  exact wordRotation.sample
`);
  assert.equal(printed.get("group"), "Group(SO3)");
  assert.equal(printed.get("sphere"), "sphereAction : SO3 ↷ S²");
  assert.equal(printed.get("space"), "spaceAction : SO3 ↷ ℝ³");
  assert.equal(printed.get("generators"), "rotA ∈ so3Matrices ∧ rotB ∈ so3Matrices");
  assert.equal(printed.get("inverses"), "so3Inverse(rotA) = transpose(rotA) ∧ so3Inverse(rotB) = transpose(rotB)");
  assert.equal(printed.get("norm"), "∀ (M : realRing ^ 3 × 3), ∀ v, Orthogonal(M) → FunctionBetween(v, 3, ℝ) → normSq(M · v) = normSq(v)");
  assert.equal(printed.get("freeness"), "∀ w, List(4, w) → Reduced(w) → w ≠ [] → wordRotation(w) ≠ SO3.one");
  assert.equal(printed.get("sample"), "wordRotation([0, 2]) ≠ Ring.one(matrixRing(realRing, 3))");
});

test("the freeness theorem and wordRotation([0, 2]) ≠ 1 check without sorry", () => {
  const file = { name: "Rotation/Freeness.g17", source: readFileSync("lib/Grace/Cumulus/Rotation/Freeness.g17", "utf8") };
  const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  assert.equal(result.ok, true);
  for (const name of ["wordRotation.ne_one", "wordRotation.ne_unit", "wordRotation.sample"]) {
    const proof = result.theorems.find(t => t.name.endsWith(name));
    assert.ok(proof, name);
    assert.equal(proof.steps.at(-1)?.after.goals.length, 0, name);
  }
  assert.ok(!file.source.includes("sorry"));
});
