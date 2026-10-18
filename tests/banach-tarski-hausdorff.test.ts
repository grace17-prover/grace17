// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Hausdorff's paradox (Geometry/Hausdorff): the rotation of a word is an
// injective homomorphism of the free group into SO3, a rotation other than
// the identity fixes at most two points of the sphere, the points fixed by
// nontrivial words form a countable set, and its complement is paradoxical.
// The modules are checked through the machine interface's check method with
// the audit attached: every theorem is proved, the statements print as
// written, and the audit of the final theorem names the choice axiom and
// nothing beyond the ZF axioms.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.";
const modules = [
  "Algebra/Group/Action/Restrict",
  "Geometry/Vectors3",
  "Geometry/Hausdorff/Hom",
  "Geometry/Hausdorff/FixedPoints",
  "Geometry/Hausdorff/Countable",
  "Geometry/Hausdorff/Paradox",
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

// One workspace holds every module, so the environment is loaded once and
// every theorem of the six files is reported with its audit.
let checked: CheckResult | undefined;

function hausdorff(): CheckResult {
  if (!checked) {
    checked = callMachineMethod("check", {
      files: modules.map(module => ({ name: `lib/Grace/Cumulus/${module}.g17` })),
      audit: true,
    }) as CheckResult;
  }
  return checked;
}

function theorem(name: string): Theorem {
  const found = hausdorff().theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of the Hausdorff development`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the Hausdorff modules check with every theorem proved", t => {
  const result = hausdorff();
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
    "Algebra.Group.Action.Restrict.restrictAction.action":
      "∀ act, ∀ G, ∀ X, ∀ Y, Action(act, G, X) → Y ⊆ X → (∀ g ∈ G.carrier, ∀ y ∈ Y, g ·ₐ y ∈ Y) → Action(restrictAction(act, G, Y), G, Y)",
    "Algebra.Group.Action.Restrict.restrictAction.apply":
      "∀ act, ∀ G, ∀ X, ∀ Y, ∀ g, ∀ y, Action(act, G, X) → Y ⊆ X → (∀ g ∈ G.carrier, ∀ y ∈ Y, g ·ₐ y ∈ Y) → g ∈ G → y ∈ Y → call2(restrictAction(act, G, Y), g, y) = g ·ₐ y",
    "Geometry.Vectors3.cross.normSq":
      "∀ (u v : 3 → ℝ), normSq(cross(u, v)) = normSq(u) * normSq(v) - dot3(u, v) * dot3(u, v)",
    "Geometry.Vectors3.vectorNeg.sphere": "∀ v ∈ S², vectorNeg(v) ∈ S²",
    "Geometry.Hausdorff.Hom.wordRotation.concat":
      "∀ u, ∀ v, List(4, u) → List(4, v) → wordRotation(concat(u, v)) = wordRotation(u) * wordRotation(v)",
    "Geometry.Hausdorff.Hom.wordRotation.reduce":
      "∀ w, List(4, w) → wordRotation(reduce(w)) = wordRotation(w)",
    "Geometry.Hausdorff.Hom.wordRotation.inverseWord":
      "∀ w, List(4, w) → wordRotation(inverseWord(w)) * wordRotation(w) = Ring.one(matrixRing(realRing, 3))",
    "Geometry.Hausdorff.Hom.wordHom.hom": "wordHom : freeGroup →* SO3",
    "Geometry.Hausdorff.Hom.wordHom.injective": "InjectiveBetween(wordHom, reducedWords, SO3.carrier)",
    "Geometry.Hausdorff.FixedPoints.so3.fixed_pair":
      "∀ M ∈ so3Matrices, ∀ u v ∈ S², M · u = u → M · v = v → v ≠ u → v ≠ vectorNeg(u) → M = Ring.one(matrixRing(realRing, 3))",
    "Geometry.Hausdorff.FixedPoints.so3.fixed_points":
      "∀ M ∈ so3Matrices, M ≠ Ring.one(matrixRing(realRing, 3)) → ∃ p ∈ S², ∀ v ∈ S², M · v = v → v = p ∨ v = vectorNeg(p)",
    "Geometry.Hausdorff.Countable.wordFixedSet.subset": "wordFixedSet ⊆ S²",
    "Geometry.Hausdorff.Countable.reducedWords.countable": "Countable(reducedWords)",
    "Geometry.Hausdorff.Countable.wordFixedSet.countable": "Countable(wordFixedSet)",
    "Geometry.Hausdorff.Paradox.wordFixedSet.invariant":
      "∀ w ∈ reducedWords, ∀ v ∈ S² ∖ wordFixedSet, sphereAction(wordRotation(w), v) ∈ S² ∖ wordFixedSet",
    "Geometry.Hausdorff.Paradox.freeSphereAction.action": "freeSphereAction : freeGroup ↷ S² ∖ wordFixedSet",
    "Geometry.Hausdorff.Paradox.freeSphereAction.free": "FreeAction(freeSphereAction, freeGroup, S² ∖ wordFixedSet)",
    "Geometry.Hausdorff.Paradox.hausdorff":
      "Paradoxical(restrictAction(sphereAction, SO3, S² ∖ wordFixedSet), SO3, S² ∖ wordFixedSet)",
    "Geometry.Hausdorff.Paradox.hausdorff.pieces":
      "∃ A, ∃ B, A ⊆ S² ∖ wordFixedSet ∧ B ⊆ S² ∖ wordFixedSet ∧ Disjoint(A, B) ∧ " +
      "Equidecomposable(sphereAction, SO3, S², A, S² ∖ wordFixedSet) ∧ Equidecomposable(sphereAction, SO3, S², B, S² ∖ wordFixedSet)",
  };
  for (const [name, statement] of Object.entries(expected)) {
    assert.equal(theorem(name).statement, statement, name);
  }
});

test("the audit of Hausdorff's paradox names the choice axiom and nothing beyond ZF", t => {
  for (const name of ["Geometry.Hausdorff.Paradox.hausdorff", "Geometry.Hausdorff.Paradox.hausdorff.pieces"]) {
    assert.equal(theorem(name).status, "proved", name);
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.ok(axioms.hereditary.includes("set.choice"), name);
    const others = axioms.hereditary.filter(axiom => axiom !== "set.choice");
    assert.deepEqual(others.filter(axiom => !zfAxioms.test(axiom)), [], name);
    assert.deepEqual(axioms.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), [], name);
    t.diagnostic(`${name} axioms: ${axioms.hereditary.join(", ")}`);
  }
});

test("the free action and the fixed-point theorem are theorems of ZF", t => {
  for (const name of [
    "Geometry.Hausdorff.FixedPoints.so3.fixed_points",
    "Geometry.Hausdorff.Hom.wordHom.injective",
    "Geometry.Hausdorff.Paradox.freeSphereAction.free",
    "Geometry.Hausdorff.Paradox.Equidecomposable.transfer",
  ]) {
    const axioms = audit(name);
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => !zfAxioms.test(axiom)), [], name);
  }
  t.diagnostic("four theorems audited without choice");
});
