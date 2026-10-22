// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The ball layer of the Banach–Tarski development: decompositions
// transfer between a set and an invariant subset, the motions of ℝ³ form
// a group acting on ℝ³ with the rotations embedded, the pieces of the
// sphere lift to cones in the punctured ball, the ball absorbs its center,
// the closed unit ball is paradoxical under the motions, and in the strong
// form it is equidecomposable with two disjoint copies of itself. The
// statements are pinned as the Workbench prints them, every proof checks
// without admissions, and the audit of the final theorem names the choice
// axiom and nothing beyond the ZF axioms: the global choice operator does
// not enter, since the absorption layer codes countable unions through
// choice functions.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { callMachineMethod } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const modules = [
  "Algebra/Group/Paradox/Transfer.g17",
  "Geometry/Euclid/Motions.g17",
  "Geometry/Euclid/Ball.g17",
  "Geometry/Euclid/Cones.g17",
  "Geometry/Euclid/Center.g17",
  "Geometry/BanachTarski.g17",
];
const files = modules.map(name => ({ name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8") }));

const expected: Record<string, string> = {
  "Grace.Cumulus.Algebra.Group.Paradox.Transfer.Equidecomposable.of_restrict":
    "∀ act, ∀ G, ∀ X, ∀ Y, ∀ A, ∀ B, Action(act, G, X) → Y ⊆ X → (∀ g ∈ G.carrier, ∀ y ∈ Y, g ·ₐ y ∈ " +
    "Y) → A ⊆ Y → B ⊆ Y → Equidecomposable(restrictAction(act, G, Y), G, Y, A, B) → " +
    "Equidecomposable(act, G, X, A, B)",
  "Grace.Cumulus.Algebra.Group.Paradox.Transfer.Paradoxical.of_equidecomposable":
    "∀ act, ∀ G, ∀ X, ∀ Y, Action(act, G, X) → Y ⊆ X → Equidecomposable(act, G, X, X, Y) → (∃ A, ∃ B, " +
    "A ⊆ Y ∧ B ⊆ Y ∧ Disjoint(A, B) ∧ Equidecomposable(act, G, X, A, Y) ∧ Equidecomposable(act, G, X, " +
    "B, Y)) → Paradoxical(act, G, X)",
  "Grace.Cumulus.Algebra.Group.Paradox.Transfer.Paradoxical.to_restrict":
    "∀ act, ∀ G, ∀ X, ∀ Y, Action(act, G, X) → Y ⊆ X → (∃ A, ∃ B, A ⊆ Y ∧ B ⊆ Y ∧ Disjoint(A, B) ∧ " +
    "Equidecomposable(act, G, X, A, Y) ∧ Equidecomposable(act, G, X, B, Y)) → " +
    "Paradoxical(restrictAction(act, G, Y), G, Y)",
  "Grace.Cumulus.Geometry.Euclid.Motions.Motions.group":
    "Group(Motions)",
  "Grace.Cumulus.Geometry.Euclid.Motions.motionAction.action":
    "motionAction : Motions ↷ ℝ³",
  "Grace.Cumulus.Geometry.Euclid.Motions.rotationMotion.hom":
    "rotationMotion : SO3 →* Motions",
  "Grace.Cumulus.Geometry.Euclid.Motions.rotationMotion.compatible":
    "∀ M ∈ SO3.carrier, ∀ x ∈ ℝ³, spaceAction(M, x) = motionAction(rotationMotion(M), x)",
  "Grace.Cumulus.Geometry.Euclid.Cones.cone.sphere":
    "cone(S²) = puncturedBall",
  "Grace.Cumulus.Geometry.Euclid.Cones.cone.equidecomposable":
    "∀ A, ∀ B, A ⊆ S² → B ⊆ S² → Equidecomposable(sphereAction, SO3, S², A, B) → " +
    "Equidecomposable(spaceAction, SO3, ℝ³, cone(A), cone(B))",
  "Grace.Cumulus.Geometry.Euclid.Center.unitBall.absorb_center":
    "Equidecomposable(motionAction, Motions, ℝ³, unitBall, puncturedBall)",
  "Grace.Cumulus.Geometry.BanachTarski.puncturedBall.paradoxical":
    "Paradoxical(restrictAction(spaceAction, SO3, puncturedBall), SO3, puncturedBall)",
  "Grace.Cumulus.Geometry.BanachTarski.banachTarski":
    "∃ A, ∃ B, A ⊆ unitBall ∧ B ⊆ unitBall ∧ Disjoint(A, B) ∧ Equidecomposable(motionAction, Motions, " +
    "ℝ³, A, unitBall) ∧ Equidecomposable(motionAction, Motions, ℝ³, B, unitBall)",
  "Grace.Cumulus.Geometry.BanachTarski.banachTarski.restricted":
    "Paradoxical(restrictAction(motionAction, Motions, unitBall), Motions, unitBall)",
  "Grace.Cumulus.Geometry.BanachTarski.banachTarski.two_balls_part":
    "∃ C, C ⊆ unitBall ∧ Equidecomposable(motionAction, Motions, ℝ³, C, unitBall ∪ shiftedBall)",
};

interface Audit {
  complete: boolean;
  hereditary: string[];
}

interface Theorem {
  name: string;
  status: string;
  audit?: Audit;
}

interface CheckResult {
  status: string;
  theorems: Theorem[];
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the ball layer checks without admissions and prints its statements as written", t => {
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

test("the audit of the paradoxical ball names the choice axiom and nothing beyond ZF", t => {
  const result = callMachineMethod("check", {
    files: [{ name: "lib/Grace/Cumulus/Geometry/BanachTarski.g17" }],
    audit: true,
  }) as CheckResult;
  assert.equal(result.status, "checked");
  const name = "Grace.Cumulus.Geometry.BanachTarski.banachTarski";
  const theorem = result.theorems.find(item => item.name === name);
  assert.ok(theorem, `${name} is the final theorem of the ball layer`);
  assert.equal(theorem.status, "proved");
  const audit = theorem.audit;
  assert.ok(audit, `${name} carries an audit`);
  assert.equal(audit.complete, true);
  assert.ok(audit.hereditary.includes("set.choice"));
  // The choice axiom enters once, for the orbit representatives of
  // Algebra/Group/Paradox; the countable unions of the absorption layer are
  // coded through choice functions, so the global choice operator is absent.
  const choice = /^set\.choice$/u;
  assert.deepEqual(audit.hereditary.filter(axiom => !choice.test(axiom) && !zfAxioms.test(axiom)), []);
  assert.deepEqual(audit.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), []);
  t.diagnostic(`banachTarski axioms: ${audit.hereditary.join(", ")}`);
});
