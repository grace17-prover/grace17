// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The strong form of the Banach–Tarski paradox: the closed unit ball is
// equidecomposable with the disjoint union of two copies of itself. The
// piece maps realise a decomposition as a piecewise-moved bijection, the
// Banach–Schröder–Bernstein theorem turns two embeddings (each set
// equidecomposable with a subset of the other) into a decomposition
// through the back-and-forth chain of Cardinal.Dominance, and the ball
// embeds in two balls as a subset while two balls embed in the ball
// through the paradoxical pieces. The statements are pinned as the
// Workbench prints them, every proof checks without admissions, and the
// audit of the strong theorem names the choice axiom and nothing beyond
// the ZF axioms.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { callMachineMethod } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const modules = [
  "Algebra/Group/Paradox/PieceMaps.g17",
  "Algebra/Group/Paradox/SchroederBernstein.g17",
  "Geometry/BanachTarski.g17",
];
const files = modules.map(name => ({ name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8") }));

const expected: Record<string, string> = {
  "Grace.Cumulus.Algebra.Group.Paradox.PieceMaps.pieceMap.bijective":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ F, Action(act, G, X) → F ⊆ 𝒫(X) × G.carrier → Pieces(A, F) → " +
    "MovedPieces(act, X, B, F) → BijectiveBetween(pieceMap(act, X, F), A, B)",
  "Grace.Cumulus.Algebra.Group.Paradox.PieceMaps.Equidecomposable.restrict":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ C, ∀ F, Action(act, G, X) → Finite(F) → F ⊆ 𝒫(X) × G.carrier → " +
    "Pieces(A, F) → (∀ p ∈ F, moved(act, X, p) ⊆ B) → (∀ p ∈ F, ∀ q ∈ F, p ≠ q → " +
    "Disjoint(moved(act, X, p), moved(act, X, q))) → C ⊆ A → " +
    "Equidecomposable(act, G, X, C, functionImage(pieceMap(act, X, F), C, B))",
  "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.chain.complement":
    "∀ f, ∀ g, ∀ A, ∀ B, FunctionBetween(f, A, B) → InjectiveBetween(g, B, A) → " +
    "functionImage(g, B ∖ functionImage(f, chain(f, g, A, B), B), A) = A ∖ chain(f, g, A, B)",
  "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.Equidecomposable.bijection":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, Action(act, G, X) → Equidecomposable(act, G, X, A, B) → " +
    "∃ f, BijectiveBetween(f, A, B) ∧ PiecewiseMoved(act, G, X, A, f)",
  "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.Equidecomposable.of_bijection":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ f, Action(act, G, X) → BijectiveBetween(f, A, B) → " +
    "PiecewiseMoved(act, G, X, A, f) → Equidecomposable(act, G, X, A, B)",
  "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.Equidecomposable.of_injections":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ f, ∀ g, Action(act, G, X) → FunctionBetween(f, A, B) → " +
    "InjectiveBetween(g, B, A) → " +
    "(∀ C, C ⊆ A → Equidecomposable(act, G, X, C, functionImage(f, C, B))) → " +
    "(∀ D, D ⊆ B → Equidecomposable(act, G, X, D, functionImage(g, D, A))) → " +
    "Equidecomposable(act, G, X, A, B)",
  "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.Equidecomposable.of_embeddings":
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, Action(act, G, X) → A ⊆ X → B ⊆ X → Embeds(act, G, X, A, B) → " +
    "Embeds(act, G, X, B, A) → Equidecomposable(act, G, X, A, B)",
  "Grace.Cumulus.Geometry.BanachTarski.banachTarski.two_balls_part":
    "∃ C, C ⊆ unitBall ∧ Equidecomposable(motionAction, Motions, ℝ³, C, unitBall ∪ shiftedBall)",
  "Grace.Cumulus.Geometry.BanachTarski.banachTarski.two_balls":
    "Equidecomposable(motionAction, Motions, ℝ³, unitBall, unitBall ∪ shiftedBall)",
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

test("the strong Banach–Tarski layer checks without admissions and prints its statements as written", t => {
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

test("the audit of the Banach–Schröder–Bernstein theorem names only ZF axioms", t => {
  const result = callMachineMethod("check", {
    files: [{ name: "lib/Grace/Cumulus/Algebra/Group/Paradox/SchroederBernstein.g17" }],
    audit: true,
  }) as CheckResult;
  assert.equal(result.status, "checked");
  const name = "Grace.Cumulus.Algebra.Group.Paradox.SchroederBernstein.Equidecomposable.of_embeddings";
  const theorem = result.theorems.find(item => item.name === name);
  assert.ok(theorem, `${name} is the Banach–Schröder–Bernstein theorem`);
  assert.equal(theorem.status, "proved");
  const audit = theorem.audit;
  assert.ok(audit, `${name} carries an audit`);
  assert.equal(audit.complete, true);
  // The chain is defined by recursion on ℕ with explicit sets, so the
  // theorem is choice-free even though the Paradox root carries choice.
  assert.deepEqual(audit.hereditary.filter(axiom => !zfAxioms.test(axiom)), []);
  t.diagnostic(`of_embeddings axioms: ${audit.hereditary.join(", ")}`);
});

test("the audit of the strong form names the choice axiom and nothing beyond ZF", t => {
  const result = callMachineMethod("check", {
    files: [{ name: "lib/Grace/Cumulus/Geometry/BanachTarski.g17" }],
    audit: true,
  }) as CheckResult;
  assert.equal(result.status, "checked");
  const name = "Grace.Cumulus.Geometry.BanachTarski.banachTarski.two_balls";
  const theorem = result.theorems.find(item => item.name === name);
  assert.ok(theorem, `${name} is the strong form of the paradox`);
  assert.equal(theorem.status, "proved");
  const audit = theorem.audit;
  assert.ok(audit, `${name} carries an audit`);
  assert.equal(audit.complete, true);
  assert.ok(audit.hereditary.includes("set.choice"));
  // The choice axiom enters once, for the orbit representatives of
  // Algebra/Group/Paradox; the Schröder–Bernstein construction is explicit
  // and adds no axiom, so the global choice operator is absent.
  const choice = /^set\.choice$/u;
  assert.deepEqual(audit.hereditary.filter(axiom => !choice.test(axiom) && !zfAxioms.test(axiom)), []);
  assert.deepEqual(audit.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), []);
  t.diagnostic(`banachTarski.two_balls axioms: ${audit.hereditary.join(", ")}`);
});
