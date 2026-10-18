// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The sphere layer of the Banach–Tarski development: every point of the
// sphere is carried to the pole by a rotation, images and powers commute
// with conjugation, the sphere absorbs every countable subset, and with
// Hausdorff's paradox the unit sphere is SO3-paradoxical. The statements
// are pinned as the Workbench prints them, every proof checks without
// admissions, and the audit of the final theorem names the choice axiom
// and nothing beyond the ZF axioms: the countable unions of
// Geometry/Absorption/CountableUnion are coded through choice functions,
// so the global choice operator does not enter.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { callMachineMethod } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const modules = [
  "Geometry/Sphere/Transitive.g17",
  "Geometry/Sphere/Conjugate.g17",
  "Geometry/Sphere/Absorb.g17",
  "Geometry/Sphere/Paradox.g17",
];
const files = modules.map(name => ({ name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8") }));

const expected: Record<string, string> = {
  "Grace.Cumulus.Geometry.Sphere.Transitive.so3.transitive_pole":
    "∀ q ∈ S², ∃ σ ∈ so3Matrices, σ · q = basis(2)",
  "Grace.Cumulus.Geometry.Sphere.Conjugate.actImage.conjugate":
    "∀ σ ρ ∈ so3Matrices, ∀ D, D ⊆ S² → actImage(sphereAction, σ⁻¹ * ρ * σ, D) = " +
    "actImage(sphereAction, σ⁻¹, actImage(sphereAction, ρ, actImage(sphereAction, σ, D)))",
  "Grace.Cumulus.Geometry.Sphere.Conjugate.so3.pow_conjugate":
    "∀ σ ρ ∈ so3Matrices, ∀ n : ℕ, (σ⁻¹ * ρ * σ) ^ n = σ⁻¹ * ρ ^ n * σ",
  "Grace.Cumulus.Geometry.Sphere.Absorb.sphere.exists_separating_any":
    "∀ D, Countable(D) → D ⊆ S² → " +
    "∃ ρ ∈ SO3.carrier, ∀ n ∈ ℕ, Disjoint(actImage(sphereAction, ρ ^ (n + 1), D), D)",
  "Grace.Cumulus.Geometry.Sphere.Absorb.sphere.absorb_any":
    "∀ D, Countable(D) → D ⊆ S² → Equidecomposable(sphereAction, SO3, S², S², S² ∖ D)",
  "Grace.Cumulus.Geometry.Sphere.Paradox.sphere.paradoxical":
    "Paradoxical(sphereAction, SO3, S²)",
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

test("the sphere layer checks without admissions and prints its statements as written", t => {
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

const choiceAxioms = /^set\.choice$/u;

test("the audit of the paradoxical sphere names choice and nothing beyond ZF", t => {
  const result = callMachineMethod("check", {
    files: [{ name: "lib/Grace/Cumulus/Geometry/Sphere/Paradox.g17" }],
    audit: true,
  }) as CheckResult;
  assert.equal(result.status, "checked");
  const name = "Grace.Cumulus.Geometry.Sphere.Paradox.sphere.paradoxical";
  const theorem = result.theorems.find(item => item.name === name);
  assert.ok(theorem, `${name} is a theorem of the sphere layer`);
  assert.equal(theorem.status, "proved");
  const audit = theorem.audit;
  assert.ok(audit, `${name} carries an audit`);
  assert.equal(audit.complete, true);
  assert.ok(audit.hereditary.includes("set.choice"));
  assert.deepEqual(audit.hereditary.filter(axiom => !choiceAxioms.test(axiom) && !zfAxioms.test(axiom)), []);
  assert.deepEqual(audit.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), []);
  t.diagnostic(`sphere.paradoxical axioms: ${audit.hereditary.join(", ")}`);
});
