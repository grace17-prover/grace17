// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfgKernel, createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const algebra = readFileSync("examples/FiniteModuleIntegrality.g17", "utf8");
const nullstellensatz = readFileSync("examples/Nullstellensatz.g17", "utf8");
function load(source: string, choice = false) {
  const kernel = choice ? createZfgKernel() : createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "Application.g17", source }], ["lib"]);
  assert.deepEqual(modules.flatMap(m => m.sorries), []);
  return kernel;
}

test("finite-module integrality and indexed combinations are hereditary admission-free ZF", t => {
  const kernel = load(algebra);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace\.Cumulus\.Algebra\.(IndexedCombinations|MatrixAnnihilator|Ring.DeterminantIdentity)\./.test(n) ||
    n.startsWith("FiniteModuleIntegralityExample."));
  assert.ok(names.length >= 17);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

test("abstract Nullstellensatz and certificate have no inherited admissions", () => {
  const kernel = load(nullstellensatz, true);
  for (const name of ["unit_iff_unsatisfiable", "certificate_iff_unsatisfiable"]) {
    const audit = auditTheoremAxioms(kernel, `NullstellensatzExample.${name}`);
    assert.equal(audit.complete, true);
    assert.deepEqual(audit.hereditary.filter(a => /sorry/i.test(a)), []);
    assert.ok(audit.hereditary.some(a => /choice/i.test(a)), "maximal ideals retain their explicit Choice dependency");
  }
});

for (const [label, source, pattern, choice] of [
  ["multiplication equations", algebra, /^  requires rows :.*\n/gm, false],
  ["finite generation as a module", algebra, /^  requires finiteModule :.*\n/gm, false],
  ["algebraic closedness", nullstellensatz, /^hypothesis closed :.*\n/gm, true],
  ["finitely many variables", nullstellensatz, /^hypothesis finite :.*\n/gm, true],
] as const) {
  test(`applications require ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed, choice), /cannot|does not match|unknown|missing/i);
  });
}
