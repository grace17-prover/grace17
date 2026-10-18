// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { auditTheoremAxioms, createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

// Erdős problem 397: the infinite family of coincidences among products of
// central binomial coefficients found by Somani with ChatGPT is checked in
// ZF, with no admissions and no use of Choice.
test("the Erdős 397 family is a theorem of ZF with no admissions", t => {
  const kernel = createZfKernel();
  const source = readFileSync("examples/Erdos397Starter.g17", "utf8");
  const modules = loadModuleSourceGraph(kernel, [{ file: "Erdos397Starter.g17", source }], ["lib"]);
  assert.equal(modules.flatMap(module => module.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.NumberTheory.Erdos397.") ||
    name.startsWith("Grace.Cumulus.NumberTheory.Binomial.") ||
    name.startsWith("Erdos397Starter.")).filter(name => !name.endsWith(".generalized_induction_aux"));
  assert.ok(names.includes("Grace.Cumulus.NumberTheory.Erdos397.erdos397.identity"));
  assert.ok(names.includes("Grace.Cumulus.NumberTheory.Erdos397.erdos397.distinct"));
  assert.ok(names.includes("Grace.Cumulus.NumberTheory.Erdos397.erdos397.unbounded"));
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(axiom => /sorry|choice/i.test(axiom)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited without Choice or admissions`);
});
