// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const source = readFileSync("examples/MaximalIndependentFamily.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "MaximalIndependentFamily.g17", source: text }], ["lib"]);
  return kernel;
}

test("finite maximal independent families and their relations have complete ZF audits", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Cardinal.FiniteSubsets.")
    || name.startsWith("Grace.Cumulus.Algebra.Polynomial.IndependentSubfamily.")
    || name.startsWith("MaximalIndependentFamily."));
  assert.ok(names.length >= 20, `expected the family proofs, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(axiom => /choice|sorry/i.test(axiom)), [], name);
  }
});

for (const premise of ["source", "target", "hom", "finite", "seed", "injective", "emptyAssignment", "assignment", "subset", "independent", "maximal", "index", "outside"]) {
  test(`finite selection and dependence require ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("completed and cached maximal-family goals preserve polynomial ring scopes", () => {
  for (let pass = 0; pass < 2; pass++) {
    const checked = checkWorkbenchFiles([{ name: "MaximalIndependentFamily.g17", source }], "ZF", ["MaximalIndependentFamily.g17"]);
    const relation = checked.theorems.find(t => t.name === "MaximalIndependentFamily.excluded_generator_has_relation")!;
    assert.ok(relation);
    assert.ok(relation.steps.length);
    assert.match(relation.statement, /p ∈ Q/);
    assert.match(relation.statement, /Q\[0\]/);
    assert.match(relation.statement, /polynomialAtOver\(insert\(j, M\), R, S, f,/);
  }
});
