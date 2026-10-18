// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/EmptyVariablePolynomials.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "EmptyVariablePolynomials.g17", source: text }], ["lib"]);
  return kernel;
}

test("empty-variable reconstruction and relation transport have complete admission-free ZF audits", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name => name.startsWith("Grace.Cumulus.Algebra.Polynomial.EmptyVariables.") || name.startsWith("EmptyVariablePolynomials."));
  assert.equal(names.length, 13);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited in ZF`);
});

for (const premise of ["polynomial", "nonzero", "source", "target", "hom", "assignment", "algebraic"]) {
  test(`constant-coefficient transport retains ${premise}`, () => {
    const changed = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("coefficient extraction cannot reverse the nonzero conclusion", () => {
  assert.throws(() => load(source.replace("shows emptyPolynomialCoefficient(A, zero)(p) ≠ zero", "shows emptyPolynomialCoefficient(A, zero)(p) = zero")), /does not match|cannot/i);
});
