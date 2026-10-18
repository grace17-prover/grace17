// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/PolynomialLocalization.g17", "utf8");

test("evaluation and localization obstruction proofs have complete hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialLocalization.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name =>
    /Grace.Cumulus.Algebra.(Field.(Powers|LocalizationObstruction)|Polynomial.LocalizationObstruction)\./.test(name)
    || name.endsWith("polynomialCoordinateDifference.nonzero")
    || name.startsWith("PolynomialLocalization.")
    || name.endsWith("restrictBinary.value_on_subset")
    || name.endsWith("denominatorPowers.one_mem"));
  assert.equal(names.length, 14);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const [premise, expected] of [
  ["injective", /InjectiveBetween/],
  ["nonvanishing", /polynomialAt/],
  ["index", /cannot find evidence/i],
] as const) {
  test(`polynomial obstruction cannot discard ${premise}`, () => {
    let incomplete = source.replace(new RegExp(`^hypothesis ${premise} :.*\\n`, "m"), "");
    if (premise === "index") incomplete = incomplete.replace("proper_at_point with *", "proper_at_point at I, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, g, v, s, j with *");
    assert.notEqual(incomplete, source);
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "PolynomialLocalization.g17", source: incomplete }], ["lib"]), expected);
  });
}

test("a centered variable needs a genuine variable index and a nontrivial coefficient ring", () => {
  const prefix = `module Nonzero
namespace Nonzero
import Grace.Cumulus.Algebra.Polynomial.PointIdeal
section Rings
variable (I A add zero neg mul one j a : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring P := R[I]
hypothesis ring : IsCommRing(R)
hypothesis coefficient : a ∈ R
`;
  const proof = `theorem invalid
  shows polynomialCoordinateDifference(I, R, j, a) ≠ P[0]
proof
  exact polynomialCoordinateDifference.nonzero with *
end Rings
end Nonzero
`;
  for (const extra of ["hypothesis index : j ∈ I\n", "hypothesis distinct : R[0] ≠ R[1]\n"]) {
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Nonzero.g17", source: prefix + extra + proof }], ["lib"]), /cannot find evidence/);
  }
});

for (const premise of ["denominatorOne", "carrier"]) {
  test(`general nonfield obstruction requires ${premise}`, () => {
    const library = readFileSync("lib/Grace/Cumulus/Algebra/Field/LocalizationObstruction.g17", "utf8");
    const context = library.slice(library.indexOf("section Nonfields"), library.indexOf("theorem localizationWithin.not_field_of_kernel"));
    const body = `theorem invalid (p : Set)
  requires member : p ∈ R
  requires nonzero : p ≠ R[0]
  requires vanishes : h(p) = U[0]
  shows ¬IsField(L)
proof
  exact localizationWithin.not_field_of_kernel at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, C, sum, o, inverse, product, e, g, h, D, T, p with *
end Nonfields
end MissingPremise
`;
    const source = "module MissingPremise\nnamespace MissingPremise\nimport Grace.Cumulus.Algebra.Field.LocalizationObstruction\n" + context.replace(new RegExp(`^hypothesis ${premise} :.*\\n`, "m"), "") + body;
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "MissingPremise.g17", source }], ["lib"]), /cannot find evidence/);
  });
}
