// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const source = readFileSync("examples/CharacteristicPolynomial.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "CharacteristicPolynomial.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("actual characteristic polynomials, extension evaluation, and annihilation are admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Algebra.Ring.CharacteristicMatrix.") ||
    name.startsWith("Grace.Cumulus.Algebra.Polynomial.Characteristic.") ||
    name.startsWith("CharacteristicPolynomialExample."));
  assert.ok(names.length >= 24, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["the eigenvector equation", /^  requires eigenvector :.*\n/gm],
  ["coefficient compatibility", /^  requires entries :.*\n/gm],
  ["the nonzero coordinate for roots", /^  requires nonzero :.*\n/gm],
  ["the domain condition for roots", /^  requires domain :.*\n/gm],
] as const) {
  test(`characteristic polynomial applications require ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("characteristic shorthand elaborates to the exact explicit formulas", () => {
  const header = `module CharacteristicNotation
namespace CharacteristicNotation
import Grace.Cumulus.Algebra.Polynomial.Characteristic
section Rings
variable (n I A add zero neg mul one M x v j h : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
  const make = (ring: string) => header + `theorem matrix
  shows characteristicMatrix(n, ${ring}, M, x) = h → h = characteristicMatrix(n, ${ring}, M, x)
proof
  intro equation
  cc
theorem polynomial
  shows characteristicPolynomial(n, I, ${ring}, M, j) = h → h = characteristicPolynomial(n, I, ${ring}, M, j)
proof
  intro equation
  cc
theorem eigenvector
  shows LeftEigenvector(n, ${ring}, M, x, v) → LeftEigenvector(n, ${ring}, M, x, v)
proof
  intro evidence
  exact evidence
end Rings
end CharacteristicNotation
`;
  const short = load(make("R"));
  const full = load(make("A, add, zero, neg, mul, one"));
  for (const suffix of ["matrix", "polynomial", "eigenvector"]) {
    const name = `CharacteristicNotation.${suffix}`;
    assert.ok(formulaEquals(short.theorems.get(name)!, full.theorems.get(name)!));
  }
});

test("characteristic proof histories retain scoped notation on cold and cached checks", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "CharacteristicPolynomial.g17", source }], "ZF", ["CharacteristicPolynomial.g17"]);
    const theorem = result.theorems.find(t => t.name === "CharacteristicPolynomialExample.annihilate")!;
    assert.ok(theorem);
    assert.equal(theorem.sorries.length, 0);
    assert.match(theorem.statement, /LeftEigenvector\(n, S, N,/);
    assert.match(theorem.statement, /characteristicPolynomial\(n, I, R, M, j\)/);
    assert.ok(theorem.steps.length);
    assert.match(JSON.stringify(theorem.steps), /characteristicPolynomial\(n, I, R, M, j\)/);
  }
});
