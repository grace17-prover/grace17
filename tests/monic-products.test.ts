// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const source = readFileSync("examples/MonicProducts.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "MonicProducts.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("Horner coefficients, monic factors, and extension bridges are admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Algebra\.Polynomial\.(HornerDegree|HornerExtension|MonicProducts)\./.test(name) ||
    name.startsWith("MonicProductsExample."));
  assert.ok(names.length >= 26, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["a nontrivial ring for nonvanishing", /^  requires nontrivial :.*\n/gm],
  ["the first nonzero leading coefficient", /^  requires leftNonzero :.*\n/gm],
  ["the second nonzero leading coefficient", /^  requires rightNonzero :.*\n/gm],
  ["a genuine variable index", /^hypothesis index :.*\n/gm],
  ["a proved characteristic representation", /^  requires representation :.*\n/gm],
] as const) {
  test(`monic polynomial applications require ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("scoped linear factors preserve the explicit statement", () => {
  const make = (ring: string) => `module MonicNotation
namespace MonicNotation
import Grace.Cumulus.Algebra.Polynomial.MonicProducts
section Rings
variable (I A add zero neg mul one j xs h : Set)
notation ring R := (A, add, zero, neg, mul, one)
theorem equality
  shows polynomialLinearFactors(I, ${ring}, j, xs) = h → h = polynomialLinearFactors(I, ${ring}, j, xs)
proof
  intro equation
  cc
end Rings
end MonicNotation
`;
  const short = load(make("R"));
  const full = load(make("A, add, zero, neg, mul, one"));
  assert.ok(formulaEquals(short.theorems.get("MonicNotation.equality")!, full.theorems.get("MonicNotation.equality")!));
});

test("monic factor proof histories preserve mathematical notation on cold and cached checks", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "MonicProducts.g17", source }], "ZF", ["MonicProducts.g17"]);
    const theorem = result.theorems.find(t => t.name === "MonicProductsExample.factor")!;
    assert.ok(theorem);
    assert.equal(theorem.sorries.length, 0);
    assert.match(theorem.statement, /polynomialLinearFactors\(I, R, j,/);
    assert.ok(theorem.steps.length);
    assert.match(JSON.stringify(theorem.steps), /polynomialLinearFactors\(I, R, j,/);
  }
});
