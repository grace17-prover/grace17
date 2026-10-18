// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const source = readFileSync("examples/Adjugate.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "Adjugate.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("cofactor expansion, actual adjugates, and kernel annihilation are admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Algebra\.Ring\.(WeightedRegrouping|Cofactors|Adjugate|DeterminantKernel)\./.test(name) ||
    name.endsWith("FiniteLinearity.finiteRingSum.scale_eq") || name.startsWith("AdjugateExample."));
  assert.ok(names.length >= 45, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["distinct indices for off-diagonal vanishing", /^  requires distinct :.*\n/m],
  ["the kernel equation for annihilation", /^  requires kernel :.*\n/m],
  ["a nonzero coordinate for singularity", /^  requires nonzero :.*\n/m],
  ["the domain assumption when concluding determinant zero", /^  requires domain :.*\n/m],
] as const) {
  test(`the adjugate consequences require ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}


test("cofactor, adjugate, and kernel shorthand preserves exact formulas", () => {
  const header = `module AdjugateNotation
namespace AdjugateNotation
import Grace.Cumulus.Algebra.Ring.DeterminantKernel
section Rings
variable (n A add zero neg mul one M N v i j h : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
  const terms = [
    ["cofactorTerms", "M, i"], ["cofactorRow", "M, i"],
    ["cofactorPairWeights", "M, N, i, j"], ["cofactorPairing", "M, N, i, j"],
    ["adjugate", "M"], ["matrixProductWeights", "M, N, i, j"],
    ["matrixProductEntry", "M, N, i, j"], ["rowVectorWeights", "v, M, j"],
    ["rowVectorEntry", "v, M, j"], ["adjugateContraction", "v, M, j"],
  ];
  const make = (ring: string) => header + terms.map(([name, tail], i) =>
    `theorem form${i}\n  shows ${name}(n, ${ring}, ${tail}) = h → h = ${name}(n, ${ring}, ${tail})\nproof\n  intro equation\n  cc\n`
  ).join("\n") + `theorem kernel\n  shows LeftKernelVector(n, ${ring}, M, v) → LeftKernelVector(n, ${ring}, M, v)\nproof\n  intro evidence\n  exact evidence\nend Rings\nend AdjugateNotation\n`;
  const short = load(make("R"));
  const full = load(make("A, add, zero, neg, mul, one"));
  for (const suffix of [...terms.map((_, i) => `form${i}`), "kernel"]) {
    const name = `AdjugateNotation.${suffix}`;
    assert.ok(formulaEquals(short.theorems.get(name)!, full.theorems.get(name)!));
  }
  assert.deepEqual([...short.axioms.keys()], [...full.axioms.keys()]);
});

test("adjugate and kernel proof histories retain mathematical notation on cached checks", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "Adjugate.g17", source }], "ZF", ["Adjugate.g17"]);
    const theorem = result.theorems.find(t => t.name === "AdjugateExample.annihilate")!;
    assert.ok(theorem);
    assert.equal(theorem.sorries.length, 0);
    assert.match(theorem.statement, /LeftKernelVector\(n, R, M, v\)/);
    assert.match(theorem.statement, /determinant\(n, R, M\)/);
    assert.ok(theorem.steps.length);
    assert.match(JSON.stringify(theorem.steps), /determinant\(n, R, M\)/);
  }
});
