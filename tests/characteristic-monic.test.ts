// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const source = readFileSync("examples/CharacteristicMonic.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "CharacteristicMonic.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("Characteristic monicity and indexed eigenvector annihilation are admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Algebra\.Polynomial\.(HornerArithmetic|HornerForms|AffineDeterminant|CharacteristicMonic)\./.test(name) ||
    name.startsWith("CharacteristicMonicExample."));
  assert.ok(names.length >= 30, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["affine matrix entries", /^  requires entries :.*M\[r, c\].*\n/gm],
  ["compatible coefficient maps", /^  requires entries :.*N\[r, c\].*\n/gm],
  ["an eigenvector equation", /^  requires eigenvector :.*\n/gm],
  ["a typed source matrix", /^  requires matrixM :.*\n/gm],
] as const) {
  test(`monic applications require ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("characteristic monicity proof histories preserve mathematical notation on cold and cached checks", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "CharacteristicMonic.g17", source }], "ZF", ["CharacteristicMonic.g17"]);
    const theorem = result.theorems.find(t => t.name === "CharacteristicMonicExample.monic")!;
    assert.ok(theorem);
    assert.equal(theorem.sorries.length, 0);
    assert.match(theorem.statement, /characteristicPolynomial\(n, I, R, M, j\)/);
    assert.ok(theorem.steps.length);
    assert.match(JSON.stringify(theorem.steps), /characteristicPolynomial\(n, I, R, M, j\)/);
  }
});
