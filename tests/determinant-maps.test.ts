// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/DeterminantMaps.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "DeterminantMaps.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("finite algebra and determinant transport are hereditarily admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Algebra\.(Ring\.(FiniteHom|DeterminantHom)|Polynomial\.Determinant)\./.test(name) ||
    name.startsWith("DeterminantMaps."));
  assert.ok(names.length >= 19, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["a ring homomorphism", /^hypothesis hom :.*\n/m],
  ["the entrywise relation", /^  requires entries :.*\n/m],
  ["a well-typed polynomial assignment", /^hypothesis assignment :.*\n/m],
] as const) {
  test(`determinant transport requires ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("polynomial determinant goals keep both ring scopes on cold and cached Workbench checks", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  for (let pass = 0; pass < 2; pass++) {
    const result = checkWorkbenchFiles([{ name: "DeterminantMaps.g17", source }], "ZF", ["DeterminantMaps.g17"]);
    const theorem = result.theorems.find(t => t.name === "DeterminantMaps.evaluate")!;
    assert.ok(theorem);
    assert.equal(theorem.sorries.length, 0);
    assert.match(theorem.statement, /determinant\(n, P, M\)/);
    assert.match(theorem.statement, /determinant\(n, R, N\)/);
    assert.ok(theorem.steps.length);
    assert.match(JSON.stringify(theorem.steps), /determinant\(n, P, M\)/);
  }
});
