// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/AlgebraicallyClosedFields.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "AlgebraicallyClosedFields.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("explicit monic vanishing polynomials and algebraically closed infinitude are admission-free ZF", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Algebra.(Polynomial.MonicVanishing|Field.Infinite)\./.test(name)
    || name.startsWith("AlgebraicallyClosedFields."));
  assert.equal(names.length, 8);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
});

for (const premise of ["closed", "ring"]) {
  test(`field infinitude and polynomial construction retain the ${premise} premise`, () => {
    const changed = source.replace(new RegExp(`^  requires ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}
