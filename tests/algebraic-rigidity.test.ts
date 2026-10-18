// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/AlgebraicRigidity.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "AlgebraicRigidity.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("synthetic division along homomorphisms and algebraic rigidity are admission-free ZF", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Algebra.(Polynomial.HornerHom|Field.Rigidity)\./.test(name)
    || name.startsWith("AlgebraicRigidity."));
  assert.equal(names.length, 13);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
});

for (const premise of ["closed", "field", "hom", "algebraic"]) {
  test(`algebraic rigidity retains its ${premise} premise`, () => {
    const changed = source.replace(new RegExp(`^(?:  requires|hypothesis) ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}
