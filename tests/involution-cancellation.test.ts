// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/InvolutionCancellation.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "InvolutionCancellation.g17", source: text }], ["lib"]);
  return kernel;
}

test("finite involution and determinant cancellation are admission-free in ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Algebra.Ring.Cancellation.") ||
    name.startsWith("Grace.Cumulus.Algebra.Ring.DeterminantCancellation.") ||
    name.startsWith("InvolutionCancellation."));
  assert.equal(names.length, 11);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} entries audited in ZF`);
});

// In particular, sign reversal alone does not handle fixed points in
// characteristic two. Neither finite-ness nor the pairing laws are optional.
for (const premise of ["finite", "weights", "involution", "opposite", "fixed", "free", "matrix", "signs", "products"]) {
  test(`cancellation retains the ${premise} obligation`, () => {
    const changed = source.replace(new RegExp(`^  requires ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}
