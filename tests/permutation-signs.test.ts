// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/PermutationSigns.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PermutationSigns.g17", source: text }], ["lib"]);
  return kernel;
}

test("inversion-count exchange signs and unconditional equal-row cancellation are proved in ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Cardinal.Counting.") ||
    name.startsWith("Grace.Cumulus.Cardinal.InversionExchange.") ||
    name.startsWith("Grace.Cumulus.Algebra.Ring.PermutationSign.") ||
    name.startsWith("PermutationSigns.") ||
    /(?:InvolutionOn\.restrict_between|transposition\.(?:symmetric|conjugate)|permutationExchange\.(?:symmetric|conjugate)|Less\.(?:successor_lower_of_ne|of_successor_upper_ne))$/.test(name)).filter(name => !name.endsWith(".generalized_induction_aux"));
  assert.equal(names.length, 34);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  assert.doesNotMatch(source, /requires signs/);
  t.diagnostic(`${names.length} entries audited in ZF; no sign premise on the equal-row example`);
});

for (const premise of ["ha", "hb", "distinct", "permutation", "matrix", "rows", "finite", "fresh"]) {
  test(`permutation signs and counting retain ${premise}`, () => {
    const changed = source.replace(new RegExp(`^  requires ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}
