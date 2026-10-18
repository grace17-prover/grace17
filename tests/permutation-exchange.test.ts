// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const source = readFileSync("examples/PermutationExchange.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PermutationExchange.g17", source: text }], ["lib"]);
  return kernel;
}

test("actual transposition graphs, permutation pairing, and product invariance are proved in ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    name.startsWith("Grace.Cumulus.Set.Transposition.") ||
    name.startsWith("Grace.Cumulus.Cardinal.PermutationExchange.") ||
    name.startsWith("Grace.Cumulus.Algebra.Ring.DeterminantCancellation.") ||
    name.startsWith("PermutationExchange."));
  assert.ok(names.includes("Grace.Cumulus.Cardinal.PermutationExchange.permutationExchange.free"));
  assert.ok(names.includes("Grace.Cumulus.Algebra.Ring.DeterminantCancellation.permutationEntries.exchange_product"));
  assert.ok(names.includes("PermutationExchange.coincident_choices"));
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} entries audited in ZF; the lower-level conditional helper retains its explicit sign premise`);
});

for (const premise of ["ha", "hb", "distinct", "rows", "signs"]) {
  test(`the row-exchange API retains ${premise}`, () => {
    const changed = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}
