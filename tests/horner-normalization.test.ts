// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/HornerNormalization.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "HornerNormalization.g17", source: text }], ["lib"]);
  return kernel;
}

test("trailing-zero normalization and finite-root applications are hereditary ZF proofs", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n =>
    n.startsWith("Grace.Cumulus.Algebra.Polynomial.HornerNormalization.") || n.startsWith("HornerNormalization."));
  assert.equal(names.length, 9); // Five laws and four examples; canonical binder order needs no auxiliary.
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const premise of ["field", "infinite", "excluded", "nonzero"]) {
  test(`finite-root applications require ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "")
      .replaceAll("hornerRoots.finite_of_coefficient with", "hornerRoots.finite_of_coefficient at A, add, z, neg, mul, one, cs with")
      .replace("hornerAt.exists_nonzero_of_coefficient with", "hornerAt.exists_nonzero_of_coefficient at A, add, z, neg, mul, one, cs with")
      .replace("hornerAt.exists_nonzero_avoiding_of_coefficient with", "hornerAt.exists_nonzero_avoiding_of_coefficient at A, add, z, neg, mul, one, F, cs with")
      .replace(/theorem trailing_zeros[\s\S]*?(?=end Fields)/, "");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("normalization goals remain available on cold and cached checks", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "HornerNormalization.g17", source }], "ZF", ["HornerNormalization.g17"]);
    const theorem = result.theorems.find(t => t.name === "HornerNormalization.trailing_zeros")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length > 3);
    assert.match(theorem.statement, /hornerRoots/);
  }
});
