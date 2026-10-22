// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialRoots.g17", "utf8");

test("synthetic division, finite roots, and nonvanishing have complete hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialRoots.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.(Horner|HornerRoots)\./.test(n)
    || n === "Grace.Core.List.List.cases" || n.startsWith("PolynomialRoots."));
  assert.equal(names.length, 18); // Includes two checked generalized-induction auxiliaries.
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const [premise, expected] of [
  ["field", /cannot find evidence.*IsField/],
  ["nonzero", /cannot find evidence/],
  ["infinite", /cannot find evidence.*Finite/],
  ["excluded", /cannot find evidence.*Finite/],
] as const) {
  test(`root/nonvanishing conclusions cannot discard ${premise}`, () => {
    let incomplete = source.replace(new RegExp(`^\\s*(hypothesis|requires) ${premise} :.*\\n`, "m"), "\n");
    if (premise === "field") incomplete = incomplete.replace("hornerRoots.finite with *", "hornerRoots.finite at A, add, z, neg, mul, one, leading, cs with *");
    assert.notEqual(incomplete, source);
    assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "PolynomialRoots.g17", source: incomplete }], ["lib"]), expected);
  });
}

test("guarded polynomial applications retain completed and cached goal history", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialRoots.g17", source }], "ZF", ["PolynomialRoots.g17"]);
    const checked = result.theorems.find(t => t.name === "PolynomialRoots.nonvanishing");
    assert.ok(checked);
    assert.match(checked.statement, /hornerAt/);
    assert.match(JSON.stringify(checked.steps), /hornerAt/);
  }
});
