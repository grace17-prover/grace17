// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = `module Contracts
namespace Contracts
import Grace.Cumulus.Algebra.Field.IntegralDescent
section Rings
variable (A add zero neg mul one B plus z minus times unit f : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
hypothesis source : IsCommRing(R)
hypothesis field : IsField(S)
hypothesis hom : IsRingHom(f, R, S)
`;
const end = "end Rings\nend Contracts\n";
function load(body: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Contracts.g17", source: header + body + end }], ["lib"]);
  return kernel;
}

test("integral inverse and field descent have complete hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/IntegralDescent.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name => /^(Grace.Cumulus.Algebra.(IntegralInverse|Field.IntegralDescent)\.|IntegralDescent\.)/.test(name));
  assert.ok(names.length >= 6, `${names.length} boundaries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("field descent cannot discard injectivity", () => {
  assert.throws(() => load(`theorem invalid
  requires integral : ∀ y ∈ S, IntegralOver(f, R, S, y)
  shows IsField(R)
proof
  exact IsField.of_integral_extension with *
`), /cannot find evidence for InjectiveBetween/);
});

test("field descent cannot discard integrality", () => {
  assert.throws(() => load(`theorem invalid
  requires embedding : InjectiveBetween(f, R, S)
  shows IsField(R)
proof
  exact IsField.of_integral_extension with *
`), /cannot find evidence for .*IntegralOver/);
});

test("goal-directed exact proofs retain completed and cached goal histories", () => {
  const source = readFileSync("examples/IntegralDescent.g17", "utf8");
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "IntegralDescent.g17", source }], "ZF", ["IntegralDescent.g17"]);
    const theorem = result.theorems.find(t => t.name === "IntegralDescent.field_descends");
    assert.ok(theorem);
    assert.match(theorem.statement, /IsField\(R\)/);
    assert.match(JSON.stringify(theorem.steps), /IsField\(R\)/);
  }
});
