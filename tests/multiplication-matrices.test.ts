// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const source = readFileSync("examples/MultiplicationMatrices.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "MultiplicationMatrices.g17", source: text }], ["lib"]);
  return kernel;
}

test("indexed lists and general multiplication matrices have complete hereditary ZF audits", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Algebra.(IndexedLists|MultiplicationMatrix)\./.test(name)
    || name === "Grace.Cumulus.Nat.Foundation.natural.member"
    || name.startsWith("MultiplicationMatrices."));
  assert.ok(names.length >= 25);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited in ZF, including empty and repeated generators`);
});

for (const premise of ["sameLength", "entries", "source", "target", "hom", "element", "finiteModule", "rowLengths", "row", "size", "coefficients"]) {
  test(`list and multiplication-matrix applications retain ${premise}`, () => {
    const declaration = premise === "element" ? "hypothesis" : "(?:hypothesis|  requires)";
    const text = source.replace(new RegExp(`^${declaration} ${premise} :.*\\n`, "gm"), "");
    assert.throws(() => load(text), /cannot find evidence|cannot uniquely infer|conclusion does not match/);
  });
}

test("multiplication-matrix statement retains the actual multiplier", () => {
  const text = source.replace("S[x * listCoefficient{B}(z, xs, i)]", "S[x * x]");
  assert.throws(() => load(text), /conclusion does not match/);
});

test("repeated generators are not collapsed to a single position", () => {
  const text = source.replace("length{A}([a, a]) = 2", "length{A}([a, a]) = 1");
  assert.throws(() => load(text), /rfl|reflexiv|goal/);
});

test("cold and cached Workbench states preserve scoped square-matrix statements", () => {
  for (let pass = 0; pass < 2; pass++) {
    const checked = checkWorkbenchFiles([{ name: "MultiplicationMatrices.g17", source }], "ZF", ["MultiplicationMatrices.g17"]);
    const theorem = checked.theorems.find(t => t.name === "MultiplicationMatrices.square_multiplication_matrix")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length);
    assert.match(theorem.statement, /RingMatrix\(.*R, M\)/);
    assert.match(theorem.statement, /linearCombination\(R, S, f, xs, cs\)/);
    for (const name of ["lists_are_determined_by_entries", "positions_cover_the_support", "repeated_generators_keep_both_positions", "empty_list_has_no_positions", "recover_a_coefficient_row"]) {
      assert.ok(checked.theorems.find(t => t.name === `MultiplicationMatrices.${name}`)?.steps.length, name);
    }
  }
});
