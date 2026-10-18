// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/Determinants.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Determinants.g17", source: text }], ["lib"]);
  return kernel;
}

test("finite row selection and determinants have complete hereditary ZF audits", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Cardinal.Permutations\./.test(name)
    || /^Grace.Cumulus.Algebra.(CoefficientMatrix|Ring.Determinant|Ring.DeterminantZero)\./.test(name)
    || name === "Grace.Cumulus.Set.Function.FunctionBetween.empty"
    || name === "Grace.Cumulus.Set.Finite.FiniteSet.insert.restore"
    || name.startsWith("Determinants."));
  assert.ok(names.length >= 25);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited in ZF`);
});

for (const premise of ["ring", "matrix", "other", "entries", "row", "vanishes", "source", "target", "hom", "element", "finiteModule"]) {
  test(`determinant and row-selection applications retain ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("the empty determinant cannot be replaced by zero", () => {
  const text = source.replace("shows determinant(∅, R, M) = R[1]", "shows determinant(∅, R, M) = R[0]");
  assert.throws(() => load(text), /conclusion does not match the goal/);
});

test("cold and cached Workbench states display scoped determinant notation", () => {
  for (let pass = 0; pass < 2; pass++) {
    const checked = checkWorkbenchFiles([{ name: "Determinants.g17", source }], "ZF", ["Determinants.g17"]);
    const theorem = checked.theorems.find(t => t.name === "Determinants.zero_row")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length);
    assert.match(theorem.statement, /determinant\(n, R, M\)/);
    assert.match(theorem.statement, /RingMatrix\(n, R, M\)/);
    const rows = checked.theorems.find(t => t.name === "Determinants.select_all_multiplication_rows")!;
    assert.ok(rows.steps.length);
    assert.match(rows.statement, /linearCombination\(R, S, f, xs, rows\(g\)\)/);
  }
});

test("matrix, sign and determinant shorthand preserve formulas and compiled proofs", () => {
  const prefix = `module Syntax
namespace Syntax
import Grace.Cumulus.Algebra.Ring.Determinant
section Rings
variable (I A add zero neg mul one M p : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
  const forms = [
    ["RingMatrix(I, R, M)", "RingMatrix(I, A, M)"],
    ["determinant(I, R, M) = determinant(I, R, M)", "determinant(I, A, add, zero, neg, mul, one, M) = determinant(I, A, add, zero, neg, mul, one, M)"],
    ["permutationSign(I, R, p) = permutationSign(I, R, p)", "permutationSign(I, A, add, zero, neg, mul, one, p) = permutationSign(I, A, add, zero, neg, mul, one, p)"],
  ];
  const body = (variant: number) => forms.map((f, i) => `theorem form${i}\n  requires evidence : ${f[variant]}\n  shows ${f[variant]}\nproof\n  exact evidence\n`).join("\n") + "end Rings\nend Syntax\n";
  const compact = load(prefix + body(0));
  const expanded = load(prefix + body(1));
  for (let i = 0; i < forms.length; i++) {
    const name = `Syntax.form${i}`;
    assert.ok(formulaEquals(compact.theorems.get(name)!, expanded.theorems.get(name)!));
    const proof = compileProofModule([exportTheoremForMachine(compact, name)]);
    assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(expanded, name)]));
    verifyProofMachine(compact, proof);
  }
});
