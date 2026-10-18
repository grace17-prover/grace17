// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialCoefficientLists.g17", "utf8");
const prefix = "module PolynomialCoefficientLists\nnamespace PolynomialCoefficientLists\nimport Grace.Cumulus.Algebra.Polynomial.CoefficientHorner\n";
const suffix = "\nend PolynomialCoefficientLists\n";
function load(text: string) {
  const k = createZfKernel();
  loadModuleSourceGraph(k, [{ file: "PolynomialCoefficientLists.g17", source: text }], ["lib"]);
  return k;
}

test("finite coefficient lists and the Horner homomorphism bridge have complete ZF audits", () => {
  const k = createZfKernel();
  loadModuleGraph(k, ["examples/PolynomialCoefficientLists.g17"], ["lib"]);
  const names = [...k.theorems.keys()].filter(n =>
    n.startsWith("Grace.Cumulus.Algebra.CoefficientLists.")
    || /^Grace.Cumulus.Algebra.Polynomial.(HornerHom|CoefficientHorner)\./.test(n)
    || n.startsWith("PolynomialCoefficientLists."));
  assert.ok(names.length >= 29, "the audited API must retain its original coverage");
  assert.ok(names.includes("Grace.Cumulus.Algebra.Polynomial.HornerHom.hornerValue.synthetic_division"));
  for (const name of names) {
    const audit = auditTheoremAxioms(k, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("a finite window requires the lookup index to be below its length", () => {
  const body = prefix + `theorem lookup (A z f : Set, start n k : Nat)
  requires function : FunctionBetween(f, ℕ, A)
  requires bound : k < n
  shows listCoefficient{A}(z, coefficientWindow(f, start, n), k) = f(start + k)
proof
  exact coefficientWindow.coefficient at A, z, f, start, n, k with *
` + suffix;
  load(body);
  assert.throws(() => load(body.replace(/^  requires bound :.*\n/m, "")), /cannot find evidence/);
});

test("finite-list representation cannot be inferred from a function without finite support", () => {
  assert.throws(() => load(prefix + `theorem invalid (A z f : Set)
  requires function : FunctionBetween(f, ℕ, A)
  shows ∃ cs, List(A, cs) ∧ (∀ n, Nat(n) → listCoefficient{A}(z, cs, n) = f(n))
proof
  exact CoefficientMap.list_representation at A, z, f with *
` + suffix), /cannot find evidence/);
});

for (const premise of ["assignment", "index"]) {
  test(`Horner polynomial evaluation requires ${premise}`, () => {
    const incomplete = source.replace(new RegExp(`^  requires ${premise} :.*\\n`, "gm"), "")
      .replace("polynomialCoefficientFamily.list_representation with *", "polynomialCoefficientFamily.list_representation at I, A, z, p, j with *")
      .replace("polynomialAt.coefficient_horner with *", "polynomialAt.coefficient_horner at I, A, add, z, neg, mul, one, j, v, cs with *");
    // For index, isolate the evaluation theorem so rejection exercises that law.
    const evaluationOnly = incomplete.replace(/theorem coefficient_list[\s\S]*?(?=theorem horner_is_polynomial)/, "");
    assert.throws(() => load(evaluationOnly), /cannot find evidence/);
  });
}

test("polynomial-coefficient Horner scope has exactly the expanded meaning", () => {
  const context = prefix + `section Rings
variable (I A add z neg mul one j : Set)
notation ring R := (A, add, z, neg, mul, one)
notation ring P := R[I]
`;
  const body = (term: string) => `theorem syntax (cs : List(P))\n  shows ${term} = ${term}\nproof\n  rfl\nend Rings\n`;
  const a = load(context + body("polynomialFromCoefficients(I, R, j, cs)") + suffix);
  const b = load(context + body("polynomialFromCoefficients(I, A, add, z, neg, mul, one, j, cs)") + suffix);
  const name = "PolynomialCoefficientLists.syntax";
  assert.ok(formulaEquals(a.theorems.get(name)!, b.theorems.get(name)!));
  const proof = compileProofModule([exportTheoremForMachine(a, name)]);
  assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(b, name)]));
  verifyProofMachine(a, proof);
});

test("completed and cached Horner evaluation goals retain coefficient scope", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialCoefficientLists.g17", source }], "ZF", ["PolynomialCoefficientLists.g17"]);
    const theorem = result.theorems.find(t => t.name === "PolynomialCoefficientLists.evaluate_horner")!;
    assert.ok(theorem);
    assert.match(theorem.statement, /polynomialFromCoefficients\(I, R, j, cs\)/);
    assert.ok(theorem.steps.length);
  }
});
