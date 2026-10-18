// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialVariableCoefficients.g17", "utf8");
const prefix = "module PolynomialVariableCoefficients\nnamespace PolynomialVariableCoefficients\nimport Grace.Cumulus.Algebra.Polynomial.VariableExpansion\n";
const suffix = "\nend PolynomialVariableCoefficients\n";
function load(text: string) {
  const k = createZfKernel();
  loadModuleSourceGraph(k, [{ file: "PolynomialVariableCoefficients.g17", source: text }], ["lib"]);
  return k;
}

test("variable coefficient extraction and finite expansion have complete hereditary ZF audits", () => {
  const k = createZfKernel();
  loadModuleGraph(k, ["examples/PolynomialVariableCoefficients.g17"], ["lib"]);
  const names = [...k.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.Variable(Coefficients|Expansion)\./.test(n)
    || n.startsWith("PolynomialVariableCoefficients."));
  assert.equal(names.length, 38);
  for (const name of names) {
    const audit = auditTheoremAxioms(k, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

const recovery = prefix + `theorem recovery (I A z p j m : Set)
  requires zeroIn : z ∈ A
  requires polynomial : p ∈ polynomials(I, A, z)
  requires member : m ∈ monomials(I)
  requires index : j ∈ I
  shows polynomialVariableCoefficient(I, A, z, p, j, m(j))(coefficientErase(I, ℕ, 0, m, j)) = p(m)
proof
  exact polynomialVariableCoefficient.recover at I, A, z, p, j, m with *
` + suffix;
for (const premise of ["zeroIn", "polynomial", "member", "index"]) {
  test(`coefficient recovery rejects missing ${premise}`, () => {
    load(recovery);
    const incomplete = recovery.replace(new RegExp(`^  requires ${premise} :.*\\n`, "m"), "");
    assert.notEqual(incomplete, recovery);
    assert.throws(() => load(incomplete), /cannot find evidence/);
  });
}

test("a coefficient index must be a natural number", () => {
  const valid = prefix + `theorem coefficient (I A z p j : Set, n : Nat)
  requires zeroIn : z ∈ A
  requires polynomial : p ∈ polynomials(I, A, z)
  shows polynomialVariableCoefficient(I, A, z, p, j, n) ∈ polynomials(I, A, z)
proof
  exact polynomialVariableCoefficient.member at I, A, z, p, j, n with *
` + suffix;
  load(valid);
  assert.throws(() => load(valid.replace("n : Nat", "n : Set")), /cannot find evidence/);
});

for (const premise of ["index", "nonzero"]) {
  test(`nonzero coefficient witness requires ${premise}`, () => {
    const valid = prefix + `theorem witness (I A z p j : Set)
  requires zeroIn : z ∈ A
  requires polynomial : p ∈ polynomials(I, A, z)
  requires index : j ∈ I
  requires nonzero : p ≠ constantFunction(monomials(I), A, z)
  shows ∃ n ∈ ℕ, polynomialVariableCoefficient(I, A, z, p, j, n) ≠ constantFunction(monomials(I), A, z)
proof
  exact polynomialVariableCoefficient.exists_nonzero at I, A, z, p, j with *
` + suffix;
    load(valid);
    assert.throws(() => load(valid.replace(new RegExp(`^  requires ${premise} :.*\\n`, "m"), "")), /cannot find evidence/);
  });
}

test("coefficient evaluation cannot discard agreement on the remaining coordinates", () => {
  const incomplete = source.replace(/^  requires agreement :.*\n/m, "").replace("agree_away with *", "agree_away at I, A, add, z, neg, mul, one, p, j, v, w, n with *");
  assert.throws(() => load(incomplete), /cannot find evidence/);
});

test("scoped coefficient and coefficient-family terms preserve exact formulas and proof programs", () => {
  const context = prefix + `section Rings
variable (I A add z neg mul one p j : Set)
notation ring R := (A, add, z, neg, mul, one)
`;
  for (const [short, full] of [
    ["polynomialVariableCoefficient(I, R, p, j, n)", "polynomialVariableCoefficient(I, A, z, p, j, n)"],
    ["polynomialCoefficientFamily(I, R, p, j)", "polynomialCoefficientFamily(I, A, z, p, j)"],
  ]) {
    const body = (term: string) => `theorem syntax (n : Nat)\n  shows ${term} = ${term}\nproof\n  rfl\nend Rings\n`;
    const a = load(context + body(short) + suffix);
    const b = load(context + body(full) + suffix);
    const name = "PolynomialVariableCoefficients.syntax";
    assert.ok(formulaEquals(a.theorems.get(name)!, b.theorems.get(name)!));
    const proof = compileProofModule([exportTheoremForMachine(a, name)]);
    assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(b, name)]));
    verifyProofMachine(a, proof);
  }
});

test("completed and cached coefficient goals retain scoped notation", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialVariableCoefficients.g17", source }], "ZF", ["PolynomialVariableCoefficients.g17"]);
    const theorem = result.theorems.find(t => t.name === "PolynomialVariableCoefficients.coefficient_is_polynomial");
    assert.ok(theorem);
    assert.match(theorem.statement, /polynomialVariableCoefficient\(I, R, p, j, n\)/);
    assert.match(JSON.stringify(theorem.steps), /polynomialVariableCoefficient\(I, R, p, j, n\)/);
  }
});
