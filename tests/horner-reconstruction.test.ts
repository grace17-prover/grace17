// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialReconstruction.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PolynomialReconstruction.g17", source: text }], ["lib"]);
  return kernel;
}

test("monomial shifts and sparse reconstruction have complete hereditary ZF audits", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.(MonomialShift|HornerReconstruction)\./.test(n)
    || n.startsWith("PolynomialReconstruction."));
  assert.ok(names.length >= 20);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const premise of ["ring", "polynomial", "index", "coefficients", "nonzero", "assignment"]) {
  test(`reconstruction applications require ${premise}`, () => {
    // Explicit instantiation isolates missing evidence from argument inference.
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "")
      .replace("polynomials.exists_coefficient_horner with", "polynomials.exists_coefficient_horner at I, A, add, z, neg, mul, one, p, j with")
      .replace("polynomialFromCoefficients.reconstruct with", "polynomialFromCoefficients.reconstruct at I, A, add, z, neg, mul, one, p, j, cs with")
      .replace("polynomials.exists_nonzero_coefficient_horner with", "polynomials.exists_nonzero_coefficient_horner at I, A, add, z, neg, mul, one, p, j with")
      .replace("polynomialAt.reconstruction with", "polynomialAt.reconstruction at I, A, add, z, neg, mul, one, p, j, v, cs with");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

const coefficientLaw = `module PolynomialReconstruction
namespace PolynomialReconstruction
import Grace.Cumulus.Algebra.Polynomial.HornerReconstruction
theorem lookup (I A add z neg mul one j m : Set) (cs : List(polynomials(I, A, z))) (n : Nat)
  requires ring : IsCommRing(A, add, z, neg, mul, one)
  requires index : j ∈ I
  requires monomial : m ∈ monomials(I)
  requires absent : m(j) = 0
  requires omitted : coefficientsOmitVariable(I, A, z, j, cs)
  shows polynomialFromCoefficients(I, A, add, z, neg, mul, one, j, cs)(monomialShift(I, j, m, n)) = listCoefficient{polynomials(I, A, z)}(constantFunction(monomials(I), A, z), cs, n)(m)
proof
  exact polynomialFromCoefficients.coefficient at I, A, add, z, neg, mul, one, j, m, cs, n with *
end PolynomialReconstruction
`;

test("Horner coefficient lookup requires both independence and zero base exponent", () => {
  load(coefficientLaw);
  for (const premise of ["omitted", "absent"]) {
    assert.throws(() => load(coefficientLaw.replace(new RegExp(`^  requires ${premise} :.*\\n`, "m"), "")), /cannot find evidence/);
  }
});

test("completed and cached reconstruction goals retain the scoped polynomial expression", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialReconstruction.g17", source }], "ZF", ["PolynomialReconstruction.g17"]);
    const theorem = result.theorems.find(t => t.name === "PolynomialReconstruction.reconstruction")!;
    assert.ok(theorem);
    assert.match(theorem.statement, /polynomialFromCoefficients\(I, R, j, cs\) = p/);
    assert.ok(theorem.steps.length);
  }
});
