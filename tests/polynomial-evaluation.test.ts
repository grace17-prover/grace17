// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const header = `module EvalSyntax
import Grace.Cumulus.Algebra.Polynomial.EvaluationHom
section Rings
variable (I A add zero neg mul one : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring P := R[I]
`;
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "EvalSyntax.g17", source }], ["lib"]);
  return kernel;
}

test("polynomial evaluation and worked examples have complete choice-free audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialEvaluation.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n => /^(Grace.Cumulus.Algebra.Polynomial.Evaluation(Hom)?\.|PolynomialEvaluation\.)/.test(n));
  assert.ok(names.length >= 28);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("polynomial shorthand and carrier aliases elaborate exactly to the existing terms", () => {
  const body = `theorem identity (p : Set)
  requires hp : p ∈ P
  shows P[p + 0] = P[p + 0]
proof
  rfl
end Rings
`;
  const short = load(header + body);
  const explicit = load(header.replace("notation ring P := R[I]", "notation ring P := (polynomials(I, A, zero), polynomialAdd(I, A, add, zero, neg, mul, one), constantFunction(monomials(I), A, zero), polynomialNeg(I, A, add, zero, neg, mul, one), polynomialMul(I, A, add, zero, neg, mul, one), polynomialConstant(I, A, zero, one))") + body.replace("p ∈ P", "p ∈ polynomials(I, A, zero)"));
  assert.ok(formulaEquals(short.theorems.get("identity")!, explicit.theorems.get("identity")!));
});

test("iterated polynomial notation and ring carrier aliases remain scoped", () => {
  load(header + `notation ring Q := P[I]
theorem carrier
  shows Q = polynomials(I, P, P[0])
proof
  rfl
end Rings
`);
  assert.throws(() => load(header + `end Rings
theorem escaped
  shows P = P
proof
  rfl
`), /unknown variable or constant P/);
});

test("polynomial notation diagnoses missing imports and unknown coefficient scopes", () => {
  assert.throws(() => load(header.replace("R[I]", "Missing[I]")), /unknown coefficient ring notation Missing/);
  assert.throws(() => load(header.replace("Grace.Cumulus.Algebra.Polynomial.EvaluationHom", "Grace.Cumulus.Algebra.Ring")), /polynomial ring operation.*import Grace.Cumulus.Algebra.Polynomial.Ring/);
});

test("multiplicative evaluation cannot be inferred from an arbitrary function on monomials", () => {
  assert.throws(() => load(header + `theorem invalid (h p q : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires values : FunctionBetween(h, monomials(I), A)
  requires hp : p ∈ P
  requires hq : q ∈ P
  shows polynomialEvaluate(I, A, add, zero, neg, mul, one, h)(polynomialProduct(I, A, add, zero, neg, mul, one, p, q)) = R[polynomialEvaluate(I, A, add, zero, neg, mul, one, h)(p) * polynomialEvaluate(I, A, add, zero, neg, mul, one, h)(q)]
proof
  exact polynomialEvaluate.mul at I, A, add, zero, neg, mul, one, h, p, q with *
end Rings
`), /MonomialCharacter/);
});
