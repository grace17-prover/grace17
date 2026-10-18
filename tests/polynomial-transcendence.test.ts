// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialTranscendence.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PolynomialTranscendence.g17", source: text }], ["lib"]);
  return kernel;
}

test("transcendence, finite localization, and finite-module bridges have complete ZF audits", t => {
  const kernel = load(source);
  const extras = new Set([
    "Grace.Cumulus.Set.Function.restrict.nested",
    "Grace.Cumulus.Algebra.CoefficientLists.listMap.compose",
    "Grace.Cumulus.Algebra.Polynomial.EvaluationOver.polynomialAtOver.coefficient_image",
    "Grace.Cumulus.Algebra.IntegralFinite.integralGenerators.finite_module_enlarged",
  ]);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Algebra.Polynomial.(EvaluationSupport|Transfer|AlgebraicDependence|TranscendenceLocalization)\./.test(name)
    || /^Grace.Cumulus.Algebra.Field.(AlgebraicLocalization|FiniteAlgebraicLocalization)\./.test(name)
    || name.startsWith("Grace.Cumulus.Algebra.HornerRelations.")
    || name.startsWith("PolynomialTranscendence.") || extras.has(name));
  assert.ok(names.length >= 48);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited in ZF`);
});

for (const premise of ["source", "polynomial", "supported", "nonzero", "subset", "index", "outside", "field", "hom", "injective", "algebraic", "finite", "assignment", "independent", "maximal", "generates"]) {
  test(`transcendence applications retain ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("cold and cached finite-module goals preserve ordinary carrier sets and scoped rings", () => {
  for (let pass = 0; pass < 2; pass++) {
    const checked = checkWorkbenchFiles([{ name: "PolynomialTranscendence.g17", source }], "ZF", ["PolynomialTranscendence.g17"]);
    const theorem = checked.theorems.find(t => t.name === "PolynomialTranscendence.finite_over_one_localization")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length);
    assert.match(theorem.statement, /∃ s ∈ Q/);
    assert.match(theorem.statement, /FiniteAlgebraModule\(identity\(T\), T, S\)/);
    const transfer = checked.theorems.find(t => t.name === "PolynomialTranscendence.retain_used_variables")!;
    assert.match(transfer.statement, /polynomialTransfer\(J, I, R\)/);
  }
});

const syntaxPrefix = `module Syntax
namespace Syntax
import Grace.Cumulus.Algebra.Polynomial.TranscendenceLocalization
section Rings
variable (I J A add z neg mul one B plus o minus times unit f T K x s : Set)
notation ring R := (A, add, z, neg, mul, one)
notation ring S := (B, plus, o, minus, times, unit)
`;
const syntaxSuffix = "end Rings\nend Syntax\n";
test("transfer and carrier-only shorthand have identical formulas and checked proofs", () => {
  const predicates = [
    ["IntegralOver(f, T, S, x)", "IntegralOver(f, T, B, plus, o, times, unit, x)"],
    ["FiniteAlgebraModule(f, T, S)", "FiniteAlgebraModule(f, T, B, plus, o, minus, times)"],
    ["IntegralOver(f, T ∪ K, S, x)", "IntegralOver(f, T ∪ K, B, plus, o, times, unit, x)"],
  ];
  const terms = [
    ["polynomialTransfer(I, J, R)", "polynomialTransfer(I, J, A, add, z, neg, mul, one)"],
    ["linearSpan(f, T ∪ K, S, K)", "linearSpan(f, T ∪ K, B, plus, o, minus, times, K)"],
    ["monicValue(T, f, S, x, [])", "monicValue{T}(f, plus, times, unit, x, [])"],
  ];
  const body = (form: number) => predicates.map((p, i) => `theorem predicate${i}\n  requires evidence : ${p[form]}\n  shows ${p[form]}\nproof\n  exact evidence\n`).join("\n")
    + terms.map((p, i) => `theorem term${i}\n  shows ${p[form]} = ${p[form]}\nproof\n  rfl\n`).join("\n");
  const compact = load(syntaxPrefix + body(0) + syntaxSuffix);
  const expanded = load(syntaxPrefix + body(1) + syntaxSuffix);
  for (const name of [...predicates.map((_, i) => `Syntax.predicate${i}`), ...terms.map((_, i) => `Syntax.term${i}`)]) {
    assert.ok(formulaEquals(compact.theorems.get(name)!, expanded.theorems.get(name)!));
    const proof = compileProofModule([exportTheoremForMachine(compact, name)]);
    assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(expanded, name)]));
    verifyProofMachine(compact, proof);
  }
});

test("carrier-only shorthand does not guess operations for a full ring slot", () => {
  assert.throws(() => load(syntaxPrefix + "theorem wrong\n  shows IsRingHom(f, T, S) → IsRingHom(f, T, S)\nproof\n  intro h\n  exact h\n" + syntaxSuffix), /requires a scoped ring name/);
});
