// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialBaseChange.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PolynomialBaseChange.g17", source: text }], ["lib"]);
  return kernel;
}

test("base change, the universal evaluation map, and canonical independence have complete ZF audits", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.(CoefficientMap|MapHom|EvaluationOver)\./.test(n)
    || n.startsWith("PolynomialBaseChange."));
  assert.ok(names.length >= 39);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const premise of ["source", "target", "hom", "injective", "assignment", "index", "independent", "polynomial"]) {
  test(`base-change applications require ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "")
      .replace("polynomialMap.hom with", "polynomialMap.hom at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f with")
      .replace("polynomialMap.injective with", "polynomialMap.injective at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f with")
      .replace("polynomialAtOver.hom with", "polynomialAtOver.hom at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f, v with")
      .replace("polynomialAtOver.variable with", "polynomialAtOver.variable at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f, v, j with")
      .replace("AlgebraicallyIndependent.relation_iff with", "AlgebraicallyIndependent.relation_iff at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f, v, p with");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("scoped map, evaluation, independence and variable-family notation expand exactly", () => {
  const prefix = source.slice(0, source.indexOf("theorem map_is_hom"));
  const body = (expanded: boolean) => {
    const map = expanded ? "polynomialMap(I, A, z, B, o, f)" : "polynomialMap(I, R, S, f)";
    const evaluation = expanded ? "polynomialAtOver(I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f, v)" : "polynomialAtOver(I, R, S, f, v)";
    const variables = expanded ? "polynomialVariables(I, A, z, one)" : "polynomialVariables(I, R)";
    const independent = expanded ? "AlgebraicallyIndependent(I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, f, v)" : "AlgebraicallyIndependent(I, R, S, f, v)";
    return [map, evaluation, variables].map((term, i) => `theorem syntax${i}\n  shows ${term} = ${term}\nproof\n  rfl\n`).join("\n")
      + `theorem syntax3\n  shows ${independent} → ${independent}\nproof\n  intro assumption\n  exact assumption\nend Rings\nend PolynomialBaseChange\n`;
  };
  const compact = load(prefix + body(false));
  const expanded = load(prefix + body(true));
  for (let i = 0; i < 4; i++) {
    const name = `PolynomialBaseChange.syntax${i}`;
    assert.ok(formulaEquals(compact.theorems.get(name)!, expanded.theorems.get(name)!));
    const proof = compileProofModule([exportTheoremForMachine(compact, name)]);
    assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(expanded, name)]));
    verifyProofMachine(compact, proof);
  }
});

test("completed and cached base-change goals retain scoped rings", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialBaseChange.g17", source }], "ZF", ["PolynomialBaseChange.g17"]);
    const theorem = result.theorems.find(t => t.name === "PolynomialBaseChange.evaluation_is_hom")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length);
    assert.match(theorem.statement, /polynomialAtOver\(I, R, S, f, v\)/);
  }
});
