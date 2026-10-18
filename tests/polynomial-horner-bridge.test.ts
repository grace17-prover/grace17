// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, exportTheoremForMachine, compileProofModule, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialHornerBridge.g17", "utf8");
function load(text: string) {
  const k = createZfKernel();
  loadModuleSourceGraph(k, [{ file: "PolynomialHornerBridge.g17", source: text }], ["lib"]);
  return k;
}

test("Horner sparse bridge, finite variable dependence, and examples have hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialHornerBridge.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.(HornerPolynomial|HornerLocalization|Variables)\./.test(n)
    || n.startsWith("Grace.Cumulus.Cardinal.FiniteUnion.") || n.startsWith("PolynomialHornerBridge."));
  assert.ok(names.length >= 23, `${names.length} theorem boundaries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const premise of ["infinite", "nonzero", "index", "injective", "carrier"]) {
  test(`point-free Horner localization cannot omit ${premise}`, () => {
    const prefix = "module PolynomialHornerBridge\nnamespace PolynomialHornerBridge\nimport Grace.Cumulus.Algebra.Polynomial.HornerLocalization\n";
    const body = source.slice(source.indexOf("section Localizations"));
    let incomplete = body.replace(new RegExp(`^\\s*(hypothesis|requires) ${premise} :.*\\n`, "m"), "\n");
    assert.notEqual(incomplete, body);
    incomplete = incomplete.replace("not_field_from_horner with *", "not_field_from_horner at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, g, j, leading, T, cs with *");
    assert.throws(() => load(prefix + incomplete), /cannot find evidence/);
  });
}

test("sparse evaluation agreement requires agreement on used variables", () => {
  const incomplete = source.replace(/^  requires agreement :.*\n/m, "");
  assert.notEqual(incomplete, source);
  assert.throws(() => load(incomplete), /cannot find evidence/);
});

test("scoped sparse-Horner and used-variable terms have exact expanded meanings", () => {
  const prefix = `module PolynomialHornerBridge
namespace PolynomialHornerBridge
import Grace.Cumulus.Algebra.Polynomial.HornerPolynomial
import Grace.Cumulus.Algebra.Polynomial.Variables
section Rings
variable (I A add z neg mul one j leading p : Set)
notation ring R := (A, add, z, neg, mul, one)
`;
  const forms = [
    ["polynomialFromHorner(I, R, j, leading, cs)", "polynomialFromHorner(I, A, add, z, neg, mul, one, j, leading, cs)"],
    ["polynomialVariablesUsed(I, R, p)", "polynomialVariablesUsed(I, A, z, p)"],
  ];
  for (const [short, full] of forms) {
    const body = (term: string) => `theorem syntax (cs : List(A))\n  shows ${term} = ${term}\nproof\n  rfl\nend Rings\nend PolynomialHornerBridge\n`;
    const a = load(prefix + body(short));
    const b = load(prefix + body(full));
    assert.ok(formulaEquals(a.theorems.get("PolynomialHornerBridge.syntax")!, b.theorems.get("PolynomialHornerBridge.syntax")!));
    const proof = compileProofModule([exportTheoremForMachine(a, "PolynomialHornerBridge.syntax")]);
    assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(b, "PolynomialHornerBridge.syntax")]));
    verifyProofMachine(a, proof);
  }
});

test("completed and cached bridge goals retain polynomial and restricted ring notation", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialHornerBridge.g17", source }], "ZF", ["PolynomialHornerBridge.g17"]);
    const theorem = result.theorems.find(t => t.name === "PolynomialHornerBridge.not_a_field");
    assert.ok(theorem);
    assert.match(theorem.statement, /IsField\(L\)/);
    assert.match(JSON.stringify(theorem.steps), /IsField\(L\)/);
  }
});

for (const missing of ["finite", "members"]) {
  test(`finite-family union cannot omit ${missing}`, () => {
    const proof = `module PolynomialHornerBridge
namespace PolynomialHornerBridge
import Grace.Cumulus.Cardinal.FiniteUnion
theorem invalid (A : Set)
  requires finite : Finite(A)
  requires members : ∀ S ∈ A, Finite(S)
  shows Finite(⋃A)
proof
  exact Finite.big_union with *
end PolynomialHornerBridge
`;
    assert.throws(() => load(proof.replace(new RegExp(`^  requires ${missing} :.*\\n`, "m"), "")), /cannot find evidence/);
  });
}
