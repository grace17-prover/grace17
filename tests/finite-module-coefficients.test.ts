// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/FiniteModuleCoefficients.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "FiniteModuleCoefficients.g17", source: text }], ["lib"]);
  return kernel;
}

test("finite span coefficients and annihilator certificates have complete ZF audits", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace.Cumulus.Algebra.(SpanInsert|SpanCoefficients|SpanAnnihilator)\./.test(name)
    || name.startsWith("FiniteModuleCoefficients."));
  assert.ok(names.length >= 25, `expected the span and annihilator proofs, got ${names.length}`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited in ZF`);
});

for (const premise of ["source", "target", "hom", "finiteModule", "representations", "bounded", "element", "annihilates", "unitIn"]) {
  test(`coefficient and annihilator applications retain ${premise}`, () => {
    const text = source.replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("coefficient lists cannot claim an extra entry", () => {
  const text = source.replaceAll("ListOps.length{A}(cs) = ListOps.length{B}(xs)", "ListOps.length{A}(cs) = succ(ListOps.length{B}(xs))");
  assert.throws(() => load(text), /conclusion does not match the goal/);
});

test("cold and cached span goals retain scoped coefficient notation and proof states", () => {
  for (let pass = 0; pass < 2; pass++) {
    const checked = checkWorkbenchFiles([{ name: "FiniteModuleCoefficients.g17", source }], "ZF", ["FiniteModuleCoefficients.g17"]);
    const theorem = checked.theorems.find(t => t.name === "FiniteModuleCoefficients.extract_coefficients")!;
    assert.ok(theorem);
    assert.ok(theorem.steps.length);
    assert.match(theorem.statement, /linearCombination\(R, S, f, xs, cs\)/);
    const repeated = checked.theorems.find(t => t.name === "FiniteModuleCoefficients.repeated_generator")!;
    assert.ok(repeated.steps.length > 3);
  }
});

test("scoped linear combinations preserve the exact formula and checked proof", () => {
  const prefix = `module Syntax
namespace Syntax
import Grace.Cumulus.Algebra.SpanCoefficients
section Rings
variable (A add zero neg mul one B plus z minus times unit f xs cs : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
`;
  const body = (term: string) => `theorem identity\n  shows ${term} = ${term}\nproof\n  rfl\nend Rings\nend Syntax\n`;
  const compact = load(prefix + body("linearCombination(R, S, f, xs, cs)"));
  const expanded = load(prefix + body("linearCombination(A, zero, B, plus, z, times, f, xs, cs)"));
  assert.ok(formulaEquals(compact.theorems.get("Syntax.identity")!, expanded.theorems.get("Syntax.identity")!));
  const proof = compileProofModule([exportTheoremForMachine(compact, "Syntax.identity")]);
  assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(expanded, "Syntax.identity")]));
  verifyProofMachine(compact, proof);
});
