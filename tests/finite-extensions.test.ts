// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = `module Contracts
namespace Contracts
import Grace.Cumulus.Algebra.IntegralFinite
import Grace.Cumulus.Algebra.FiniteModuleTower
section Algebras
variable (A add zero neg mul one B plus z minus times unit C sum o inverse product e f g G H K : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
notation ring U := (C, sum, o, inverse, product, e)
`;
const end = "end Algebras\nend Contracts\n";
function load(body: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Contracts.g17", source: header + body + end }], ["lib"]);
  return kernel;
}

test("finite integral generation and finite module towers have hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/FiniteExtensions.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name => /^(Grace.Cumulus.Algebra.(SpanProduct|FiniteSpan|IntegralFinite|LinearSpanMap|FiniteModuleTower)\.|FiniteExtensions\.)/.test(name));
  names.push("Grace.Cumulus.Algebra.MonicRelations.IntegralOver.of_square");
  assert.ok(names.length >= 26, `${names.length} boundaries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("finite span and spanning product shorthands preserve exact formulas", () => {
  const bodies = [
    `theorem p\n  requires h : FiniteSpan(f, R, S, G)\n  shows FiniteSpan(f, R, S, G)\nproof\n  exact h\ntheorem t\n  shows spanProducts(S, G, H) = spanProducts(S, G, H)\nproof\n  rfl\n`,
    `theorem p\n  requires h : FiniteSpan(f, A, B, plus, z, minus, times, G)\n  shows FiniteSpan(f, A, B, plus, z, minus, times, G)\nproof\n  exact h\ntheorem t\n  shows spanProducts(B, times, G, H) = spanProducts(B, times, G, H)\nproof\n  rfl\n`,
  ];
  const a = load(bodies[0]!), b = load(bodies[1]!);
  for (const name of ["Contracts.p", "Contracts.t"])
    assert.ok(formulaEquals(a.theorems.get(name)!, b.theorems.get(name)!), name);
});

const algebra = `hypothesis source : IsCommRing(R)
hypothesis target : IsCommRing(S)
hypothesis hom : IsRingHom(f, R, S)
`;

test("integral generation cannot discard finiteness of the generator set", () => {
  assert.throws(() => load(algebra + `theorem invalid
  requires bounded : K ⊆ S
  requires integral : ∀ x ∈ K, IntegralOver(f, R, S, x)
  shows FiniteSpan(f, R, S, algebraAdjoin(f, R, S, K))
proof
  exact integralGenerators.finite_adjoin at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, K with *
`), /cannot find evidence for Finite\(K\)/);
});

test("finite generation alone does not imply a finite module", () => {
  assert.throws(() => load(algebra + `theorem invalid
  requires generated : FinitelyGeneratedAlgebra(f, R, S)
  shows FiniteAlgebraModule(f, R, S)
proof
  exact FinitelyGeneratedAlgebra.finite_module_of_integral at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f with *
`), /cannot find evidence for .*IntegralOver/);
});

test("tower finiteness requires finiteness of the intermediate algebra", () => {
  assert.throws(() => load(`theorem invalid
  requires coefficients : IsCommRing(R)
  requires source : IsCommRing(S)
  requires target : IsCommRing(U)
  requires coefficientMap : IsRingHom(f, R, S)
  requires hom : IsRingHom(g, S, U)
  requires finiteU : FiniteAlgebraModule(g, S, U)
  shows FiniteAlgebraModule(compose(g, f, R, S, U), R, U)
proof
  exact FiniteAlgebraModule.tower at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, C, sum, o, inverse, product, e, f, g with *
`), /cannot find evidence for FiniteAlgebraModule\(f,/);
});

test("completed and cached goal states retain finite span and product notation", () => {
  const source = header + `theorem visible
  requires h : FiniteSpan(f, R, S, spanProducts(S, G, H))
  shows FiniteSpan(f, R, S, spanProducts(S, G, H))
proof
  exact h
` + end;
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "Contracts.g17", source }], "ZF", ["Contracts.g17"]);
    const theorem = result.theorems.find(t => t.name === "Contracts.visible");
    assert.ok(theorem);
    assert.match(theorem.statement, /FiniteSpan\(f, R, S, spanProducts\(S, G, H\)\)/);
    assert.match(JSON.stringify(theorem.steps), /FiniteSpan\(f, R, S, spanProducts\(S, G, H\)\)/);
  }
});
