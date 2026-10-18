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
import Grace.Cumulus.Algebra.Field.Algebraic
section Rings
variable (A add zero neg mul one B plus z minus times unit f x G : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
`;
const end = "end Rings\nend Contracts\n";
function load(body: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Contracts.g17", source: header + body + end }], ["lib"]);
  return kernel;
}

test("integral and algebraic adjoining proofs have complete hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/IntegralAdjoin.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name => /^(Grace.Cumulus.Algebra.(LinearSpan|LinearSpanMultiplication|MonicRelations|IntegralAdjoin|Field.Algebraic)\.|IntegralAdjoin\.)/.test(name));
  assert.ok(names.length >= 44, `${names.length} boundaries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("module and algebraicity notation preserves the exact kernel formulas", () => {
  const predicates = [
    ["Submodule(f, R, S, G)", "Submodule(f, A, B, plus, z, minus, times, G)"],
    ["FiniteAlgebraModule(f, R, S)", "FiniteAlgebraModule(f, A, B, plus, z, minus, times)"],
    ["IntegralOver(f, R, S, x)", "IntegralOver(f, A, B, plus, z, times, unit, x)"],
    ["AlgebraicOver(f, R, S, x)", "AlgebraicOver(f, A, zero, B, plus, z, times, x)"],
  ];
  const terms = [
    ["linearSpan(f, R, S, G)", "linearSpan(f, A, B, plus, z, minus, times, G)"],
    ["monicValue(R, f, S, x, [])", "monicValue{A}(f, plus, times, unit, x, [])"],
    ["monicTailSet(R, f, S, x, [])", "monicTailSet{A}(f, plus, times, unit, x, [])"],
  ];
  const body = (column: number) => predicates.map((p, i) => `theorem p${i}\n  requires h : ${p[column]}\n  shows ${p[column]}\nproof\n  exact h\n`).join("\n") + terms.map((p, i) => `theorem t${i}\n  shows ${p[column]} = ${p[column]}\nproof\n  rfl\n`).join("\n");
  const a = load(body(0)), b = load(body(1));
  for (const name of [...predicates.map((_, i) => `p${i}`), ...terms.map((_, i) => `t${i}`)]) {
    assert.ok(formulaEquals(a.theorems.get(`Contracts.${name}`)!, b.theorems.get(`Contracts.${name}`)!), name);
  }
});

test("algebraic-to-integral normalization cannot omit the field premise", () => {
  assert.throws(() => load(`theorem missing_field
  requires source : IsCommRing(R)
  requires target : IsCommRing(S)
  requires hom : IsRingHom(f, R, S)
  requires algebraic : AlgebraicOver(f, R, S, x)
  shows IntegralOver(f, R, S, x)
proof
  exact AlgebraicOver.integral at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, x with *
`), /cannot find evidence for IsField/);
});

test("finite module conclusion cannot omit generation of the whole algebra", () => {
  assert.throws(() => load(`theorem missing_generation
  requires field : IsField(R)
  requires target : IsCommRing(S)
  requires hom : IsRingHom(f, R, S)
  requires algebraic : AlgebraicOver(f, R, S, x)
  shows FiniteAlgebraModule(f, R, S)
proof
  exact AlgebraicOver.finite_module_of_generates at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, x with *
`), /cannot find evidence for algebraAdjoin/);
});

test("completed and cached goals retain readable module notation", () => {
  const source = header + `theorem visible
  requires h : linearSpan(f, R, S, G) = S
  shows linearSpan(f, R, S, G) = S
proof
  exact h
` + end;
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "Contracts.g17", source }], "ZF", ["Contracts.g17"]);
    const theorem = result.theorems.find(t => t.name === "Contracts.visible");
    assert.ok(theorem);
    assert.match(theorem.statement, /linearSpan\(f, R, S, G\)/);
    assert.match(JSON.stringify(theorem.steps), /linearSpan\(f, R, S, G\)/);
  }
});
