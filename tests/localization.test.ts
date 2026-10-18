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
import Grace.Cumulus.Algebra.Field.PrincipalLocalization
section Algebras
variable (A add zero neg mul one B plus z minus times unit f T D K s y : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
`;
const end = "end Algebras\nend Contracts\n";
function load(body: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Contracts.g17", source: header + body + end }], ["lib"]);
  return kernel;
}

test("localization, common denominators and principal localization have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/Localization.g17"], ["lib"]);
  const names = [...kernel.theorems.keys()].filter(name => /^(Grace.Cumulus.Algebra.(Localization|ClearDenominators|Field.Localization|Field.PrincipalLocalization)\.|Localization\.)/.test(name));
  names.push("Grace.Cumulus.Algebra.Field.Construction.IsField.no_zero_divisors", "Grace.Cumulus.Algebra.Field.Construction.IsField.integral_domain");
  assert.ok(names.length >= 31, `${names.length} boundaries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("localization and power notation preserves exact kernel formulas", () => {
  const predicates = [["Denominators(S, T, D)", "Denominators(B, times, z, unit, T, D)"]];
  const terms = [
    ["localizationWithin(S, T, D)", "localizationWithin(B, times, T, D)"],
    ["denominatorInverses(S, D)", "denominatorInverses(B, times, unit, D)"],
    ["denominatorPowers(S, s)", "denominatorPowers(B, times, unit, s)"],
    ["monoidPow(S, s, n)", "monoidPow(times, unit, s, n)"],
  ];
  const body = (column: number) => predicates.map((p, i) => `theorem p${i}\n  requires h : ${p[column]}\n  shows ${p[column]}\nproof\n  exact h\n`).join("\n") + terms.map((p, i) => `theorem t${i} (n : Nat)\n  shows ${p[column]} = ${p[column]}\nproof\n  rfl\n`).join("\n");
  const a = load(body(0)), b = load(body(1));
  for (const name of ["p0", ...terms.map((_, i) => `t${i}`)])
    assert.ok(formulaEquals(a.theorems.get(`Contracts.${name}`)!, b.theorems.get(`Contracts.${name}`)!), name);
});

test("powers of a denominator require that its base be nonzero", () => {
  assert.throws(() => load(`theorem invalid
  requires field : IsField(S)
  requires subring : IsSubring(S, T)
  requires element : s ∈ T
  shows Denominators(S, T, denominatorPowers(S, s))
proof
  exact denominatorPowers.denominators at B, plus, z, minus, times, unit, T, s with *
`), /cannot find evidence for.*s.*z/);
});

test("common denominator clearing cannot discard finiteness", () => {
  assert.throws(() => load(`theorem invalid
  requires ring : IsCommRing(S)
  requires subring : IsSubring(S, T)
  requires denominators : Denominators(S, T, D)
  requires included : K ⊆ localizationWithin(S, T, D)
  shows ∃ d ∈ D, ∀ x ∈ K, S[d * x] ∈ T
proof
  exact localizationWithin.clear_finite at B, plus, z, minus, times, unit, T, D, K with *
`), /cannot find evidence for Finite\(K\)/);
});

test("the fraction-field obstruction retains its fraction-generation premise", () => {
  assert.throws(() => load(`theorem invalid
  requires source : IsCommRing(R)
  requires field : IsField(S)
  requires hom : IsRingHom(f, R, S)
  requires subalgebra : Subalgebra(f, R, S, T)
  requires denominators : Denominators(S, T, D)
  requires finite : FiniteAlgebraModule(f, R, S)
  shows T = S
proof
  exact localizationWithin.eq_field_of_finite_module at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, T, D with *
`), /cannot find evidence for localizationWithin/);
});

test("inverse adjunction cannot use an arbitrary element as the inverse", () => {
  assert.throws(() => load(`theorem invalid
  requires field : IsField(S)
  requires subring : IsSubring(S, T)
  requires element : s ∈ T
  requires nonzero : s ≠ S[0]
  shows localizationWithin(S, T, denominatorPowers(S, s)) = generatedSubring(S, insert(y, T))
proof
  exact localizationWithin.adjoin_single_inverse at B, plus, z, minus, times, unit, T, s, y with *
`), /cannot find evidence for IsInverse/);
});

test("cached and completed goals retain principal localization notation", () => {
  const source = header + `theorem visible
  requires h : K ⊆ localizationWithin(S, T, denominatorPowers(S, s))
  shows K ⊆ localizationWithin(S, T, denominatorPowers(S, s))
proof
  exact h
` + end;
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "Contracts.g17", source }], "ZF", ["Contracts.g17"]);
    const theorem = result.theorems.find(t => t.name === "Contracts.visible");
    assert.ok(theorem);
    assert.match(theorem.statement, /localizationWithin\(S, T, denominatorPowers\(S, s\)\)/);
    assert.match(JSON.stringify(theorem.steps), /localizationWithin\(S, T, denominatorPowers\(S, s\)\)/);
  }
});
