// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms, formulaEquals } from "../src/index.ts";

const source = readFileSync("examples/DeterminantRows.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "DeterminantRows.g17", source: text }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

test("row linearity and elementary row operations are hereditarily admission-free ZF", t => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(name =>
    /Grace.Cumulus.Algebra.Ring.(FiniteLinearity|MatrixRows|DeterminantLinearity|DeterminantRows)\./.test(name) ||
    name.startsWith("DeterminantRows."));
  assert.ok(names.length >= 17, `${names.length} entries`);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

for (const [label, pattern] of [
  ["distinct source and destination rows", /^  requires distinct :.*\n/m],
  ["unchanged entries outside the row", /^  requires outside :.*\n/m],
  ["a scalar in the ring", /^  requires scalar :.*\n/m],
] as const) {
  test(`row addition requires ${label}`, () => {
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => load(changed), /cannot|does not match|unknown|missing/i);
  });
}

test("finite algebra scoped notation expands to the exact existing terms", () => {
  const header = `module FiniteNotation
namespace FiniteNotation
import Grace.Cumulus.Algebra.Ring.DeterminantLinearity
section Rings
variable (V A add zero neg mul one w v h a M : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
  const forms = [
    ["finiteRingSum(V, R, w)", "finiteRingSum(V, A, add, zero, neg, mul, one, w)"],
    ["finiteRingProduct(V, R, w)", "finiteRingProduct(V, A, add, zero, neg, mul, one, w)"],
    ["coefficientAdd(V, R, w, v)", "coefficientAdd(V, A, add, zero, neg, mul, one, w, v)"],
    ["coefficientScale(V, R, a, w)", "coefficientScale(V, A, add, zero, neg, mul, one, a, w)"],
    ["determinantTerms(V, R, M)", "determinantTerms(V, A, add, zero, neg, mul, one, M)"],
  ];
  const make = (column: number) => header + forms.map((pair, i) =>
    `theorem form${i}\n  shows ${pair[column]} = h → h = ${pair[column]}\nproof\n  intro equation\n  cc\n`
  ).join("\n") + "end Rings\nend FiniteNotation\n";
  const short = load(make(0));
  const full = load(make(1));
  for (let i = 0; i < forms.length; i++)
    assert.ok(formulaEquals(short.theorems.get(`FiniteNotation.form${i}`)!, full.theorems.get(`FiniteNotation.form${i}`)!));
  assert.deepEqual([...short.axioms.keys()], [...full.axioms.keys()]);
});

test("finite sum and product goals retain scoped notation without choosing ambiguous aliases", async () => {
  const { app, v } = await import("../src/ast.ts");
  const { formatTerm } = await import("../src/pretty.ts");
  const ring = { name: "R", carrier: v("A"), add: v("add"), zero: v("zero"), neg: v("neg"), mul: v("mul"), one: v("one"), call1: "apply", call2: "call2" };
  for (const [module, name] of [["FiniteSetSum", "finiteRingSum"], ["FiniteProduct", "finiteRingProduct"]]) {
    const term = app(`Grace.Cumulus.Algebra.Ring.${module}.${name}`, v("V"), ring.carrier, ring.add, ring.zero, ring.neg, ring.mul, ring.one, v("w"));
    const pieces = ["carrier", "add", "zero", "neg", "mul", "one"] as const;
    const notations = [{ token: name!, fixity: "scoped" as const, kind: "function" as const, target: term.fn, parameters: ["V", "R", "w"],
      expansion: [{ parameter: "V" }, ...pieces.map(piece => ({ parameter: "R", piece })), { parameter: "w" }] }];
    assert.equal(formatTerm(term, { rings: [ring], notations }), `${name}(V, R, w)`);
    const ambiguous = formatTerm(term, { rings: [ring, { ...ring, name: "S" }], notations });
    assert.doesNotMatch(ambiguous, /\(V, [RS], w\)/);
    assert.match(ambiguous, /\(V, A, add,/);
  }
});
