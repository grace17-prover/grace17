// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, formulaEquals } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = `module Contracts
namespace Contracts
import Grace.Cumulus.Algebra.Polynomial.PointIdeal
section Rings
variable (A add zero neg mul one B plus z minus times unit f M : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
`;
const end = `end Rings\nend Contracts\n`;
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{file: "Contracts.g17", source}], ["lib"]);
  return kernel;
}
const forms = [
  ["IsCommRing(R)", "IsCommRing(A, add, zero, neg, mul, one)"],
  ["IsIntegralDomain(R)", "IsIntegralDomain(A, add, zero, neg, mul, one)"],
  ["Nontrivial(R)", "Nontrivial(A, zero, one)"],
  ["IsField(R)", "IsField(A, add, zero, neg, mul, one)"],
  ["IsIdeal(R, M)", "IsIdeal(A, add, zero, neg, mul, M)"],
  ["IsProperIdeal(R, M)", "IsProperIdeal(A, add, zero, neg, mul, one, M)"],
  ["IsMaximalIdeal(R, M)", "IsMaximalIdeal(A, add, zero, neg, mul, one, M)"],
  ["IsPrimeIdeal(R, M)", "IsPrimeIdeal(A, add, zero, neg, mul, one, M)"],
  ["IsSubring(R, M)", "IsSubring(A, add, zero, neg, mul, one, M)"],
  ["IsRingHom(f, R, S)", "IsRingHom(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)"],
  ["IsRingIso(f, R, S)", "IsRingIso(f, A, add, zero, neg, mul, one, B, plus, z, minus, times, unit)"],
];
function body(index: number, form: string) {
  return `theorem contract${index}\n  requires evidence : ${form}\n  shows ${form}\nproof\n  exact evidence\n`;
}

test("every scoped structure form elaborates to exactly the existing predicate", () => {
  const short = load(header + forms.map((p,i) => body(i,p[0]!)).join("\n") + end);
  const full = load(header + forms.map((p,i) => body(i,p[1]!)).join("\n") + end);
  for (let i=0; i<forms.length; i++)
    assert.ok(formulaEquals(short.theorems.get(`Contracts.contract${i}`)!, full.theorems.get(`Contracts.contract${i}`)!));
  assert.deepEqual([...short.axioms.keys()], [...full.axioms.keys()]);
});

test("structure shorthand rejects a carrier in place of an explicit scoped ring name", () => {
  assert.throws(() => load(header + body(0,"IsIdeal(A, M)") + end), /requires a scoped ring name/);
});

test("ordinary user predicates retain precedence over structural shorthand", () => {
  const source = header.replace("section Rings", "predicate IsIdeal (A M : Set) := A = M\nsection Rings");
  load(source + body(0,"IsIdeal(R, M)") + end);
  const wrongArity = header.replace("section Rings", "predicate IsIdeal (A add zero neg mul M : Set) := A = M\nsection Rings");
  assert.throws(() => load(wrongArity + body(0,"IsIdeal(R, M)") + end), /unknown predicate IsIdeal/);
});

test("completed and cached workbench goals show the same scoped structures", () => {
  const source = header + body(0,"IsRingHom(f, R, S)") + end;
  for(let i=0;i<2;i++) {
    const result = checkWorkbenchFiles([{name:"Contracts.g17",source}], "ZF", ["Contracts.g17"]);
    const theorem = result.theorems.find(t=>t.name === "Contracts.contract0")!;
    assert.ok(theorem);
    assert.match(theorem.statement, /RingHom\(f, R, S\)/);
    assert.match(JSON.stringify(theorem.steps), /RingHom\(f, R, S\)/);
  }
});

test("rewritten polynomial point examples use scoped maximal-ideal statements", () => {
  load(readFileSync("examples/PolynomialPoints.g17","utf8"));
});

test("goal rendering does not choose between indistinguishable structure aliases", async () => {
  const { pred, v } = await import("../src/ast.ts");
  const { formatFormula } = await import("../src/pretty.ts");
  const ring = {name:"R",carrier:v("A"),add:v("add"),zero:v("zero"),neg:v("neg"),mul:v("mul"),one:v("one"),call1:"apply",call2:"call2"};
  const formula=pred("Grace.Cumulus.Algebra.Ring.IdealCore.IsMaximalIdeal",ring.carrier,ring.add,ring.zero,ring.neg,ring.mul,ring.one,v("M"));
  const pieces = ["carrier", "add", "zero", "neg", "mul", "one"] as const;
  const notations = [{ token: "IsMaximalIdeal", fixity: "scoped" as const, kind: "predicate" as const,
    target: "Grace.Cumulus.Algebra.Ring.IdealCore.IsMaximalIdeal", parameters: ["R", "M"],
    expansion: [...pieces.map(piece => ({ parameter: "R", piece })), { parameter: "M" }] }];
  assert.equal(formatFormula(formula,{rings:[ring], notations}),"IsMaximalIdeal(R, M)");
  assert.equal(formatFormula(formula,{rings:[ring,{...ring,name:"S"}], notations}),"IsMaximalIdeal(A, add, R[0], neg, mul, R[1], M)");
  assert.equal(formatFormula(formula,{rings:[ring]}),"IsMaximalIdeal(A, add, 0, neg, mul, 1, M)");
});

const own = `module Contracts
namespace Contracts
import Grace.Cumulus.Algebra.Ring
predicate Closed (A add zero M : Set) := M ⊆ A ∧ zero ∈ M
notation scoped Closed(R, M) => Closed(R.carrier, R.add, R.zero, M)
def shift (A add x : Set) : Set := A
notation scoped shift(R, x) => shift(R.carrier, R.add, x)
section Rings
variable (A add zero neg mul one M : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;

test("a module declares scoped forms for its own predicates and functions", () => {
  const short = load(own + body(0, "Closed(R, M)") + "\n" + body(1, "shift(R, M) = A") + end);
  const full = load(own + body(0, "Closed(A, add, zero, M)") + "\n" + body(1, "shift(A, add, M) = A") + end);
  for (let i = 0; i < 2; i++)
    assert.ok(formulaEquals(short.theorems.get(`Contracts.contract${i}`)!, full.theorems.get(`Contracts.contract${i}`)!));
  const result = checkWorkbenchFiles([{name:"Contracts.g17", source: own + body(0, "Closed(R, M)") + "\n" + body(1, "shift(R, M) = A") + end}], "ZF", ["Contracts.g17"]);
  assert.match(result.theorems.find(t => t.name === "Contracts.contract0")!.statement, /Closed\(R, M\)/);
  assert.match(result.theorems.find(t => t.name === "Contracts.contract1")!.statement, /shift\(R, M\) = A/);
  assert.ok(result.notations.some(item => item.fixity === "scoped" && item.token === "Closed" && item.module === "Contracts"));
});

test("a scoped declaration names the written parameters and the target's pieces", () => {
  const declare = (text: string) => load(`module Contracts\nnamespace Contracts\nimport Grace.Cumulus.Algebra.Ring\npredicate Closed (A add zero M : Set) := M ⊆ A\n${text}\nend Contracts\n`);
  assert.throws(() => declare("notation scoped Closed(R, M) => Closed(R.carrier, R.add, R.zero, N)"), /must be a parameter of Closed/);
  assert.throws(() => declare("notation scoped Closed(R, M, N) => Closed(R.carrier, R.add, R.zero, M)"), /parameter N of Closed is not used/);
  assert.throws(() => declare("notation scoped Closed(R, M) => Closed(R.carrier, R.add, R.inv, M)"), /must be a parameter of Closed, or a ring piece/);
  assert.throws(() => declare("notation scoped Closed(R, M) => Closed(R.carrier, R.add, M)"), /unknown scoped notation target Closed, a predicate or function of 3 arguments/);
  assert.throws(() => declare("notation scoped Closed(A, M) => Closed(A, A, A, M)"), /names no ring scope piece/);
});

test("a scoped form is visible only through imports", () => {
  const user = `module Other\nnamespace Other\nimport Grace.Cumulus.Algebra.Ring\nsection Rings\nvariable (A add zero neg mul one M : Set)\nnotation ring R := (A, add, zero, neg, mul, one)\n` + body(0, "Closed(R, M)") + "end Rings\nend Other\n";
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{file: "Contracts.g17", source: own + end}, {file: "Other.g17", source: user}], ["lib"]), /unknown predicate Closed/);
});

test("constructed ring carriers recover a unique alias without inventing one", async () => {
  const { app, pred, v } = await import("../src/ast.ts");
  const { formatFormula, formatTerm } = await import("../src/pretty.ts");
  const carrier = app("polynomials", app("insert", v("j"), v("M")), v("A"), v("z"));
  const ring = {name:"Q", carrier, add:v("add"), zero:v("zero"), neg:v("neg"), mul:v("mul"), one:v("one"), call1:"apply", call2:"call2"};
  const formula = pred("in", v("p"), carrier);
  assert.equal(formatFormula(formula, {rings:[ring]}), "p ∈ Q");
  assert.equal(formatFormula(formula, {rings:[ring,{...ring,name:"T"}]}), "p ∈ polynomials(insert(j, M), A, z)");
  assert.equal(formatFormula(formula), "p ∈ polynomials(insert(j, M), A, z)");
  assert.equal(formatTerm(app("polynomials", v("I"), v("A"), v("z")), {rings:[ring]}), "polynomials(I, A, z)");
});
