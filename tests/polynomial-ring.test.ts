// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("polynomial ring construction, induction, and worked ring proofs have complete ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["examples/PolynomialRing.g17"], ["lib"]);
  const prefixes = [
    "Grace.Cumulus.Algebra.CoefficientInduction.",
    "Grace.Cumulus.Algebra.Polynomial.Unit.",
    "Grace.Cumulus.Algebra.Polynomial.Terms.",
    "Grace.Cumulus.Algebra.Polynomial.Associativity.",
    "Grace.Cumulus.Algebra.Polynomial.Ring.",
    "PolynomialRing.",
  ];
  const names = [...kernel.theorems.keys()].filter(n => prefixes.some(p => n.startsWith(p)));
  names.push("Grace.Cumulus.Algebra.Ring.PushforwardTransport.finitePushforward.reconstruct",
    "Grace.Cumulus.Algebra.Ring.PushforwardTransport.finitePushforward.singleton",
    "Grace.Cumulus.Algebra.Polynomial.IdealSupport.monomialIdealPolynomials.ideal");
  assert.ok(names.length >= 60, `expected all new theorem boundaries, got ${names.length}`);
  for (const name of names) {
    assert.ok(kernel.theorems.has(name), name);
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

function rejects(source: string, pattern: RegExp) {
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "Invalid.g17", source: `module Invalid
import Grace.Cumulus.Algebra.Polynomial.IdealSupport
${source}` }], ["lib"]), pattern);
}

test("polynomial ring construction retains the coefficient ring laws", () => {
  rejects(`theorem invalid (I A add zero neg mul one : Set)
  shows IsCommRing(polynomials(I, A, zero), polynomialAdd(I, A, add, zero, neg, mul, one), constantFunction(monomials(I), A, zero), polynomialNeg(I, A, add, zero, neg, mul, one), polynomialMul(I, A, add, zero, neg, mul, one), polynomialConstant(I, A, zero, one))
proof
  exact polynomials.comm_ring at I, A, add, zero, neg, mul, one with *
`, /CommRing\(A/);
});

test("polynomial associativity requires finite-support membership of every input", () => {
  rejects(`theorem invalid (I A add zero neg mul one p q r : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires memberP : p ∈ polynomials(I, A, zero)
  requires memberQ : q ∈ polynomials(I, A, zero)
  shows polynomialProduct(I, A, add, zero, neg, mul, one, polynomialProduct(I, A, add, zero, neg, mul, one, p, q), r) = polynomialProduct(I, A, add, zero, neg, mul, one, p, polynomialProduct(I, A, add, zero, neg, mul, one, q, r))
proof
  exact polynomialProduct.associative at I, A, add, zero, neg, mul, one, p, q, r with *
`, /r ∈ polynomials/);
});

test("polynomial induction cannot omit closure under sums", () => {
  rejects(`theorem invalid (I A add zero neg mul one S p : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  requires member : p ∈ polynomials(I, A, zero)
  requires base : constantFunction(monomials(I), A, zero) ∈ S
  requires terms : ∀ a ∈ A, ∀ m ∈ monomials(I), polynomialTerm(I, A, zero, a, m) ∈ S
  shows p ∈ S
proof
  exact polynomials.induction at I, A, add, zero, neg, mul, one, S, p with *
`, /coefficientAdd/);
});

test("locally proved ring evidence is usable and stays local to its theorem", () => {
  const header = `module LocalRing
namespace LocalRing
import Grace.Cumulus.Algebra.OrderedAdditive
predicate RingPresentation (A add zero neg mul one : Set) := IsCommRing(A, add, zero, neg, mul, one)
theorem unpack (A add zero neg mul one : Set)
  requires presentation : RingPresentation(A, add, zero, neg, mul, one)
  shows IsCommRing(A, add, zero, neg, mul, one)
proof
  unfold RingPresentation at presentation
  exact presentation
`;
  const statement = (name: string, evidence: boolean) => `theorem ${name} (A add zero neg mul one x : Set)
  requires presentation : RingPresentation(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  shows call2(add, x, zero) = x
proof
${evidence ? "  have localRing := unpack with presentation\n" : ""}  ring
`;
  loadModuleSourceGraph(createZfKernel(), [{ file: "LocalRing.g17",
    source: header + statement("works", true) + "end LocalRing\n" }], ["lib"]);
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [{ file: "LocalRing.g17",
    source: header + statement("works", true) + statement("cannot_leak", false) + "end LocalRing\n" }], ["lib"]),
    /ring|settle|normal forms|linear arithmetic requires Less/);
});

test("ring with the polynomial instance rejects a false identity", () => {
  const source = readFileSync("examples/PolynomialRing.g17", "utf8").replace(
    "p * p + p * q + p * q + q * q", "p * p + q * q");
  assert.throws(() => loadModuleSourceGraph(createZfKernel(), [
    { file: "PolynomialRing.g17", source },
  ], ["lib"]), /different normal forms/);
});

test("polynomial ring instances compose for iterated polynomial carriers", () => {
  const base = ["A", "add", "zero", "neg", "mul", "one"];
  const lift = (index: string, [carrier, add, zero, neg, mul, one]: string[]) => {
    const args = [index, carrier, add, zero, neg, mul, one].join(", ");
    return [`polynomials(${index}, ${carrier}, ${zero})`, `polynomialAdd(${args})`,
      `constantFunction(monomials(${index}), ${carrier}, ${zero})`, `polynomialNeg(${args})`,
      `polynomialMul(${args})`, `polynomialConstant(${index}, ${carrier}, ${zero}, ${one})`];
  };
  const nested = lift("J", lift("I", base));
  const structure = nested.join(", ");
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Iterated.g17", source: `module Iterated
namespace Iterated
import Grace.Cumulus.Algebra.Polynomial.Ring
theorem ring (I J A add zero neg mul one : Set)
  requires coefficients : IsCommRing(A, add, zero, neg, mul, one)
  shows IsCommRing(${structure})
proof
  synthesize
section Arithmetic
variable (I J A add zero neg mul one : Set)
hypothesis coefficients : IsCommRing(A, add, zero, neg, mul, one)
notation ring P := (${structure})
theorem expand (p q : Set)
  requires hp : p ∈ ${nested[0]}
  requires hq : q ∈ ${nested[0]}
  shows (p + q) * (p - q) = p * p - q * q
proof
  ring
end Arithmetic
end Iterated
` }], ["lib"]);
  const audit = auditTheoremAxioms(kernel, "Iterated.ring");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), []);
});
