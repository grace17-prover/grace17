// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {createZfKernel,loadModuleGraph,loadModuleSourceGraph,auditTheoremAxioms} from "../src/index.ts";

const header=`module Boundary
namespace Boundary
import Grace.Cumulus.Algebra.Polynomial.FiniteGeneration
section Polynomials
variable (I A add zero neg mul one T : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring P := R[I]
hypothesis coefficients : IsCommRing(R)
`;
const end=`end Polynomials\nend Boundary\n`;
function load(source:string) {
 const kernel=createZfKernel();loadModuleSourceGraph(kernel,[{file:"Boundary.g17",source}],["lib"]);return kernel;
}

test("monomial induction, polynomial generation and examples check in ZF with complete audits",()=>{
 const kernel=createZfKernel();loadModuleGraph(kernel,["examples/PolynomialGeneration.g17"],["lib"]);
 const names=[...kernel.theorems.keys()].filter(n=>/^(Grace.Cumulus.Algebra.Polynomial.(MonomialGeneration|Generation|FiniteGeneration)\.|PolynomialGeneration\.)/.test(n));
 assert.ok(names.length>=26,`${names.length} boundaries`);
 for(const name of names) {
  const audit=auditTheoremAxioms(kernel,name);
  assert.equal(audit.complete,true,name);
  assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[],name);
 }
});

test("finite-generation corollary does not erase finite-variable hypothesis",()=>{
 assert.throws(()=>load(header+`theorem invalid
  shows FinitelyGeneratedAlgebra(polynomialCoefficients(I, R), R, P)
proof
  exact polynomials.finitely_generated at I, A, add, zero, neg, mul, one with *
`+end),/Finite\(I\)/);
});

test("a coefficient-containing subalgebra must also contain variables to equal the polynomial ring",()=>{
 assert.throws(()=>load(header+`hypothesis subalgebra : Subalgebra(polynomialCoefficients(I, R), R, P, T)
theorem invalid
  shows T = P
proof
  exact polynomialSubalgebra.eq_carrier at I, A, add, zero, neg, mul, one, T with *
`+end),/polynomialVariable/);
});

test("a subring containing variables does not automatically contain all coefficients",()=>{
 assert.throws(()=>load(header+`hypothesis subring : IsSubring(P, T)
hypothesis variables : ∀ j ∈ I, polynomialVariable(I, R, j) ∈ T
theorem invalid
  shows T = P
proof
  exact polynomialSubalgebra.eq_carrier at I, A, add, zero, neg, mul, one, T with *
`+end),/Subalgebra/);
});

const maps=`module Maps
namespace Maps
import Grace.Cumulus.Algebra.Image
section Algebras
variable (A add zero neg mul one B plus z minus times unit C sum o inverse product e f g : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
notation ring U := (C, sum, o, inverse, product, e)
hypothesis coefficients : IsCommRing(R)
hypothesis source : IsCommRing(S)
hypothesis target : IsCommRing(U)
hypothesis coefficientMap : IsRingHom(f, R, S)
hypothesis hom : IsRingHom(g, S, U)
hypothesis finiteGeneration : FinitelyGeneratedAlgebra(f, R, S)
`;

test("surjective algebra images have complete ZF audits and require surjectivity",()=>{
 const theorem=`theorem image
  shows FinitelyGeneratedAlgebra(compose(g, f, A, B, C), R, U)
proof
  exact FinitelyGeneratedAlgebra.surjective_image with coefficients, source, target, coefficientMap, hom, finiteGeneration, onto
end Algebras
end Maps
`;
 const kernel=load(maps+"hypothesis onto : SurjectiveBetween(g, B, C)\n"+theorem);
 const names=[...kernel.theorems.keys()].filter(n=>n.startsWith("Grace.Cumulus.Algebra.Image.")||n==="Maps.image");
 assert.ok(names.length>=7, `expected the image proofs, got ${names.length}`);
 for(const name of names) {
  const audit=auditTheoremAxioms(kernel,name);
  assert.equal(audit.complete,true,name);
  assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[],name);
 }
 assert.throws(()=>load(maps+theorem.replace("with coefficients, source, target, coefficientMap, hom, finiteGeneration, onto","at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, C, sum, o, inverse, product, e, f, g with *")),/SurjectiveBetween/);
});
