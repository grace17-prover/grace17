// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {createZfKernel,createSetTheoryKernel,loadModuleGraph,loadModuleSourceGraph,auditTheoremAxioms,formulaEquals} from "../src/index.ts";
import {checkWorkbenchFiles} from "../src/workbench.ts";

function load(source:string,choice=false) {
 const k=choice?createSetTheoryKernel({profile:"ZFC"}):createZfKernel();
 loadModuleSourceGraph(k,[{file:"Contracts.g17",source}],["lib"]);return k;
}
const header=`module Contracts
namespace Contracts
import Grace.Cumulus.Algebra.Polynomial.ResidueCriterion
section Rings
variable (I A add zero neg mul one J f g : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring P := R[I]
notation ring Q := P ⧸ J
`;
const end="end Rings\nend Contracts\n";

test("field embeddings, polynomial uniqueness, residue reconstruction and criterion are checked in ZF",()=>{
 const k=createZfKernel();loadModuleGraph(k,["examples/PolynomialUniversal.g17"],["lib"]);
 const names=[...k.theorems.keys()].filter(n=>/^(Grace.Cumulus.Algebra.(Ring.Equalizer|Field.Embedding|Polynomial.(Universal|Residue|ResidueCriterion))\.|PolynomialUniversal\.)/.test(n));
 assert.ok(names.length>=23,`${names.length} boundaries`);
 for(const name of names){const audit=auditTheoremAxioms(k,name);assert.equal(audit.complete,true,name);assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[],name);}
});

test("conditional Nullstellensatz reduction records Choice only for maximal ideal existence",()=>{
 const k=createSetTheoryKernel({profile:"ZFC"});loadModuleGraph(k,["examples/NullstellensatzReduction.g17"],["lib"]);
 const prefix="Grace.Cumulus.Algebra.Polynomial.NullstellensatzReduction.";
 for(const name of ["polynomialIdeal.common_zero_of_residue_surjectivity","polynomialIdeal.unit_iff_no_common_zero_of_residue_surjectivity","polynomialIdeal.unit_iff_no_common_zero_of_field_algebra_rigidity"]){
  const audit=auditTheoremAxioms(k,prefix+name);assert.equal(audit.complete,true);assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),["set.choice"]);
 }
 for(const name of ["IsMaximalIdeal.common_zero_of_residue_surjectivity","IsMaximalIdeal.point_of_residue_surjectivity","polynomialResidueCoefficients.surjective_of_field_algebra_rigidity"]){
  const audit=auditTheoremAxioms(k,prefix+name);assert.equal(audit.complete,true);assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[]);
 }
});

test("polynomial uniqueness cannot omit agreement on coefficients or on variables",()=>{
 const assumptions=`hypothesis ring : IsCommRing(R)
hypothesis first : IsRingHom(f, P, R)
hypothesis second : IsRingHom(g, P, R)
`;
 const constants="hypothesis constants : ∀ a ∈ R, f(polynomialConstant(I, R, a)) = g(polynomialConstant(I, R, a))\n";
 const variables="hypothesis variables : ∀ j ∈ I, f(polynomialVariable(I, R, j)) = g(polynomialVariable(I, R, j))\n";
 const proof=`theorem invalid
  shows f = g
proof
  exact IsRingHom.polynomial_ext at I, A, add, zero, neg, mul, one, A, add, zero, neg, mul, one, f, g with *
`;
 assert.throws(()=>load(header+assumptions+constants+proof+end),/polynomialVariable/);
 assert.throws(()=>load(header+assumptions+variables+proof+end),/polynomialConstant/);
});

test("common-zero reconstruction cannot omit surjectivity of the residue coefficient map",()=>{
 assert.throws(()=>load(header+`hypothesis field : IsField(R)
hypothesis maximal : IsMaximalIdeal(P, J)
theorem invalid
  shows ∃ v, PolynomialCommonZero(I, A, add, zero, neg, mul, one, J, v)
proof
  exact polynomialResidueCoefficients.common_zero_of_surjective at I, A, add, zero, neg, mul, one, J with *
`+end),/SurjectiveBetween/);
});

test("the conditional Nullstellensatz equivalence cannot drop its remaining residue hypothesis",()=>{
 const source=header.replace("import Grace.Cumulus.Algebra.Polynomial.ResidueCriterion","import Grace.Cumulus.Algebra.Polynomial.NullstellensatzReduction");
 assert.throws(()=>load(source+`hypothesis field : IsField(R)
hypothesis generators : J ⊆ P
theorem invalid
  shows P[1] ∈ idealSpan(P, J) ↔ ¬(∃ v, PolynomialCommonZero(I, A, add, zero, neg, mul, one, J, v))
proof
  exact polynomialIdeal.unit_iff_no_common_zero_of_residue_surjectivity at I, A, add, zero, neg, mul, one, J with *
`+end,true),/SurjectiveBetween/);
});

test("new scoped residue and ideal terms elaborate to exactly their full applications",()=>{
 const pairs=[
  ["polynomialValues(I, R, f)","polynomialValues(I, A, add, zero, neg, mul, one, f)"],
  ["polynomialResidueCoefficients(I, R, J)","polynomialResidueCoefficients(I, A, add, zero, neg, mul, one, J)"],
  ["polynomialResidueRetraction(I, R, J)","polynomialResidueRetraction(I, A, add, zero, neg, mul, one, J)"],
  ["idealSpan(R, J)","idealSpan(A, add, zero, neg, mul, J)"],
 ];
 const body=(col:number)=>header+pairs.map((pair,i)=>`theorem t${i}\n  shows ${pair[col]} = ${pair[col]}\nproof\n  rfl\n`).join("\n")+end;
 const a=load(body(0)),b=load(body(1));for(let i=0;i<pairs.length;i++)assert.ok(formulaEquals(a.theorems.get(`Contracts.t${i}`)!,b.theorems.get(`Contracts.t${i}`)!));
});

test("completed and cached goal histories retain the explicit missing residue hypothesis",()=>{
 const source=header.replace("import Grace.Cumulus.Algebra.Polynomial.ResidueCriterion","import Grace.Cumulus.Algebra.Polynomial.NullstellensatzReduction")+`hypothesis field : IsField(R)
hypothesis generators : J ⊆ P
hypothesis residues : ∀ K, IsMaximalIdeal(P, K) → SurjectiveBetween(polynomialResidueCoefficients(I, R, K), R, (P ⧸ idealRelation(P, K)))
theorem conditional
  shows P[1] ∈ idealSpan(P, J) ↔ ¬(∃ v, PolynomialCommonZero(I, A, add, zero, neg, mul, one, J, v))
proof
  exact polynomialIdeal.unit_iff_no_common_zero_of_residue_surjectivity with field, residues, generators
`+end;
 for(let i=0;i<2;i++){
  const r=checkWorkbenchFiles([{name:"Contracts.g17",source}],"ZFC",["Contracts.g17"]);
  const theorem=r.theorems.find(t=>t.name==="Contracts.conditional")!;assert.ok(theorem);
  assert.match(theorem.statement,/SurjectiveBetween/);
  assert.match(theorem.statement,/polynomialResidueCoefficients\(I, R, K\)/);
  assert.match(JSON.stringify(theorem.steps),/idealSpan\(P, J\)/);
 }
});

test("field embeddings require a nontrivial target and a field source",()=>{
 const base=`module EmbeddingBoundary
import Grace.Cumulus.Algebra.Field.Embedding
section Maps
variable (A add zero neg mul one B plus z minus times unit f : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
hypothesis target : IsCommRing(S)
hypothesis hom : IsRingHom(f, R, S)
`;
 const proof=`theorem invalid
  shows InjectiveBetween(f, R, S)
proof
  exact IsRingHom.field_injective at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f with *
end Maps
`;
 assert.throws(()=>load(base+"hypothesis field : IsField(R)\n"+proof),/Nontrivial/);
 assert.throws(()=>load(base+"hypothesis source : IsCommRing(R)\nhypothesis nontrivial : Nontrivial(S)\n"+proof),/IsField/);
});
