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
import Grace.Cumulus.Algebra.Adjoin
import Grace.Cumulus.Algebra.Polynomial.PointIdeal
section Algebras
variable (A add zero neg mul one B plus z minus times unit f I G T v j a : Set)
notation ring R := (A, add, zero, neg, mul, one)
notation ring S := (B, plus, z, minus, times, unit)
`;
const end = `end Algebras\nend Contracts\n`;
function load(source: string) {
  const k=createZfKernel();
  loadModuleSourceGraph(k,[{file:"Contracts.g17",source}],["lib"]);
  return k;
}
const terms = [
 ["generatedSubring(R, G)","generatedSubring(A, add, zero, neg, mul, one, G)"],
 ["algebraAdjoin(f, R, S, G)","algebraAdjoin(f, A, B, plus, z, minus, times, unit, G)"],
 ["pointIdeal(I, R, v)","pointIdeal(I, A, add, zero, neg, mul, one, v)"],
 ["polynomialAt(I, R, v)","polynomialAt(I, A, add, zero, neg, mul, one, v)"],
 ["polynomialCoefficients(I, R)","polynomialCoefficients(I, A, zero)"],
 ["polynomialVariable(I, R, j)","polynomialVariable(I, A, zero, one, j)"],
 ["polynomialConstant(I, R, a)","polynomialConstant(I, A, zero, a)"],
 ["polynomialCoordinateDifference(I, R, j, a)","polynomialCoordinateDifference(I, A, add, zero, neg, mul, one, j, a)"],
 ["algebraAdjoin(f, R, S, generatedSubring(S, G))","algebraAdjoin(f, A, B, plus, z, minus, times, unit, generatedSubring(B, plus, z, minus, times, unit, G))"],
];
const predicates = [
 ["Subalgebra(f, R, S, T)","Subalgebra(f, A, B, plus, z, minus, times, unit, T)"],
 ["FinitelyGeneratedAlgebra(f, R, S)","FinitelyGeneratedAlgebra(f, A, B, plus, z, minus, times, unit)"],
];
function identity(i:number,term:string) { return `theorem t${i}\n  shows ${term} = ${term}\nproof\n  rfl\n`; }
function body(i:number,formula:string) { return `theorem p${i}\n  requires h : ${formula}\n  shows ${formula}\nproof\n  exact h\n`; }

test("scoped algebra terms and predicates elaborate identically to full applications",()=>{
 const kernels=[0,1].map(col=>load(header+terms.map((p,i)=>identity(i,p[col]!)).join("\n")+predicates.map((p,i)=>body(i,p[col]!)).join("\n")+end));
 for(const name of [...terms.map((_,i)=>`Contracts.t${i}`),...predicates.map((_,i)=>`Contracts.p${i}`)])
  assert.ok(formulaEquals(kernels[0]!.theorems.get(name)!,kernels[1]!.theorems.get(name)!),name);
});

test("term shorthand requires a scoped name and respects user function shadowing",()=>{
 assert.throws(()=>load(header+identity(0,"generatedSubring(A, G)")+end),/requires a scoped ring name/);
 load(header.replace("section Algebras","def generatedSubring (X Y : Set) : Set := X\nsection Algebras")+identity(0,"generatedSubring(R, G)")+end);
 assert.throws(()=>load(header.replace("section Algebras","def generatedSubring (A add zero neg mul one G : Set) : Set := G\nsection Algebras")+identity(0,"generatedSubring(R, G)")+end),/arity|unknown|argument/i);
});

test("nested term notation survives completed and cached workbench goal rendering",()=>{
 const source=header+identity(0,terms[8]![0]!)+end;
 for(let i=0;i<2;i++) {
  const result=checkWorkbenchFiles([{name:"Contracts.g17",source}],"ZF",["Contracts.g17"]);
  const theorem=result.theorems.find(t=>t.name==="Contracts.t0")!;
  assert.ok(theorem);
  assert.match(theorem.statement,/algebraAdjoin\(f, R, S, generatedSubring\(S, G\)\)/);
  assert.match(JSON.stringify(theorem.steps),/algebraAdjoin\(f, R, S, generatedSubring\(S, G\)\)/);
 }
});

test("adjunction library and examples have complete hereditary ZF audits",()=>{
 const k=createZfKernel();loadModuleGraph(k,["examples/AlgebraAdjoin.g17"],["lib"]);
 const names=[...k.theorems.keys()].filter(n=>/^(Grace.Cumulus.Algebra.Adjoin\.|AlgebraAdjoin\.)/.test(n));
 assert.ok(names.length>=20);
 for(const name of names) {
  const audit=auditTheoremAxioms(k,name);
  assert.equal(audit.complete,true,name);
  assert.deepEqual(audit.hereditary.filter(a=>/choice|sorry/i.test(a)),[],name);
 }
});

test("adjunction inclusion cannot discard the generator carrier requirement",()=>{
 const source=header+`hypothesis source : IsCommRing(R)
hypothesis target : IsCommRing(S)
hypothesis hom : IsRingHom(f, R, S)
theorem invalid
  shows G ⊆ algebraAdjoin(f, R, S, G)
proof
  exact algebraAdjoin.contains at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f, G with *
`+end;
 assert.throws(()=>load(source),/G ⊆ B|G ⊆ S/);
});

test("term display preserves ambiguity instead of selecting a structure alias",async()=>{
 const {app,v}=await import("../src/ast.ts");
 const {formatTerm}=await import("../src/pretty.ts");
 const ring={name:"R",carrier:v("A"),add:v("add"),zero:v("zero"),neg:v("neg"),mul:v("mul"),one:v("one"),call1:"apply",call2:"call2"};
 const term=app("Grace.Cumulus.Algebra.Ring.GeneratedSubring.generatedSubring",ring.carrier,ring.add,ring.zero,ring.neg,ring.mul,ring.one,v("G"));
 const pieces=["carrier","add","zero","neg","mul","one"] as const;
 const notations=[{token:"generatedSubring",fixity:"scoped" as const,kind:"function" as const,target:term.fn,parameters:["R","G"],
  expansion:[...pieces.map(piece=>({parameter:"R",piece})),{parameter:"G"}]}];
 assert.equal(formatTerm(term,{rings:[ring],notations}),"generatedSubring(R, G)");
 assert.equal(formatTerm(term,{rings:[ring,{...ring,name:"S"}],notations}),"generatedSubring(A, add, R[0], neg, mul, R[1], G)");
});

test("finite generation from a coefficient map retains surjectivity",()=>{
 assert.throws(()=>load(header+`hypothesis source : IsCommRing(R)
hypothesis target : IsCommRing(S)
hypothesis hom : IsRingHom(f, R, S)
theorem invalid
  shows FinitelyGeneratedAlgebra(f, R, S)
proof
  exact FinitelyGeneratedAlgebra.of_surjective at A, add, zero, neg, mul, one, B, plus, z, minus, times, unit, f with *
`+end),/SurjectiveBetween/);
});
