// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {createZfKernel,loadModuleSourceGraph,formulaEquals} from "../src/index.ts";
import {checkWorkbenchFiles} from "../src/workbench.ts";
const header=`module QuotientSyntax
namespace QuotientSyntax
import Grace.Cumulus.Algebra.Polynomial.FiniteGeneration
section Rings
variable (A add zero neg mul one J I : Set)
notation ring R := (A, add, zero, neg, mul, one)
`;
const expanded="(A ⧸ idealRelation(A, add, neg, J), quotientBinary(A, idealRelation(A, add, neg, J), add), ⟦zero⟧[A, idealRelation(A, add, neg, J)], quotientUnary(A, idealRelation(A, add, neg, J), neg), quotientBinary(A, idealRelation(A, add, neg, J), mul), ⟦one⟧[A, idealRelation(A, add, neg, J)])";
const theorem=`theorem identity
  requires field : IsField(Q)
  shows IsField(Q)
proof
  exact field
end Rings
end QuotientSyntax
`;
function load(source:string) {const k=createZfKernel();loadModuleSourceGraph(k,[{file:"QuotientSyntax.g17",source}],["lib"]);return k;}

test("quotient ring scope expands to exactly the explicit quotient operations",()=>{
 const short=load(header+"notation ring Q := R ⧸ J\n"+theorem);
 const full=load(header+`notation ring Q := ${expanded}\n`+theorem);
 assert.ok(formulaEquals(short.theorems.get("QuotientSyntax.identity")!,full.theorems.get("QuotientSyntax.identity")!));
});

test("quotient notation supplies neither ideal hypotheses nor ring laws",()=>{
 assert.throws(()=>load(header+`notation ring Q := R ⧸ J
theorem invalid
  shows Q[1 + 0] = Q[1]
proof
  ring
end Rings
end QuotientSyntax
`),/ring|instance|CommRing|did not close/);
 assert.throws(()=>load(header+`notation ring Q := R ⧸ J
hypothesis coefficients : IsCommRing(R)
theorem invalid
  shows IsCommRing(Q)
proof
  exact idealQuotient.comm_ring at A, add, zero, neg, mul, one, J with *
end Rings
end QuotientSyntax
`),/Ideal/);
 assert.throws(()=>load(header+"notation ring Q := Missing ⧸ J\n"+theorem),/unknown quotient base ring notation Missing/);
});

test("polynomial generators and ideal relations retain exact term elaboration",()=>{
 const pairs=[
  ["polynomialGenerators(I, R)","polynomialGenerators(I, A, zero, one)"],
  ["idealRelation(R, J)","idealRelation(A, add, neg, J)"],
 ];
 const source=(col:number)=>header+pairs.map((pair,i)=>`theorem t${i}\n  shows ${pair[col]} = ${pair[col]}\nproof\n  rfl\n`).join("\n")+"end Rings\nend QuotientSyntax\n";
 const a=load(source(0)),b=load(source(1));
 for(let i=0;i<pairs.length;i++)assert.ok(formulaEquals(a.theorems.get(`QuotientSyntax.t${i}`)!,b.theorems.get(`QuotientSyntax.t${i}`)!));
});

test("nested polynomial quotient scopes survive completed and cached goals",()=>{
 const source=header+"notation ring P := R[I]\nnotation ring Q := P ⧸ J\n"+theorem;
 for(let i=0;i<2;i++){
  const result=checkWorkbenchFiles([{name:"QuotientSyntax.g17",source}],"ZF",["QuotientSyntax.g17"]);
  const t=result.theorems.find(t=>t.name==="QuotientSyntax.identity")!;
  assert.ok(t);assert.match(t.statement,/IsField\(Q\)/);assert.match(JSON.stringify(t.steps),/IsField\(Q\)/);
 }
});
