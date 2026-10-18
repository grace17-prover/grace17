// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {createZfKernel, loadModuleSourceGraph, formulaEquals} from '../src/index.ts';
test('scoped powers preserve kernel terms, natural exponent arithmetic and precedence', () => {
 const k=createZfKernel();
 loadModuleSourceGraph(k,[{file:'P.g17',source:`module P
import Grace.Cumulus.Algebra.Group.Power
import Grace.Cumulus.Nat.Pow
section Powers
variable (A plus z minus times unit : Set)
notation ring R := (A, plus, z, minus, times, unit)
theorem compact (x y : Set) (n : Nat)
  shows R[x ^ (n + 1) * y] = R[x ^ (n + 1) * y]
proof
  rfl
theorem explicit (x y : Set) (n : Nat)
  shows call2(times, monoidPow(times, unit, x, add(n, (1:Nat))), y) = call2(times, monoidPow(times, unit, x, add(n, (1:Nat))), y)
proof
  rfl
theorem tower (x : Set)
  shows R[x ^ 2 ^ 3] = monoidPow(times, unit, x, pow((2:Nat), (3:Nat)))
proof
  rfl
end Powers
`}],['lib']);
 assert.ok(formulaEquals(k.theorems.get('compact')!,k.theorems.get('explicit')!));
});

test('power goal rendering retains the ring and keeps the exponent natural', async () => {
 const {app,v,nat,formatTerm}=await import('../src/index.ts');
 const ring={name:'ℂ',carrier:v('A'),add:v('plus'),zero:v('z'),neg:v('minus'),mul:v('times'),one:v('unit'),call1:'apply',call2:'call2'};
 const power=app('Grace.Cumulus.Algebra.Group.Power.monoidPow',ring.mul,ring.one,v('x'),app('Grace.Core.Nat.Rec.add',v('n'),nat(1)));
 assert.equal(formatTerm(power,{rings:[ring]}),'x ^ (n + 1)');
 assert.doesNotMatch(formatTerm(app('Other.monoidPow',ring.mul,ring.one,v('x'),nat(2)),{rings:[ring]}),/\^/);
});
