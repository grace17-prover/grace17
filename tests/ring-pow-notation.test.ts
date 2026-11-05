// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {createZfKernel, loadModuleSourceGraph} from '../src/index.ts';

// Powers in a bundled ring: x ^ n is Ring.pow, ring reads literal powers as
// products, typecheck sees the closure instance, and the identity that
// opens the explicit hypersurface closes with one call.
test('x ^ n in a bundled commutative ring: ring and typecheck read it', () => {
 const k=createZfKernel();
 loadModuleSourceGraph(k,[{file:'P.g17',source:`module P
import Grace.Cumulus.Algebra.Ring
section Powers
variable (R : Set)
hypothesis ring : CommRing(R)

def cuspS (h u v w : Set) : Set :=
  R[2]*u^3*v + R[3]*u^4*w + h*(v^2 - R[3]*u^2*w^2) + h^2*w^3

theorem square (x y : R)
  shows (x + y)^2 = x^2 + R[2]*x*y + y^2
proof
  ring

theorem cusp (h u v w : R)
  shows (u^3 + h*v)^2 + (-u^2 + h*w)^3 = h * cuspS(R, h, u, v, w)
proof
  unfold cuspS
  ring

theorem closed (h u v w : R)
  shows cuspS(R, h, u, v, w) ∈ R
proof
  unfold cuspS
  typecheck

theorem laws (x : R) (n : Nat)
  shows x ^ (n + 1 + 1) = x ^ n * x * x
proof
  have first : x ^ (n + 1 + 1) = x ^ (n + 1) * x :=
    Ring.pow_succ at R, x, n + 1 with *
  have second : x ^ (n + 1) = x ^ n * x := Ring.pow_succ with *
  rw [first, second]
  rfl
end Powers
`}],['lib']);
 for (const name of ['square','cusp','closed','laws'])
  assert.ok(k.theorems.has('P.'+name), name);
});
