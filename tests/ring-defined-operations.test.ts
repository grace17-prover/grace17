// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from 'node:test';
import assert from 'node:assert/strict';
import {createZfKernel, loadModuleSourceGraph} from '../src/index.ts';

const check = (source: string, names: readonly string[]): void => {
 const k = createZfKernel();
 loadModuleSourceGraph(k, [{file: 'P.g17', source}], ['lib']);
 for (const name of names) assert.ok(k.theorems.has('P.' + name), name);
};

// The ring certificate reads Ring.sub, Ring.neg, Ring.zero, Ring.one, R[n],
// and Ring.pow through their defining bodies, for a variable ring, a
// declared constant such as complexRing, and a compound ring such as a
// polynomial ring, with or without a hypothesis naming the ring.
test('ring reads subtraction, negation, numerals, and powers of any ring term', () => {
 check(`module P
import Grace.Cumulus.Complex.Field
import Grace.Cumulus.Algebra.Polynomial.Bundled

section Sub
variable (B : Set)
hypothesis comm : CommRing(B)
hypothesis poly : CommRing(polynomialRing(B, 1))

theorem difference (a : polynomialRing(B, 1))
  shows a - a = Ring.zero(polynomialRing(B, 1))
proof
  ring

theorem opposite (a : polynomialRing(B, 1))
  shows -a = -a + Ring.zero(polynomialRing(B, 1))
proof
  ring

end Sub

section Complex
hypothesis complexes : CommRing(complexRing)

theorem twice
  shows complexRing[2] - complexRing[2] - complexRing.one = -complexRing.one
proof
  ring

theorem square
  shows complexRing.one - complexRing.one ^ 2 = complexRing.zero
proof
  ring

theorem powers (a : Set)
  requires member : a ∈ Ring.carrier(complexRing)
  shows (a ^ 2) ^ 3 = a ^ 6
proof
  ring

end Complex

theorem instance_only
  shows complexRing[2] - complexRing[2] = complexRing.zero
proof
  ring

end P
`, ['difference', 'opposite', 'twice', 'square', 'powers', 'instance_only']);
});

// With two commutative rings in context, the ring of a goal is the ring of
// its operations, read through a defined operation such as Ring.sub, and an
// atom defined over that ring is placed by its membership instance.
test('ring and linear_combination place atoms by the operations of the goal', () => {
 check(`module P
import Grace.Cumulus.Complex.Field
import Grace.Cumulus.AlgebraicGeometry.Coordinates.Identities

section Atoms
variable (D : Set)
hypothesis complexes : CommRing(complexRing)
hypothesis ring : CommRing(D)

theorem kill (h u v w t : D)
  requires killS : cuspS(D, h, u, v, w) = t
  shows cuspS(D, h, u, v, w) - t = Ring.zero(D)
proof
  linear_combination killS

theorem cancel (h u v w : D)
  shows cuspS(D, h, u, v, w) - cuspS(D, h, u, v, w) = Ring.zero(D)
proof
  ring

end Atoms

end P
`, ['kill', 'cancel']);
});

// A coefficient of linear_combination may be a negated numeral or a ring
// numeral, read in the ring of the goal.
test('linear_combination accepts negated and ring numerals as coefficients', () => {
 check(`module P
import Grace.Cumulus.Algebra.Ring

section Coefficients
variable (R : Set)
hypothesis ring : CommRing(R)

theorem negated (a b : R)
  requires twice : a + a = b
  shows -a - a = -b
proof
  linear_combination (-1) * twice

theorem numeral (a b : R)
  requires twice : a + a = b
  shows R[2] * a + R[2] * a = R[2] * b
proof
  linear_combination R[2] * twice

end Coefficients

end P
`, ['negated', 'numeral']);
});

// The power of an element of a polynomial ring is the ring's power under
// CommRing(R) alone: X.mem places the variable, polynomialRing.comm_ring
// supplies the ring, and typecheck sees the closure instance.
test('a power in a constructed ring is read through its instances', () => {
 check(`module P
import Grace.Cumulus.Algebra.Polynomial.Bundled

section Powers
variable (K : Set)
hypothesis comm : CommRing(K)

theorem closed
  shows X(K, 4, 1) ^ 2 ∈ Ring.carrier(polynomialRing(K, 4))
proof
  typecheck

theorem binomial
  shows (X(K, 4, 1) + X(K, 4, 2)) ^ 2 =
    X(K, 4, 1) ^ 2 + polynomialRing(K, 4)[2] * X(K, 4, 1) * X(K, 4, 2) +
      X(K, 4, 2) ^ 2
proof
  ring

theorem natural (n : Nat)
  shows 2 ^ n = 2 ^ n
proof
  rfl

end Powers

end P
`, ['closed', 'binomial', 'natural']);
});

// Truncated subtraction in arith: a subtrahend the minuend contains is
// subtracted exactly, through sub.of_add_eq, inside a side or a hypothesis.
test('arith subtracts a contained subtrahend exactly', () => {
 check(`module P
import Grace.Cumulus.Nat.SubtractionLemmas

theorem literal (k : Nat)
  shows 4 + k - 1 = 3 + k
proof
  arith

theorem summand (a b : Nat)
  shows a + b - b = a
proof
  arith

theorem inner (k : Nat)
  shows (4 + k - 1) + 1 = 4 + k
proof
  arith

theorem hypothesis (k : Nat)
  requires shape : k + 3 - 1 = 5
  shows k = 3
proof
  arith

theorem scaled (k : Nat)
  shows 2 * k + 3 - k = k + 3
proof
  arith

end P
`, ['literal', 'summand', 'inner', 'hypothesis', 'scaled']);
});

// A truncated subtraction that is not exact stays an atom: arith does not
// claim k - 3 = k - 2 - 1 or 1 - 2 = 0 - 1 from the lemma.
test('arith leaves an inexact subtraction alone', () => {
 const k = createZfKernel();
 assert.throws(() => loadModuleSourceGraph(k, [{file: 'P.g17', source: `module P
import Grace.Cumulus.Nat.SubtractionLemmas

theorem inexact (k : Nat)
  shows k - 3 = k - 2
proof
  arith

end P
`}], ['lib']), /arith found no supported linear arithmetic step/);
});

// Two instances proving one fully specified proposition are one fact, and
// the first in specificity order stands for it; instances completing an
// open argument differently are still ambiguous.
test('instance search takes the first of several proofs of one fact', () => {
 check(`module P
import Grace.Cumulus.Complex.Field
import Grace.Cumulus.Algebra.Polynomial.Bundled

theorem by_star
  shows CommRing(polynomialRing(complexRing, 2))
proof
  exact polynomialRing.comm_ring with *

theorem by_typecheck
  shows CommRing(complexRing)
proof
  typecheck

section Constants
variable (B : Set)
hypothesis comm : CommRing(B)

theorem constant (h : B)
  requires hom : polynomialConstant(B, 1) : B →+* polynomialRing(B, 1)
  shows polynomialConstant(B, 1)(h) ∈ Ring.carrier(polynomialRing(B, 1))
proof
  typecheck

end Constants

instance ambient.comm_ring
  shows CommRing(polynomialRing(complexRing, 4))
proof
  exact polynomialRing.comm_ring with complexRing.comm_ring

theorem duplicated
  shows X(complexRing, 4, 1) + X(complexRing, 4, 2) ∈
    polynomialRing(complexRing, 4)
proof
  exact Ring.add_mem with *

end P
`, ['by_star', 'by_typecheck', 'constant', 'duplicated']);
});
