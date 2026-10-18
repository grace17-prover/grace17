// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, elaborateModule, loadModuleGraph } from "../src/index.ts";

test("reopened namespaces resolve imported members and preserve local shadowing", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module NamespaceBase
namespace _root_.Euclidean
def Foo (x : Set) : Set := x
predicate Good (x : Set) := Foo(x) = x
theorem good (x : Set)
  shows Good(x)
proof
  unfold Good
  unfold Foo
  rfl
end Euclidean
`);
  const result = elaborateModule(kernel, `
module NamespaceClient
import NamespaceBase
namespace _root_.Euclidean
theorem inherited (x : Set)
  shows Good(Foo(x))
proof
  exact good at Foo(x)
namespace Nested
theorem parent (x : Set)
  shows Good(x)
proof
  exact good at x
def Foo (x : Set) : Set := pair(x, x)
theorem local_wins (x : Set)
  shows Foo(x) = pair(x, x)
proof
  unfold Foo
  rfl
end Nested
end Euclidean
theorem qualified_outside (x : Set)
  shows Euclidean.Nested.Foo(x) = pair(x, x)
proof
  unfold Euclidean.Nested.Foo
  rfl
`);
  assert.equal(result.theorems.length, 4);
  assert.throws(() => elaborateModule(kernel, `
module NamespaceOutside
import NamespaceBase
theorem unqualified (x : Set)
  shows Good(x)
proof
  exact Euclidean.good at x
`), /unknown predicate Good/);
});

test("list literals and cons work in terms and recursive patterns with contextual carriers", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, ["lib/Grace/Core/List.g17"], ["lib"]);
  const result = elaborateModule(kernel, `
module ListNotation
import Grace.Core.List
def headOr {A : Set} (fallback : Set, xs : List(A)) -> Set
  | fallback, [] => fallback
  | fallback, x :: rest => x
theorem association
  shows 1 :: 2 :: [] = [1, 2]
proof
  rfl
theorem contextual_empty (A : Set)
  shows ListOps.length{A}([]) = 0
proof
  exact length.nil at A
theorem contextual_append {A : Set} (xs : List(A))
  shows ListOps.append([], xs) = xs
proof
  exact ListOps.append.right_unit at xs with *
theorem second
  shows headOr{omega}(0, [4, 7, 9]) = 4
proof
  compute
`);
  assert.equal(result.theorems.length, 4);
  assert.throws(() => elaborateModule(kernel, `
module BadListMember
import Grace.Core.List
theorem unsupported (A x : Set)
  shows List(A, [x])
proof
  typecheck
`), /typecheck could not infer/);
});

test("ring obtains coordinate types through checked Tau rules and rejects missing Point evidence", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Geometry/Plane.g17"], ["lib"]);
  elaborateModule(kernel, `
module CoordinateInference
import Grace.Cumulus.Geometry.Plane
namespace Euclidean
theorem automatic (a b : Point)
  shows x(a) * y(b) = y(b) * x(a)
proof
  ring
end Euclidean
`);
  assert.throws(() => elaborateModule(kernel, `
module MissingPoint
import Grace.Cumulus.Geometry.Plane
namespace Euclidean
theorem unsupported (a : Set)
  shows x(a) + (0:R) = x(a)
proof
  ring
end Euclidean
`), /could not establish/);
});
