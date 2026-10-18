// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { NameResolutionIndex, AmbiguousNameError } from "../src/name-resolution.ts";
import { createZfgKernel, elaborateModule, forkSurfaceEnvironment } from "../src/index.ts";

test("public names and kernel identities survive moving declarations between modules", () => {
  const kernels = ["First.Location", "Another.Location"].map(module => {
    const kernel = createZfgKernel();
    const result = elaborateModule(kernel, `module ${module}
namespace _root_.Shared.Geometry
def identity (x : Set) : Set := x
theorem identity.correct (x : Set)
  shows identity(x) = x
proof
  unfold identity
  rfl
end Shared.Geometry
`);
    assert.deepEqual(result.definitions, ["Shared.Geometry.identity"]);
    assert.deepEqual(result.theorems, ["Shared.Geometry.identity.correct"]);
    return kernel;
  });
  assert.equal(kernels[0]!.digest(), kernels[1]!.digest());
});

test("ambiguity is independent of open order, explicit root bypasses it, and missing imports stay hidden", () => {
  const kernel = createZfgKernel();
  for (const ns of ["Left", "Right"]) elaborateModule(kernel, `module File${ns}
namespace _root_.${ns}
def value : Set := empty
theorem fact
  shows value = empty
proof
  unfold value
  rfl
end ${ns}
`);
  for (const order of [["Left", "Right"], ["Right", "Left"]]) {
    const fork = kernel.fork(); forkSurfaceEnvironment(kernel, fork);
    assert.throws(() => elaborateModule(fork, `module Client${order[0]}
import FileLeft
import FileRight
open ${order[0]}
open ${order[1]}
theorem collision
  shows value = empty
proof
  rfl
`), /ambiguous name value; qualify one of: Left.value \(module FileLeft\), Right.value \(module FileRight\)/);
  }
  assert.throws(() => elaborateModule(kernel, `module Hidden
open Left
`), /unimported namespace/);
  assert.throws(() => elaborateModule(kernel, `module HiddenTerm
def hidden : Set := Left.value
`), /unknown variable or constant Left.value/);
  elaborateModule(kernel, `module Explicit
import FileLeft
import FileRight
open Left
open Right
theorem explicit
  shows _root_.Left.value = empty
proof
  exact _root_.Left.fact
`);
  assert.throws(() => elaborateModule(kernel, `module ProofCollision
import FileLeft
import FileRight
open Left
open Right
theorem attempted
  shows _root_.Left.value = empty
proof
  exact fact
`), /ambiguous name fact/);
});

test("a short name shared by two modules resolves to the one whose module the goal or a local fact already draws on", () => {
  const kernel = createZfgKernel();
  for (const ns of ["Wide", "Narrow"]) elaborateModule(kernel, `module File${ns}
namespace _root_.${ns}
predicate Inner (x : Set) := x = x
predicate Outer (x : Set) := Inner(x)
end ${ns}
`);
  for (const ns of ["Wide", "Narrow"]) {
    const fork = kernel.fork(); forkSurfaceEnvironment(kernel, fork);
    elaborateModule(fork, `module Client${ns}
import FileWide
import FileNarrow
open Wide
open Narrow
theorem unfolding (x : Set)
  requires outer : ${ns}.Outer(x)
  shows x = x
proof
  unfold Outer at outer
  unfold Inner at outer
  exact outer
`);
    assert.ok(fork.theorems.has(`Client${ns}.unfolding`));
  }
});

test("public duplicate declarations are rejected and namespace opens have lexical scope", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module A
namespace _root_.Shared
def value : Set := empty
end Shared
`);
  assert.throws(() => elaborateModule(kernel, `module B
import A
namespace _root_.Shared
def value : Set := empty
end Shared
`), /duplicate declaration Shared.value; already provided by module A/);
  elaborateModule(kernel, `module C
import A
namespace Outer.Inner
open Shared
theorem inside
  shows value = empty
proof
  unfold value
  rfl
end Outer.Inner
`);
  assert.throws(() => elaborateModule(kernel, `module D
import A
namespace Local
open Shared
end Local
def outside : Set := value
`), /unknown variable or constant value/);
});

test("lookup and misses probe relevant names only and invalidate after new declarations", () => {
  const index = new NameResolutionIndex();
  const symbols = new Set<string>();
  for (let i = 0; i < 50000; i++) {
    const name = `Unrelated.N${i}.value${i}`;
    symbols.add(name); index.register(name, `File${i}`);
  }
  const opens = Array.from({ length: 100 }, (_, i) => `Used${i}`);
  index.register("Used7.target", "A"); symbols.add("Used7.target");
  let probes = 0;
  const exists = (name: string) => { probes++; return symbols.has(name); };
  assert.equal(index.resolve("target", [], opens, exists), "Used7.target");
  assert.equal(probes, 1);
  probes = 0;
  assert.equal(index.resolve("missing", [], opens, exists), undefined);
  assert.equal(probes, 1); // only the root fallback, never a library scan
  index.register("Used8.target", "B"); symbols.add("Used8.target");
  assert.throws(() => index.resolve("target", [], opens, exists), AmbiguousNameError);
  index.register("Used9.missing", "C"); symbols.add("Used9.missing");
  assert.equal(index.resolve("missing", [], opens, exists), "Used9.missing");
  assert.equal(index.resolve("fn.equation", [], opens, exists), undefined);
  index.register("Used9.fn", "C"); symbols.add("Used9.fn.equation");
  assert.equal(index.resolve("fn.equation", [], opens, exists), "Used9.fn.equation");
});
