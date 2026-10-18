// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfgKernel, elaborateModule, exportTheorem, verifyExportedProof } from "../src/index.ts";

function check(source: string) {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, source);
  return { kernel, result };
}

test("definition result proofs are generated, namespaced, exported, and immediately usable", () => {
  const { kernel, result } = check(`namespace Example
 def identity (n : Nat) : Nat := n
 theorem use (n : Nat)
   shows Nat(identity(n))
 proof
   exact identity.type at n with *
 end Example`);
  assert.deepEqual(result.theorems, ["Example.identity.type", "Example.use"]);
  assert.ok(verifyExportedProof(kernel, exportTheorem(kernel, "Example.identity.type")));
});

test("Set declarations need no result theorem", () => {
  const { result } = check("def identity (x : Set) : Set := x");
  assert.deepEqual(result.theorems, []);
});

test("unproved annotations cannot certify themselves or other definitions", () => {
  assert.throws(() => check("def bad (x : Set) : Nat := x"), /cannot prove declared result type/);
  assert.throws(() => check(`def bad (x : Set) : Nat := x
 def worse (x : Set) : Nat := bad(x)`), /cannot prove declared result type/);
  assert.throws(() => check(`def bad (x : Set) : Nat := x
 proof
   typecheck`));
});

test("explicit result proof blocks support facts outside automatic type inference", () => {
  const { kernel } = check(`predicate EqualZero (x : Set) := x = 0
 def zeroValue (x : Set) : EqualZero := 0
 proof
   unfold EqualZero
   unfold zeroValue
   rfl`);
  assert.ok(kernel.theorems.has("zeroValue.type"));
});

test("a later closure proof discharges a pending annotation", () => {
  const { kernel } = check(`predicate EqualZero (x : Set) := x = 0
 def zeroValue (x : Set) : EqualZero := 0
 theorem zeroValue.type (x : Set)
   shows EqualZero(zeroValue(x))
 proof
   unfold EqualZero
   unfold zeroValue
   rfl`);
  assert.ok(kernel.theorems.has("zeroValue.type"));
});

test("a misleading manual type theorem cannot discharge the annotation", () => {
  assert.throws(() => check(`def bad (x : Set) : Nat := x
 theorem bad.type (x : Nat)
   shows Nat(bad(x))
 proof
   unfold bad
   assumption`), /does not establish the declared result type/);
});

test("structural result induction respects namespaces and binder freshness", () => {
  const { kernel, result } = check(`namespace Nested
 def plus (__field0 __ih0 : Nat) -> Nat
   | zero, __ih0 => __ih0
   | succ(k), __ih0 => succ(plus(k, __ih0))
 theorem use (x y : Nat)
   shows Nat(plus(x, y))
 proof
   exact plus.type at x, y with *
 end Nested`);
  assert.deepEqual(result.theorems, ["Nested.plus.type", "Nested.use"]);
  assert.ok(kernel.theorems.has("Nested.plus.type"));
  assert.equal(kernel.theorems.has("Nested.Nested.plus.type"), false);
  assert.deepEqual(kernel.theoremTacticTraces.get("Nested.plus.type")?.steps.map(x => x.line), [2]);
});

test("implicit and multi-parameter datatype result proofs retain their parameters", () => {
  const { kernel } = check(`namespace Parametric
 datatype Cell(A B : Set)
   | cell(left : A, right : B)
 def copy {A B : Set} (value : Cell(A,B)) : Cell(A,B) := value
 def second (value : Cell(ℕ,ℕ)) -> Nat
   | Cell.cell(a, b) => b
 end Parametric`);
  assert.ok(kernel.theorems.has("Parametric.copy.type"));
  assert.ok(kernel.theorems.has("Parametric.second.type"));
});

test("definition proof blocks support authored structural induction", () => {
  const { kernel } = check(`def copy (n : Nat) -> Nat
   | zero => zero
   | succ(k) => succ(copy(k))
 proof
   induction n
   | zero =>
     rw copy
     typecheck
   | succ(k) using ih =>
     rw copy
     typecheck`);
  assert.ok(kernel.theorems.has("copy.type"));
});

test("nested datatype predicates cannot masquerade as carrier sets", () => {
  assert.throws(() => check(`datatype Box(A : Set)
   | box(value : A)
 def invalid (x : Set) : Box(Box(ℕ)) := x`), /invalid result-type carrier/);
  assert.throws(() => check(`datatype Box(A : Set)
   | box(value : A)
 def invalid (x : Box(Box(ℕ))) : Set := x`), /invalid input-type carrier/);
});

test("Set-valued structural definitions retain checked computation without a carrier claim", () => {
  const { kernel, result } = check(`datatype Box(A : Set)
   | box(value : A)
 def unbox (x : Set) -> Set
   | Box.box(value) => value
   descends x
 theorem example
   shows unbox(Box.box(0)) = 0
 proof
   compute`);
  assert.deepEqual(result.theorems, ["example"]);
  assert.ok(kernel.theorems.has("example"));
});

test("generated type theorems have hover information and stable definition locations", async () => {
  const { checkWorkbenchFiles } = await import("../src/workbench.ts");
  const source = `module DefinitionHover
namespace DefinitionHover
def identity (n : Nat) : Nat := n
end DefinitionHover`;
  for (const suffix of ["", "\n-- edit\n"]) {
    const result = checkWorkbenchFiles([{ name: "DefinitionHover.g17", source: source + suffix }]);
    const symbol = result.symbols.find(item => item.name === "DefinitionHover.identity.type");
    assert.ok(symbol);
    assert.match(symbol.info, /ℕ/);
    const proof = result.theorems.find(item => item.name === symbol.name);
    assert.equal(proof?.lineStart, 3);
    assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  }
});
