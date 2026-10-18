// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, elaborateModule, loadModuleSourceGraph, formulaEquals, compileProofModule, exportTheoremForMachine, verifyProofMachine } from "../src/index.ts";
const prefix = `module Numerals
namespace Numerals
import Grace.Cumulus.Algebra.Ring
section Rings
variable (A add zero neg mul one B plus z minus times unit : Set)
`;
const aliases = ["", "notation ring R := (A, add, zero, neg, mul, one)\n", "notation ring R := (A, add, zero, neg, mul, one)\nnotation ring S := (B, plus, z, minus, times, unit)\n"];
const body = [0, 1, 2].map(n => `theorem numeral${n} (x : Set)
  requires h : x = (${n} : Nat)
  shows (${n} : Nat) = x
proof
  rw h
  rfl
`).join("\n") + "end Rings\nend Numerals\n";
function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Numerals.g17", source }], ["lib"]);
  return kernel;
}
test("explicit natural numerals preserve their formulas and proofs in one or two ring scopes", () => {
  const plain = load(prefix + body);
  for (const alias of aliases.slice(1)) {
    const scoped = load(prefix + alias + body);
    for (const n of [0, 1, 2]) {
      const name = `Numerals.numeral${n}`;
      assert.ok(formulaEquals(plain.theorems.get(name)!, scoped.theorems.get(name)!));
      const proof = compileProofModule([exportTheoremForMachine(scoped, name)]);
      assert.deepEqual(proof, compileProofModule([exportTheoremForMachine(plain, name)]));
      verifyProofMachine(scoped, proof);
    }
  }
});
test("an annotated occurrence does not change later unannotated ring numerals", () => {
  const tail = `theorem ambient
  shows 0 = zero ∧ 1 = one
proof
  constructor
  . rfl
  . rfl
end Rings
end Numerals
`;
  const before = load(prefix + aliases[1] + tail);
  load(prefix + aliases[2] + body);
  const after = load(prefix + aliases[1] + tail);
  assert.ok(formulaEquals(before.theorems.get("Numerals.ambient")!, after.theorems.get("Numerals.ambient")!));
  verifyProofMachine(after, compileProofModule([exportTheoremForMachine(after, "Numerals.ambient")]));
});

test("natural annotations do not leak through interning into contextual numerals", () => {
  const kernel = createZfKernel();
  elaborateModule(kernel, `module Occurrences
namespace Occurrences
class Fruit (x : Set) := x = x
predicate OfNat (carrier numeral value : Set) := carrier = carrier
def carrier : Set := empty
def fruitTwo : Set := pair(empty, empty)
instance two
  shows OfNat(carrier, 2, fruitTwo)
proof
  unfold OfNat
  rfl
notation numeral "2" via OfNat(carrier, 2, _) for Fruit

theorem annotated
  shows (2 : Nat) = (2 : Nat)
proof
  rfl

theorem contextual (x : Fruit)
  requires h : x = 2
  shows x = fruitTwo
proof
  exact h
end Occurrences
`);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "Occurrences.contextual")]));
});
