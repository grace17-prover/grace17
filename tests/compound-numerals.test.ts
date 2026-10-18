// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { app, createZfgKernel, elaborateModule, formatFormula, formatTerm, notationReport } from "../src/index.ts";

const header = `module CompoundNumerals
namespace CompoundNumerals
class Fruit (x : Set) := x = x
predicate OfNat (carrier numeral value : Set) := carrier = carrier
def carrier : Set := empty
def call2 (operation left right : Set) : Set := pair(left, right)
instance two
  shows OfNat(carrier, 2, call2(empty, empty, empty))
proof
  unfold OfNat
  rfl
predicate HasAdd (carrier operation : Set) := carrier = carrier
instance add
  shows HasAdd(carrier, empty)
proof
  unfold HasAdd
  rfl
notation infixl 60 "+" => call2 via HasAdd(carrier, _) for Fruit
notation numeral "2" via OfNat(carrier, 2, _) for Fruit`;

test("compound numeral instances preserve their full checked value and print specifically", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, header + `
theorem value (x : Fruit)
  shows x + 2 = call2(empty, x, call2(empty, empty, empty))
proof
  rfl
end CompoundNumerals
`);
  const notation = notationReport(kernel);
  const two = notation.find(item => item.token === "2")!;
  assert.deepEqual(two.leadingArguments, [app("empty"), app("empty"), app("empty")]);
  assert.equal(formatTerm(app(two.target, ...two.leadingArguments!), { notations: notation }), "2");
  const statement = kernel.theorems.get("CompoundNumerals.value")!;
  assert.match(formatFormula(statement, { notations: notation }), /2/);
  kernel.checkProof(kernel.theoremProofs.get("CompoundNumerals.value")!);
});

test("compound numeral notation rejects mismatched values", () => {
  assert.throws(() => elaborateModule(createZfgKernel(), header + `
theorem wrong (x : Fruit)
  shows x + 2 = call2(empty, x, empty)
proof
  rfl
end CompoundNumerals
`), /reflexive|establish|rfl|reflexivity/);
});
