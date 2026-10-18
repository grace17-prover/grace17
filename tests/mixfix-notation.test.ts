// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// `notation mixfix "_ : _ → _" => FunctionBetween`: the declared form is read
// and printed, an implication with the same tokens is still an implication,
// and the form is unavailable where the declaration is not visible.

import assert from "node:assert/strict";
import test from "node:test";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module MixfixRegression\nimport Grace.Cumulus.Set\n";

test("f : A → B is FunctionBetween(f, A, B) in source and in print", () => {
  const source = header + `
theorem arrow (f A B x : Set)
  requires hf : f : A -> B
  requires hx : x ∈ A
  shows f(x) ∈ B
proof
  exact FunctionBetween.apply_closed with hf, hx

theorem same (f A B : Set)
  requires hf : f : A → B
  shows FunctionBetween(f, A, B)
proof
  exact hf
`;
  const result = checkWorkbenchFiles([{ name: "MixfixRegression.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 400));
  assert.match(JSON.stringify(result), /f : A → B/);
});

test("an implication whose right side is a formula is not a mixfix form", () => {
  const source = header + `
theorem implication (S n : Set)
  requires hn : Nat(n)
  requires closed : ∀ m, Nat(m) → m ∈ S
  shows Nat(n) → n ∈ S
proof
  intro again
  exact closed with hn
`;
  assert.equal(checkWorkbenchFiles([{ name: "MixfixRegression.g17", source }]).ok, true);
});

test("the mixfix form is rejected where its declaration is not visible", () => {
  const source = "module MixfixAbsent\nimport Grace.Core\n" + `
theorem arrow (f A B : Set)
  requires hf : f : A → B
  shows f = f
proof
  rfl
`;
  assert.throws(() => checkWorkbenchFiles([{ name: "MixfixAbsent.g17", source }]), /malformed|unknown|expected/i);
});

test("a mixfix pattern must alternate placeholders and punctuation and match the arity", () => {
  for (const declaration of [
    'notation mixfix "_ : _ → _" => Subset',
    'notation mixfix "_ : _ to _" => FunctionBetween',
    'notation mixfix ": _ → _" => FunctionBetween',
  ]) {
    const source = header + `\n${declaration}\n`;
    assert.throws(() => checkWorkbenchFiles([{ name: "MixfixRegression.g17", source }]), /mixfix|notation/i);
  }
});

test("a binder written with the arrow is a function-space guard", () => {
  const source = header + `
theorem value (A B : Set) (f : A → B) (x : Set)
  requires hx : x ∈ A
  shows f(x) ∈ B
proof
  exact FunctionBetween.apply_closed with *

theorem twice (A B C : Set) (f : A -> B) (g : B → C) (x : Set)
  requires hx : x ∈ A
  shows g(f(x)) ∈ C
proof
  have first : f(x) ∈ B := value with *
  exact value with first

theorem caller (A B f x : Set)
  requires hf : f : A → B
  requires hx : x ∈ A
  shows f(x) ∈ B
proof
  exact value with hf, hx
`;
  const result = checkWorkbenchFiles([{ name: "MixfixRegression.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 400));
});

test("function-space instances synthesize composition and identity guards", () => {
  const source = header + `
theorem composed (A B C x : Set) (f : A → B) (g : B → C)
  requires hx : x ∈ A
  shows (compose(g, f, A, B, C))(x) ∈ C
proof
  exact FunctionBetween.apply_closed with *

theorem composed_function (A B C : Set) (f : A → B) (g : B → C)
  shows compose(g, f, A, B, C) : A → C
proof
  synthesize

theorem identity_composed (A B : Set) (f : A → B)
  shows compose(f, identity(A), A, A, B) : A → B
proof
  synthesize
`;
  assert.equal(checkWorkbenchFiles([{ name: "MixfixRegression.g17", source }]).ok, true);
});
