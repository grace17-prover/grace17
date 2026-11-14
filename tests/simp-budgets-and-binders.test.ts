// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The simp semantics met while proving the Abhyankar–Sathaye theorem: a
// closed goal is evaluated only within an evaluation budget estimated from
// its definitions, and the budget and the rewrite budget are settings of
// one call; an equation of the context rewrites a fact under `simp … at h`
// only when it is named; rewrites reach under binders in goals and facts
// alike; a guard an instance supplies lets a conditional rule fire; and a
// short name two modules declare is read from the formula at hand.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";

const header = `module SimpBudgets
import Grace.Cumulus.Algebra.Ring

def wrap (x : Set) : Set := x
def nest0 : Set := {0, 1}
def nest1 : Set := {nest0, nest0}
def nest2 : Set := {nest1, nest1}
def nest3 : Set := {nest2, nest2}
def nest4 : Set := {nest3, nest3}
def nest5 : Set := {nest4, nest4}
def nest6 : Set := {nest5, nest5}
def nest7 : Set := {nest6, nest6}
def nest8 : Set := {nest7, nest7}
def nest9 : Set := {nest8, nest8}
def nest10 : Set := {nest9, nest9}
def nest11 : Set := {nest10, nest10}
def nest12 : Set := {nest11, nest11}
def nest13 : Set := {nest12, nest12}
def nest14 : Set := {nest13, nest13}
def nest15 : Set := {nest14, nest14}
def nest16 : Set := {nest15, nest15}
def alt16 : Set := {nest15, {nest14, nest14}}
def nest17 : Set := {nest16, nest16}
def nest18 : Set := {nest17, nest17}
def nest19 : Set := {nest18, nest18}
def nest20 : Set := {nest19, nest19}
def alt20 : Set := {nest19, {nest18, nest18}}
`;

function check(body: string, imports = ""): ReturnType<typeof createZfKernel> {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "SimpBudgets.g17", source: header.replace("import Grace.Cumulus.Algebra.Ring\n", `import Grace.Cumulus.Algebra.Ring\n${imports}`) + body }], ["lib"]);
  return kernel;
}

function failure(body: string, imports = ""): string {
  try {
    check(body, imports);
  } catch (error) {
    assert.ok(error instanceof Error, String(error));
    return error.message;
  }
  assert.fail("the module should not check");
}

test("a closed goal whose unfolding exceeds the evaluation budget is not evaluated, and the message names the budget", () => {
  const message = failure(`
theorem nested.refused
  shows nest20 = alt20
proof
  simp
`);
  assert.match(message, /did not evaluate it/u);
  assert.match(message, /simp \(compute := \d+\)/u);
});

test("the evaluation budget of one call is raised with simp (compute := N)", () => {
  check(`
theorem nested.computed
  shows nest16 = alt16
proof
  simp (compute := 1000000)
`);
  check(`
theorem nested.small
  shows nest4 = {nest3, {nest2, nest2}}
proof
  simp
`);
});

test("the rewrite budget of one call is raised with simp (steps := N), and the message names it", () => {
  const message = failure(`
theorem wrapped.short (a : Set)
  shows wrap(wrap(wrap(wrap(wrap(wrap(a)))))) = a
proof
  simp (steps := 3) [wrap]
`);
  assert.match(message, /simp stopped after 3 rewrite steps/u);
  assert.match(message, /simp \(steps := 12\)/u);
  check(`
theorem wrapped.enough (a : Set)
  shows wrap(wrap(wrap(wrap(wrap(wrap(a)))))) = a
proof
  simp (steps := 100) [wrap]
`);
  const settings = failure(`
theorem wrapped.setting (a : Set)
  shows wrap(a) = a
proof
  simp (depth := 3) [wrap]
`);
  assert.match(settings, /simp settings are backchain := N, work := N, compute := N, and steps := N/u);
});

test("simp at h rewrites with an equation of the context only when it is named", () => {
  check(`
theorem context.unnamed (f a b c : Set)
  requires h : a = b
  requires k : wrap(f(a)) = f(b)
  shows f(a) = f(b)
proof
  simp [wrap] at k
  exact k

theorem context.named (f a b c : Set)
  requires h : a = b
  requires k : wrap(f(a)) = c
  shows f(b) = c
proof
  simp [wrap, h] at k
  exact k

theorem context.several (f a b c : Set)
  requires h : a = b
  requires k : wrap(f(a)) = c
  requires m : wrap(f(b)) = c
  shows f(b) = c ∧ f(b) = c
proof
  simp (compute := 100, steps := 100) [wrap, h] at k, m
  exact ⟨k, m⟩
`);
});

test("simp reaches under binders in a goal and in a fact, with or without the bound variable in the instance", () => {
  check(`
theorem binder.fact (S T : Set)
  requires h : ∀ a ∈ wrap(S), a ∈ T
  shows ∀ a ∈ S, a ∈ T
proof
  simp [wrap] at h
  exact h

theorem binder.dependent_fact (S T : Set)
  requires h : ∀ p ∈ S, wrap(p) ∈ T
  shows ∀ p ∈ S, p ∈ T
proof
  simp [wrap] at h
  exact h

theorem binder.exists_in_disjunction (S a b : Set)
  requires h : (∃ q ∈ S, wrap(a) = q) ∨ (∃ q ∈ S, wrap(b) = q)
  shows (∃ q ∈ S, a = q) ∨ (∃ q ∈ S, b = q)
proof
  simp [wrap] at h
  exact h

theorem binder.goal (S T : Set)
  requires h : ∀ a ∈ S, a ∈ T
  shows ∀ a ∈ wrap(S), a ∈ T
proof
  simp [wrap]

theorem binder.dependent_goal (S T : Set)
  requires h : ∀ p ∈ S, p ∈ T
  shows ∀ p ∈ S, wrap(p) ∈ T
proof
  simp [wrap]
`);
});

test("a conditional rule fires when an instance supplies its membership guard", () => {
  check(`
section Guarded
variable (R : Set)
hypothesis ring : CommRing(R)

def twice (x : Set) : Set := x + x

instance twice.mem (x : R)
  shows twice(R, x) ∈ R
proof
  unfold twice
  typecheck

theorem guard.fires (a : R)
  shows twice(R, a) - a = twice(R, a) + (-a)
proof
  simp [Ring.sub.value]
end Guarded
`);
});

test("a short name two modules declare is read from the formula, and is ambiguous only when both occur", () => {
  const imports = "import Grace.Cumulus.Algebra.Polynomial.Bundled\n";
  check(`
theorem constant.bundled (R I : Set)
  shows polynomialConstant(R, I) = polynomialCoefficients(I, Ring.carrier(R), Ring.zero(R))
proof
  unfold polynomialConstant
  rfl

theorem constant.raw (I A z a : Set)
  shows polynomialConstant(I, A, z, a) = polynomialTerm(I, A, z, a, monomialOne(I))
proof
  unfold polynomialConstant
  rfl

theorem constant.at (I A z a : Set)
  requires h : polynomialConstant(I, A, z, a) = polynomialTerm(I, A, z, a, monomialOne(I))
  shows polynomialTerm(I, A, z, a, monomialOne(I)) = polynomialTerm(I, A, z, a, monomialOne(I))
proof
  unfold polynomialConstant at h
  rfl

theorem constant.simp (I A z a : Set)
  shows polynomialConstant(I, A, z, a) = polynomialTerm(I, A, z, a, monomialOne(I))
proof
  simp [polynomialConstant]
`, imports);
  const message = failure(`
theorem constant.both (R I a : Set)
  shows polynomialConstant(R, I)(a) = polynomialConstant(I, Ring.carrier(R), Ring.zero(R), a) ∨
    polynomialConstant(R, I)(a) = polynomialConstant(R, I)(a)
proof
  unfold polynomialConstant
`, imports);
  assert.match(message, /ambiguous name polynomialConstant; qualify one of/u);
});
