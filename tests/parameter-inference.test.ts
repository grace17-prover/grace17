// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Parameter inference from the places a mathematician considers obvious:
// `rw thm with facts` fixes the parameters the facts leave open from the
// instance of the rule's side that occurs in the goal or the rewritten
// fact; `rw (thm with facts)` and `simp [(thm with facts)]` accept a
// parenthesised application as a rule; an anonymous constructor infers
// through a `≠` conjunct; a nested application in a with list is
// elaborated against the requirement it fills and then fixes the rest; a
// named premise meets a requirement through one layer of a predicate
// definition; and `0` matches the constructor `zero` an induction case
// substitutes.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[] }

const header = `module ParameterInference
import Grace.Cumulus.Set.Powerset

def cross (A B : Set) : Set := A ∩ B

theorem cross.restrict (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  sorry
`;

function check(source: string): CheckResult {
  return callMachineMethod("check", {
    files: [{ name: "ParameterInference.g17", source: header + source }],
  }) as CheckResult;
}

function checks(source: string): void {
  const result = check(source);
  assert.equal(result.status, "checked",
    result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
}

function failure(source: string): string {
  const result = check(source);
  assert.equal(result.status, "failed", "the module should not check");
  return result.diagnostics.map(item => item.message).join("\n");
}

test("rw thm with facts fixes the open parameters from the goal, a fact, and under rwa", () => {
  checks(`
theorem onGoal (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  rw cross.restrict with sub
  rfl

theorem onFact (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(A, C) = ∅
  shows cross(B, C) ∩ A = ∅
proof
  rw cross.restrict with sub at h
  exact h

theorem reversed (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(A, C) = ∅
  shows cross(B, C) ∩ A = ∅
proof
  rw ← cross.restrict with sub
  exact h

theorem closing (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(B, C) ∩ A = ∅
  shows cross(A, C) = ∅
proof
  rwa cross.restrict with sub
`);
});

test("two different instances of the rule's side in the goal are each rewritten in turn", () => {
  checks(`
theorem bothInstances (A B C D : Set)
  requires sub : A ⊆ B
  requires h : cross(B, C) ∩ A = cross(B, D) ∩ A
  shows cross(A, C) = cross(A, D)
proof
  rw cross.restrict with sub
  exact h
`);
});

test("a parenthesised application is a rule in rw, rwa, and simp lists", () => {
  checks(`
theorem inRw (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  rw (cross.restrict with sub)
  rfl

theorem inRwa (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(B, C) ∩ A = ∅
  shows cross(A, C) = ∅
proof
  rwa (cross.restrict at A, B, C with sub)

theorem inSimp (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  simp [(cross.restrict with sub)]

theorem inSimpAt (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(A, C) = ∅
  shows cross(B, C) ∩ A = ∅
proof
  simp [(cross.restrict with sub)] at h
  exact h
`);
});

test("an anonymous constructor infers through a ≠ conjunct", () => {
  checks(`
def classOf (P v : Set) : Set := P ∩ v
def crossing (P l F : Set) : Set := { e ∈ F | classOf(P, l(e)) ≠ classOf(P, e) }

theorem member (P l F e : Set)
  requires inF : e ∈ F
  shows e ∈ crossing(P, l, F) ∨ classOf(P, l(e)) = classOf(P, e)
proof
  by_cases same : classOf(P, l(e)) = classOf(P, e)
  . right
    exact same
  . left
    have member := crossing.membership.backward with ⟨inF, same⟩
    exact member
`);
});

test("a nested application is elaborated against its requirement and then fixes the remaining parameters", () => {
  checks(`
theorem diff.mono (A B C : Set)
  requires h : A ⊆ B
  shows A ∖ C ⊆ B ∖ C
proof
  sorry

theorem grow (A B x : Set)
  requires ab : A ⊆ B
  requires hx : x ∈ A
  shows x ∈ B
proof
  exact ab with x, hx

theorem nested (C T e x : Set)
  requires bound : C ⊆ T
  requires hx : x ∈ C ∖ {e}
  shows x ∈ T ∖ {e}
proof
  have h := grow with (diff.mono with bound), hx
  exact h
`);
});

test("a named premise meets a requirement through one layer of a predicate definition", () => {
  checks(`
theorem pair.member (w x y : Set)
  requires h : (x, y) ∈ w
  shows x ∈ ⋃ ⋃ w
proof
  sorry

theorem related (w x y : Set)
  requires xy : relates(w, x, y)
  shows x ∈ ⋃ ⋃ w
proof
  exact pair.member with xy

theorem Functional.value (r x y z : Set)
  requires functional : Functional(r)
  requires xy : relates(r, x, y)
  requires xz : relates(r, x, z)
  shows y = z
proof
  exact functional with x, y, xy, z, xz

theorem throughPairs (r x y z : Set)
  requires functional : Functional(r)
  requires xy : (x, y) ∈ r
  requires xz : (x, z) ∈ r
  shows y = z
proof
  exact Functional.value with functional, xy, xz
`);
});

test("the numeral 0 matches the constructor zero an induction case substitutes", () => {
  checks(`
predicate Counted (A n : Set) := n = n

theorem Counted.zero (A : Set)
  requires c : Counted(A, 0)
  shows A = A
proof
  rfl

theorem byInduction (n : Nat)
  shows ∀ A, ∀ m, m = n → Counted(A, m) → A = A
proof
  induction n
  | zero =>
    intros A m e c
    rw e at c
    have r := Counted.zero with c
    exact r
  | succ(k) using ih =>
    intros A m e c
    rfl
`);
});

test("a successor pattern matches a numeral in the fact, predecessor by predecessor", () => {
  const result = callMachineMethod("check", {
    files: [{ name: "Successors.g17", source: `module Successors
import Grace.Cumulus.Nat.Foundation

theorem belowOne (i : Set)
  requires member : i ∈ succ(0)
  shows i ∈ 0 ∨ i = 0
proof
  have alternatives := membership.successor_forward{n := 0} with member
  cases alternatives with empty | equal
  . left
    exact empty
  . right
    exact equal
` }],
  }) as CheckResult;
  assert.equal(result.status, "checked",
    result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
});
