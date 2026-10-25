// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Parameter inference, round three: the goal meets a conclusion through one
// layer of a predicate definition, for `exact`, `apply`, and an annotated
// `have`; a bare `rfl` entry fixes the side of an equation requirement; a
// theorem stated by a ∀ is instantiated against the requirement it fills;
// projections open a predicate definition; `rw` takes the named-argument
// and parenthesised `at` forms as rules and rewrites every instance a with
// list leaves open; `at` takes a list of facts; and a destructuring
// pattern nests alternatives inside its components.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[] }

const header = `module InferenceRoundThree
import Grace.Cumulus.Set.Powerset

def size (A : Set) : Set := A ∩ A
def cross (A B : Set) : Set := A ∩ B
predicate Big (n : Set) := n ≠ ∅
predicate Tall (A : Set) := Big(size(A))
predicate Bounded (A : Set) := A ⊆ A

theorem Tall.union (A B : Set)
  requires ba : Bounded(A)
  requires bb : Bounded(B)
  shows Tall(A ∪ B) ↔ (Tall(A) ↔ Tall(B))
proof
  sorry

theorem Bounded.of (A C : Set)
  requires h : C ⊆ C
  shows Bounded(A)
proof
  sorry

theorem pair.of (w x y : Set)
  requires h : x ∈ ⋃ ⋃ w
  shows (x, y) ∈ w
proof
  sorry

theorem pair.iff (w x y : Set)
  shows (x, y) ∈ w ↔ x ∈ ⋃ ⋃ w ∧ y = y
proof
  sorry

theorem cross.restrict (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  sorry
`;

function check(source: string, head = header): CheckResult {
  return callMachineMethod("check", {
    files: [{ name: "InferenceRoundThree.g17", source: head + source }],
  }) as CheckResult;
}

function checks(source: string, head = header): void {
  const result = check(source, head);
  assert.equal(result.status, "checked",
    result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
}

function failure(source: string, head = header): string {
  const result = check(source, head);
  assert.equal(result.status, "failed", "the module should not check");
  return result.diagnostics.map(item => item.message).join("\n");
}

test("the goal meets the conclusion through one definition layer in exact, apply, and refine", () => {
  checks(`
theorem openedConclusion (X Y : Set)
  requires hX : X ⊆ X
  requires hY : Y ⊆ Y
  shows Big(size(X ∪ Y)) ↔ (Big(size(X)) ↔ Big(size(Y)))
proof
  exact Tall.union with (Bounded.of with hX), (Bounded.of with hY)

theorem openedGoal (w x y : Set)
  requires h : x ∈ ⋃ ⋃ w
  shows relates(w, x, y)
proof
  exact pair.of with h

theorem openedGoalBackward (w x y : Set)
  requires hx : x ∈ ⋃ ⋃ w
  shows relates(w, x, y)
proof
  exact pair.iff.backward with ⟨hx, rfl⟩

theorem openedGoalApply (w x y : Set)
  requires h : x ∈ ⋃ ⋃ w
  shows relates(w, x, y)
proof
  apply pair.of
  exact h

theorem openedComponent (w x y : Set)
  requires h : x ∈ ⋃ ⋃ w
  shows relates(w, x, y) ∧ x ∈ ⋃ ⋃ w
proof
  refine ⟨(pair.of with h), h⟩
`);
});

test("an annotated have meets Nat(t) through t ∈ ℕ", () => {
  checks(`
theorem fromGoal (A : Set)
  requires h : A ⊆ A
  shows weigh(A, A) ∈ ℕ
proof
  have weight : weigh(A, A) ∈ ℕ := weigh.natural with h
  exact weight
`, `module InferenceRoundThree
import Grace.Cumulus.Nat.Foundation

def weigh (A B : Set) : Set := A ∪ B

theorem weigh.natural (A B : Set)
  requires h : A ⊆ A
  shows Nat(weigh(A, B))
proof
  sorry
`);
});

test("a bare rfl entry fixes the open side of an equation requirement", () => {
  checks(`
theorem sized (F n : Set)
  requires h : F ⊆ F
  requires equation : size(F) = n
  shows n ⊆ size(F)
proof
  sorry

theorem bareRfl (F : Set)
  requires h : F ⊆ F
  shows size(F) ⊆ size(F)
proof
  have r := sized with h, rfl
  exact r

theorem bareRflExact (F : Set)
  requires h : F ⊆ F
  shows size(F) ⊆ size(F)
proof
  exact sized with h, rfl
`);
});

test("a theorem stated by a ∀ is instantiated against the requirement it fills", () => {
  checks(`
theorem Bounded.sub (S T : Set)
  requires bt : Bounded(T)
  requires st : S ⊆ T
  shows Bounded(S)
proof
  sorry

theorem difference.sub (A B : Set)
  shows A ∖ B ⊆ A
proof
  sorry

theorem bareName (X Y : Set)
  requires bX : Bounded(X)
  shows Bounded(X ∖ Y)
proof
  exact Bounded.sub with bX, difference.sub

theorem parenthesisedName (X Y : Set)
  requires bX : Bounded(X)
  shows Bounded(X ∖ Y)
proof
  exact Bounded.sub with bX, (difference.sub)
`);
});

test("projections open a predicate definition", () => {
  checks(`
predicate Tidy (V P : Set) := (∀ X ∈ P, X ⊆ V) ∧ (P ⊆ P) ∧ (V ⊆ V)

theorem projected (V P : Set)
  requires tidy : Tidy(V, P)
  shows P ⊆ P
proof
  exact tidy.right.left

theorem projectedHave (V P : Set)
  requires tidy : Tidy(V, P)
  shows V ⊆ V
proof
  have h := tidy.right.right
  exact h

theorem projectedSpecialize (V P X : Set)
  requires tidy : Tidy(V, P)
  requires hX : X ∈ P
  shows X ⊆ V
proof
  have classes := tidy.left
  exact classes with X, hX

theorem projectedCases (V P : Set)
  requires tidy : Tidy(V, P)
  shows V ⊆ V
proof
  rcases tidy.right with ⟨_, h⟩
  exact h
`);
});

test("the named-argument and parenthesised at forms are rules in rw, rwa, and simp lists", () => {
  checks(`
theorem namedArguments (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  rw cross.restrict{A := A, B := B, C := C}
  rfl

theorem parenthesisedAt (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  rw (cross.restrict at A, B, C)
  rfl

theorem closing (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(B, C) ∩ A = ∅
  shows cross(A, C) = ∅
proof
  rwa (cross.restrict at A, B, C)

theorem inSimp (A B C : Set)
  requires sub : A ⊆ B
  shows cross(A, C) = cross(B, C) ∩ A
proof
  simp [cross.restrict{A := A, B := B, C := C}]

theorem inSimpParenthesised (A B C : Set)
  requires sub : A ⊆ B
  requires h : cross(A, C) = ∅
  shows cross(B, C) ∩ A = ∅
proof
  simp [(cross.restrict at A, B, C)] at h
  exact h
`);
});

test("rw thm with facts rewrites every instance of the rule's side in turn", () => {
  checks(`
theorem bothInstances (A B C D : Set)
  requires sub : A ⊆ B
  requires h : cross(B, C) ∩ A = cross(B, D) ∩ A
  shows cross(A, C) = cross(A, D)
proof
  rw cross.restrict with sub
  exact h

theorem bothInstancesAt (A B C D : Set)
  requires sub : A ⊆ B
  requires h : cross(A, C) = cross(A, D)
  shows cross(B, C) ∩ A = cross(B, D) ∩ A
proof
  rw cross.restrict with sub at h
  exact h
`);
});

test("conflicting facts still stop a rewrite", () => {
  assert.match(failure(`
theorem conflict (A B C : Set)
  requires sub : A ⊆ B
  requires other : B ⊆ A
  shows cross(A, C) = cross(B, C) ∩ A
proof
  rw cross.restrict with sub, other
  rfl
`), /cross\.restrict: named premise other/);
});

test("rw, rwa, simp, and unfold take a list of facts after at", () => {
  checks(`
theorem rewriteList (A B C : Set)
  requires sub : A ⊆ B
  requires h1 : cross(A, C) = ∅
  requires h2 : cross(A, C) ⊆ ∅
  shows cross(B, C) ∩ A = ∅ ∧ cross(B, C) ∩ A ⊆ ∅
proof
  rw cross.restrict with sub at h1, h2
  exact ⟨h1, h2⟩

theorem rewriteAndClose (A B C : Set)
  requires sub : A ⊆ B
  requires h1 : cross(A, C) = ∅
  requires h2 : cross(A, C) ⊆ ∅
  shows cross(B, C) ∩ A ⊆ ∅
proof
  rwa cross.restrict with sub at h1, h2

theorem simpList (A B C : Set)
  requires sub : A ⊆ B
  requires h1 : cross(A, C) = ∅
  requires h2 : cross(A, C) ⊆ ∅
  shows cross(B, C) ∩ A = ∅ ∧ cross(B, C) ∩ A ⊆ ∅
proof
  simp [(cross.restrict with sub)] at h1, h2
  exact ⟨h1, h2⟩

theorem unfoldList (A B : Set)
  requires h1 : Bounded(A)
  requires h2 : Bounded(B)
  shows A ⊆ A ∧ B ⊆ B
proof
  unfold Bounded at h1, h2
  exact ⟨h1, h2⟩

theorem bracketList (A B C D : Set)
  requires sub : A ⊆ B
  requires e : ∅ = D
  requires h1 : cross(A, C) = ∅
  requires h2 : cross(A, C) ⊆ ∅
  shows cross(B, C) ∩ A = D ∧ cross(B, C) ∩ A ⊆ D
proof
  rw [(cross.restrict with sub), e] at h1, h2
  exact ⟨h1, h2⟩
`);
});

test("alternatives nest inside the components of a destructuring pattern", () => {
  checks(`
theorem nested (A B x : Set)
  requires reached : x ∈ A ∧ (x ∈ B ∨ x ∈ B)
  shows x ∈ B
proof
  rcases reached with ⟨_, same | path⟩
  . exact same
  . exact path

theorem nestedObtain (A B x : Set)
  requires reached : x ∈ A ∧ (x ∈ B ∨ x ∈ B)
  shows x ∈ B
proof
  obtain ⟨inA, same | path⟩ := reached
  . exact same
  . exact path

theorem nestedThreeWay (A B x y : Set)
  requires reached : x ∈ A ∧ (x ∈ B ∨ x = y ∨ ∃ z, z ∈ B ∧ x = z)
  requires inB : y ∈ B
  shows x ∈ B
proof
  rcases reached with ⟨inA, same | rfl | ⟨z, hz, rfl⟩⟩
  . exact same
  . exact inB
  . exact hz

theorem alternativeFollowedByComponent (A B x : Set)
  requires reached : (x ∈ A ∨ x ∈ A) ∧ x ∈ B
  shows x ∈ A ∧ x ∈ B
proof
  rcases reached with ⟨first | second, inB⟩
  . exact ⟨first, inB⟩
  . exact ⟨second, inB⟩
`);
});
