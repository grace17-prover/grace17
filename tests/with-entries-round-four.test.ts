// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// With-list entries, round four: the entries of a with list are matched
// to requirements in whatever order they are written, a theorem stated by
// a ∀ waiting for the entries that fix the parameters its requirement
// mentions; a theorem's own binders never collide with the names in
// scope; a ∀-theorem with requirements is a bare entry when the context
// discharges them; a parenthesised application takes projections; a bare
// an unannotated have whose conclusion-only parameters stay open names
// them and takes `_` holes in an at list.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[] }

const header = `module WithEntriesRoundFour
import Grace.Cumulus.Set.Powerset

predicate Linked (F u v : Set) := u ∈ F ∧ v ∈ F
predicate Small (A : Set) := A ⊆ A
predicate Apart (A B : Set) := A ∩ B = ∅
def pick (A V : Set) : Set := A ∩ V

theorem Linked.monotone (F G u v : Set)
  requires subset : F ⊆ G
  requires linked : Linked(F, u, v)
  shows Linked(G, u, v)
proof
  sorry

theorem Linked.of_member (G F e : Set)
  requires member : e ∈ F
  shows Linked(G, e, e)
proof
  sorry

theorem join.sub_left (A B : Set)
  shows A ⊆ A ∪ B
proof
  sorry

theorem meet.sub_left (A B : Set)
  shows A ∩ B ⊆ A
proof
  sorry

theorem diff.sub_left (A B : Set)
  shows A ∖ B ⊆ A
proof
  sorry

theorem Small.subset (S T : Set)
  requires small : Small(T)
  requires subset : S ⊆ T
  shows Small(S)
proof
  sorry

theorem Small.singleton (x : Set)
  shows Small({x})
proof
  sorry

theorem Apart.of_subset_right (A B C : Set)
  requires h : Apart(A, C)
  requires hBC : B ⊆ C
  shows Apart(A, B)
proof
  sorry

theorem Apart.difference_left (A B : Set)
  shows Apart(A ∖ B, B)
proof
  sorry

theorem both.bounded (V u t : Set)
  requires inV : V ⊆ V
  requires left : ∀ v ∈ V, u(v) ⊆ V
  requires right : ∀ v ∈ V, t(v) ⊆ V
  requires agree : ∀ v ∈ V, u(v) = t(v)
  shows V ⊆ V
proof
  sorry

theorem pick.bounded (A V : Set)
  shows ∀ v ∈ V, pick(A, V)(v) ⊆ V
proof
  sorry

theorem Small.each (A V : Set)
  requires small : Small(A)
  shows ∀ v ∈ V, pick(A, V)(v) ⊆ V
proof
  sorry

theorem pair.split (F u v : Set)
  requires linked : Linked(F, u, v)
  shows u ∈ F ∧ v ∈ F
proof
  sorry

theorem pair.iff (F u v : Set)
  shows Linked(F, u, v) ↔ u ∈ F ∧ v ∈ F
proof
  sorry
`;

function check(source: string): CheckResult {
  return callMachineMethod("check", {
    files: [{ name: "WithEntriesRoundFour.g17", source: header + source }],
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

test("a bare ∀-theorem entry waits for the entries that fix its requirement, in any order", () => {
  checks(`
theorem theoremFirst (A B u v : Set)
  requires linked : Linked(A, u, v)
  shows Linked(A ∪ B, u, v)
proof
  exact Linked.monotone with join.sub_left, linked

theorem factFirst (A B u v : Set)
  requires linked : Linked(A, u, v)
  shows Linked(A ∪ B, u, v)
proof
  exact Linked.monotone with linked, join.sub_left

theorem singletonFirst (A x : Set)
  requires subset : A ⊆ {x}
  shows Small(A)
proof
  exact Small.subset with Small.singleton, subset

theorem fixedAfterwards (A B V : Set)
  requires inV : V ⊆ V
  requires agree : ∀ v ∈ V, pick(A, V)(v) = pick(B, V)(v)
  shows V ⊆ V
proof
  exact both.bounded with inV, pick.bounded, pick.bounded, agree
`);
});

test("a theorem's own binders do not collide with the names in scope", () => {
  checks(`
theorem collision (A B C : Set)
  requires second : Small(B)
  shows Small(B ∩ C)
proof
  exact Small.subset with second, meet.sub_left

theorem collisionHave (A B C : Set)
  requires second : Small(B)
  shows Small(B ∩ C)
proof
  have h : Small(B ∩ C) := Small.subset with second, meet.sub_left
  exact h
`);
});

test("a parenthesised at-application fixes the binders a bare entry needs", () => {
  checks(`
theorem apart (A B : Set)
  shows Apart(A ∖ B, B ∖ A)
proof
  exact Apart.of_subset_right with (Apart.difference_left at A, B), diff.sub_left

theorem apartReversed (A B : Set)
  shows Apart(A ∖ B, B ∖ A)
proof
  exact Apart.of_subset_right with diff.sub_left, (Apart.difference_left at A, B)
`);
});

test("a ∀-theorem with requirements is a bare entry when the context discharges them", () => {
  checks(`
theorem viaRequires (A B V : Set)
  requires smallA : Small(A)
  requires smallB : Small(B)
  requires inV : V ⊆ V
  requires agree : ∀ v ∈ V, pick(A, V)(v) = pick(B, V)(v)
  shows V ⊆ V
proof
  exact both.bounded with inV, Small.each, Small.each, agree
`);
});

test("a parenthesised application takes .left, .right, .forward, and .backward", () => {
  checks(`
theorem projectedExact (F u v : Set)
  requires linked : Linked(F, u, v)
  shows u ∈ F
proof
  exact (pair.split with linked).left

theorem projectedHave (F u v : Set)
  requires linked : Linked(F, u, v)
  shows v ∈ F
proof
  have h := (pair.split with linked).right
  exact h

theorem projectedForward (F u v : Set)
  requires linked : Linked(F, u, v)
  shows u ∈ F
proof
  exact (pair.iff.forward with linked).left

theorem projectedDirection (F u v : Set)
  requires hu : u ∈ F
  requires hv : v ∈ F
  shows Linked(F, u, v)
proof
  exact (pair.iff at F, u, v).backward with ⟨hu, hv⟩

theorem projectedEntry (F G u v : Set)
  requires linked : Linked(F, u, v)
  requires subset : F ⊆ G
  shows u ∈ G
proof
  exact subset with u, (pair.split with linked).left

theorem projectedObtain (F u v : Set)
  requires linked : Linked(F, u, v)
  shows v ∈ F
proof
  obtain ⟨_, hv⟩ := (pair.split with linked)
  exact hv
`);
});

test("an unannotated have names the conclusion-only parameters left open and takes _ holes", () => {
  assert.match(failure(`
theorem open (F e : Set)
  requires member : e ∈ F
  shows Linked(F, e, e)
proof
  have h := Linked.of_member with member
  exact h
`), /Linked\.of_member: cannot infer parameter G: it occurs only in the conclusion Linked\(G, e, e\), which nothing here fixes; state the fact, `have h : … := Linked\.of_member with member`, or write `Linked\.of_member at G, _, _ with member` with the parameters the premises fix left as _/);
  checks(`
theorem holes (F e : Set)
  requires member : e ∈ F
  shows Linked(F, e, e)
proof
  have h := Linked.of_member at F, _, _ with member
  exact h

theorem holesExact (F e : Set)
  requires member : e ∈ F
  shows Linked(F, e, e)
proof
  exact Linked.of_member at F, _, _ with member
`);
});
