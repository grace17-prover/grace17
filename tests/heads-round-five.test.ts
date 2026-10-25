// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Heads and constructors, round five: a parenthesised or bare application
// is the subject of `rcases`, `cases`, and `obtain`, and the head of a
// further application; a nested constructor with entries after it fills
// the first conjunct, a final `_` leaves a whole conjunction, a nested
// `rfl` substitutes into the facts its pattern binds before and after it,
// and a predicate met inside a constructor opens through its definition;
// a local ∀ fact with arguments is a rewrite rule; `rw … at` takes a
// projection, and a rule that matches only under a binder is applied
// there.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[] }

const header = `module HeadsRoundFive
import Grace.Cumulus.Set.Powerset

predicate Linked (F u v : Set) := u ∈ F ∧ v ∈ F
predicate Apart (A B : Set) := A ∩ B = ∅
def classes (A : Set) : Set := A ∪ A
def tagged (S : Set) : Set := { p ∈ S | p ⊆ S ∧ p ≠ ∅ }
def related (f : Set) : Set := { p ∈ f | ∃ x ∈ f, p = x }
predicate Guarded (A B : Set) := A ⊆ B ∧ B ⊆ A
predicate Wrapped (A : Set) := ∃ B, Guarded(A, B)
predicate Level (n : Nat) := n ∈ n ∧ n ⊆ n

theorem three.cases (x a b c : Set)
  requires h : x ∈ {a, b, c}
  shows x = a ∨ x = b ∨ x = c
proof
  sorry

theorem pair.split (F u v : Set)
  requires linked : Linked(F, u, v)
  shows u ∈ F ∧ v ∈ F
proof
  sorry

theorem Apart.iff (A B : Set)
  shows Apart(A, B) ↔ ∀ x, x ∈ A → x ∈ B → ⊥
proof
  sorry
`;

function check(source: string): CheckResult {
  return callMachineMethod("check", {
    files: [{ name: "HeadsRoundFive.g17", source: header + source }],
  }) as CheckResult;
}

function checks(source: string): void {
  const result = check(source);
  assert.equal(result.status, "checked",
    result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
}

test("a parenthesised or bare application is the subject of rcases and cases", () => {
  checks(`
theorem rcasesParenthesised (x a b c : Set)
  requires h : x ∈ {a, b, c}
  requires ha : a ∈ a
  requires hb : b ∈ b
  requires hc : c ∈ c
  shows x ∈ x
proof
  rcases (three.cases with h) with rfl | rfl | rfl
  . exact ha
  . exact hb
  . exact hc

theorem rcasesBare (x a b c : Set)
  requires h : x ∈ {a, b, c}
  requires ha : a ∈ a
  requires hb : b ∈ b
  requires hc : c ∈ c
  shows x ∈ x
proof
  rcases three.cases with h with rfl | rfl | rfl
  . exact ha
  . exact hb
  . exact hc

theorem casesParenthesised (x a b : Set)
  requires h : x ∈ {a, b, b}
  requires ha : a ∈ a
  requires hb : b ∈ b
  shows x ∈ x
proof
  cases (three.cases with h) with first | rest
  . rw first
    exact ha
  . rcases rest with rfl | rfl
    . exact hb
    . exact hb

theorem rcasesTuple (F u v : Set)
  requires linked : Linked(F, u, v)
  shows v ∈ F
proof
  rcases (pair.split with linked) with ⟨_, hv⟩
  exact hv
`);
});

test("a parenthesised application is the head of a further application", () => {
  checks(`
theorem headApplied (A B x : Set)
  requires apart : Apart(A, B)
  requires hA : x ∈ A
  requires hB : x ∈ B
  shows ⊥
proof
  exact (Apart.iff.forward with apart) with x, hA, hB

theorem headAppliedHave (A B x : Set)
  requires apart : Apart(A, B)
  requires hA : x ∈ A
  requires hB : x ∈ B
  shows ⊥
proof
  have h := (Apart.iff.forward with apart) with x, hA, hB
  exact h
`);
});

test("a nested constructor with entries after it fills the first conjunct", () => {
  checks(`
theorem witnessApplication (A X : Set)
  requires member : X ∈ A
  shows ∃ C, (∃ Y, Y ∈ A ∧ C = classes(Y)) ∧ X ∈ A
proof
  exact ⟨classes(X), ⟨X, member, rfl⟩, member⟩

theorem witnessVariable (A X : Set)
  requires member : X ∈ A
  shows ∃ C, (∃ Y, Y ∈ A ∧ C = Y) ∧ X ∈ A
proof
  exact ⟨X, ⟨X, member, rfl⟩, member⟩
`);
});

test("a final _ leaves a whole conjunction, into a set-builder included", () => {
  checks(`
theorem builderConjunction (S p : Set)
  requires hp : p ∈ S
  requires rest : p ⊆ S ∧ p ≠ ∅
  shows p ∈ tagged(S)
proof
  refine ⟨hp, _⟩
  exact rest

theorem lastInequality (A x y : Set)
  requires hx : x ∈ A
  requires e : x ≠ y
  shows ∃ z, z ∈ A ∧ z ≠ y
proof
  refine ⟨x, hx, _⟩
  exact e
`);
});

test("a nested rfl substitutes into the facts bound after it", () => {
  checks(`
theorem siblingSubstitution (A f X : Set)
  requires hX : ((∃ w, w ∈ A ∧ X = classes(w)) ∧ X ∉ f) ∧ X ≠ ∅
  shows ∃ w, w ∈ A ∧ classes(w) ∉ f ∧ classes(w) ≠ ∅
proof
  obtain ⟨⟨⟨w, hw, rfl⟩, notLeft⟩, notRight⟩ := hX
  exact ⟨w, hw, notLeft, notRight⟩
`);
});

test("a constructor opens as many predicate layers as its shape demands", () => {
  checks(`
theorem guardedLayer (n : Set)
  requires nat : Nat(n)
  requires h1 : n ∈ n
  requires h2 : n ⊆ n
  shows Level(n)
proof
  exact ⟨h1, h2⟩

theorem predicateThenBuilder (f x : Set)
  requires hx : x ∈ f
  shows x ∈ related(f)
proof
  refine ⟨hx, x, hx, _⟩
  rfl

theorem twoLayers (A : Set)
  requires h : A ⊆ A
  shows Wrapped(A)
proof
  exact ⟨A, h, h⟩
`);
});

test("rw takes a projection after at, a local ∀ fact with arguments, and a rule under a binder", () => {
  checks(`
theorem atProjection (A B C : Set)
  requires same : A = B
  requires obstruction : C ⊆ C ∧ (C ⊆ C ∧ A ∈ C)
  shows B ∈ C
proof
  rw same at obstruction.right.right
  exact obstruction.right.right

theorem localForallRule (A V f g : Set)
  requires h : ∀ v ∈ V, f(v) = g(v)
  requires hv : A ∈ V
  requires target : g(A) ∈ V
  shows f(A) ∈ V
proof
  rw h with A, hv
  exact target

theorem underFallback (A B V : Set)
  requires same : A = B
  requires h : ∀ v ∈ V, v ∈ classes(B)
  shows ∀ v ∈ V, v ∈ classes(A)
proof
  rw same
  exact h

theorem underFallbackAt (A B V : Set)
  requires same : A = B
  requires h : ∀ v ∈ V, v ∈ classes(A)
  shows ∀ v ∈ V, v ∈ classes(B)
proof
  rw same at h
  exact h
`);
});

test("a keyword entry is evidence for a predicate conjunct and opens no definition", () => {
  const result = callMachineMethod("check", {
    files: [{ name: "Keyword.g17", source: `module Keyword
import Grace.Cumulus.Set.Basic

predicate Marked (A : Set) := A ⊆ A ∧ A = A

predicate Framed (A B : Set) := Marked(A) ∧ B = B ∧ A = A

theorem framed (A B : Set)
  requires marked : Marked(A)
  shows Framed(A, B)
proof
  unfold Framed
  exact ⟨assumption, rfl, rfl⟩
` }],
  }) as { status: string; diagnostics: readonly { line: number; message: string }[] };
  assert.equal(result.status, "checked", result.diagnostics.map(item => `${item.line}: ${item.message}`).join("\n"));
});
