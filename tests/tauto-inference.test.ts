// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Friction met while proving graph theory: `tauto` reads an equation and
// its mirror image as one atom, so a disjunction of equations closes a goal
// stated with the sides the other way round; an unannotated `have h :=
// thm.backward with ⟨a, b⟩` infers the theorem's parameters from the
// components of the anonymous constructor, as it does from named entries,
// so a stray context fact of the right shape cannot pick a wrong instance;
// and `by_cases h :` reads its proposition from the next, more indented
// line, as `have h :` does.

import assert from "node:assert/strict";
import test from "node:test";
import { callMachineMethod } from "../src/index.ts";

interface Diagnostic { readonly line: number; readonly message: string }
interface CheckResult { readonly status: string; readonly diagnostics: readonly Diagnostic[] }

const header = "module TautoInference\nimport Grace.Cumulus.Set.Powerset\n";

function check(source: string): CheckResult {
  return callMachineMethod("check", {
    files: [{ name: "TautoInference.g17", source: header + source }],
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

test("tauto identifies an equation with its mirror image", () => {
  checks(`
theorem mirror (a b : Set)
  requires h : a = b
  shows ¬(b ≠ a)
proof
  tauto

theorem negations (a b : Set)
  requires h : ¬(a = b)
  shows b ≠ a ∧ ¬(b = a)
proof
  tauto
`);
});

test("a disjunction of equations meets a goal stated the other way round", () => {
  checks(`
theorem otherEnd (v l r : Set)
  requires ends : l = v ∨ r = v
  requires notLeft : v ≠ l
  shows r = v
proof
  tauto

theorem eitherEnd (v l r : Set)
  requires ends : l = v ∨ r = v
  shows v = l ∨ v = r
proof
  tauto
`);
});

test("tauto stays a propositional search and reports a counterexample", () => {
  const message = failure(`
theorem transitivity (a b c : Set)
  requires h : a = b
  shows b = c
proof
  tauto
`);
  assert.match(message, /tauto found a counterexample/u);
});

test("an unannotated have infers parameters from an anonymous constructor", () => {
  checks(`
def classOf (P x : Set) : Set := { C ∈ P | x ∈ C }
def crossingClasses (P leftEnd rightEnd F : Set) : Set :=
  { e ∈ F | classOf(P, leftEnd(e)) ≠ classOf(P, rightEnd(e)) }

theorem memberFromComponents (P leftEnd rightEnd F e : Set)
  requires inF : e ∈ F
  requires crosses : classOf(P, leftEnd(e)) ≠ classOf(P, rightEnd(e))
  shows e ∈ crossingClasses(P, leftEnd, rightEnd, F)
proof
  have member := crossingClasses.membership.backward with ⟨inF, crosses⟩
  exact member
`);
});

test("the components choose the instance when context facts of the same shape differ", () => {
  checks(`
def comps (F : Set) : Set := 𝒫(F)

theorem rightInstance (F e X Y : Set)
  requires inOld : X ∈ comps(F)
  requires inNew : X ∈ comps(F ∪ {e})
  requires notY : X ≠ Y
  shows X ∈ comps(F) ∖ {Y}
proof
  have inner := difference.singleton_membership.backward with ⟨inOld, notY⟩
  exact inner
`);
});

test("nested constructors and witnesses drive inference the same way", () => {
  checks(`
theorem packed (A B C x : Set)
  requires h : x ∈ A ∧ (x ∈ B ∧ x ∈ C)
  shows x ∈ C
proof
  exact h.right.right

theorem useNested (A B C D x : Set)
  requires ha : x ∈ A
  requires hb : x ∈ B
  requires hc : x ∈ C
  requires hd : x ∈ D
  shows x ∈ C ∧ x ∈ C
proof
  have first := packed with ⟨ha, ⟨hb, hc⟩⟩
  have second := packed with ⟨ha, hd, hc⟩
  exact ⟨first, second⟩

theorem inhabitedOf (A : Set)
  requires h : ∃ y, y ∈ A
  shows Nonempty(A)
proof
  obtain ⟨y, hy⟩ := h
  exact ⟨y, hy⟩

theorem useWitness (A B x : Set)
  requires hx : x ∈ A
  requires hy : x ∈ B
  shows Nonempty(A)
proof
  have found := inhabitedOf with ⟨x, hx⟩
  exact found
`);
});

test("a constructor whose component fits only through a definition keeps the old report", () => {
  const message = failure(`
def inhabitedSubsets (A : Set) : Set := {S ∈ 𝒫(A) | Nonempty(S)}

theorem viaDefinition (A S : Set)
  requires subset : S ⊆ A
  requires nonempty : Nonempty(S)
  shows S ∈ inhabitedSubsets(A)
proof
  have member := inhabitedSubsets.membership.backward with ⟨subset, nonempty⟩
  exact member
`);
  assert.match(message, /cannot uniquely infer parameters A, S/u);
});

test("by_cases reads its proposition from the next line after the colon", () => {
  checks(`
theorem splitColon (A x : Set)
  shows x ∈ A ∨ ¬(x ∈ A)
proof
  by_cases h :
    x ∈ A
  . left; exact h
  . right; exact h

theorem splitOperator (A B x : Set)
  shows (x ∈ A ∧ x ∈ B) ∨ ¬(x ∈ A ∧ x ∈ B)
proof
  by_cases h : x ∈ A ∧
    x ∈ B
  . left; exact h
  . right; exact h

theorem splitLeadingOperator (A B x : Set)
  shows (x ∈ A ∧ x ∈ B) ∨ ¬(x ∈ A ∧ x ∈ B)
proof
  by_cases h : x ∈ A
    ∧ x ∈ B
  . left; exact h
  . right; exact h
`);
});
