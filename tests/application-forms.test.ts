// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

function load(name: string, source: string): void {
  loadModuleSourceGraph(createZfKernel(), [{ file: `${name}.g17`, source: `module ${name}\n${source}` }], ["lib"]);
}

function failure(name: string, source: string): string {
  try {
    load(name, source);
  } catch (error) {
    return error instanceof Error ? error.message : String(error);
  }
  throw new Error(`${name} was expected to fail`);
}

test("a named premise that fits several requirements is read each way until the parameters are fixed", () => {
  load("Shift", `
section Shift
variable (I i : Set)
hypothesis index : i ∈ I

theorem shift.function (m : Set)
  requires member : m ∈ pair(I, I)
  shows m ∈ pair(I, I)
proof
  exact member

theorem shift.same (m : Set)
  requires member : m ∈ pair(I, I)
  shows m ∈ pair(I, I)
proof
  have function := shift.function with member
  exact function

end Shift
`);
});

test("a partial at list fills the leading parameters and the facts fix the rest", () => {
  load("Partial", `
section S
variable (K J : Set)
hypothesis base : K ∈ J

theorem ext (B f g : Set)
  requires first : f ∈ B
  requires second : g ∈ B
  requires agree : f = g
  shows f = g
proof
  exact agree

theorem written (B f g : Set)
  requires first : f ∈ B
  requires second : g ∈ B
  requires agree : f = g
  shows f = g
proof
  exact ext at K, J, B with first, second, agree

theorem sectionOnly (B f g : Set)
  requires first : f ∈ B
  requires second : g ∈ B
  requires agree : f = g
  shows f = g
proof
  exact ext at K, J with base, first, second, agree

theorem unannotated (B f g : Set)
  requires first : f ∈ B
  requires second : g ∈ B
  requires agree : f = g
  shows f = g
proof
  have h := ext at K, J, B with first, second, agree
  exact h

end S
`);
});

test("a named fact proving a premise already discharged is accepted as redundant evidence", () => {
  const source = (entry: string): string => `
import Grace.Core.Nat

theorem nat.copy (n : Nat)
  shows n = n
proof
  rfl

theorem use (m : Set)
  requires hm : Nat(m)
  requires other : m = m
  shows m = m
proof
  exact nat.copy at m with ${entry}
`;
  load("Redundant", source("hm"));
  assert.match(failure("Stray", source("other")), /no remaining argument at other/u);
});

test("an existential fact fills its conjunct in any constructor position", () => {
  load("Existential", `
theorem leading (A : Set)
  requires fibre : ∃ e, e ∈ A
  requires value : A = A
  requires third : A ∈ A
  shows (∃ e, e ∈ A) ∧ A = A ∧ A ∈ A
proof
  exact ⟨fibre, value, third⟩

theorem afterWitness (A S : Set)
  requires inS : A ∈ S
  requires fibre : ∃ e, e ∈ A
  requires value : A = A
  shows ∃ F ∈ S, (∃ e, e ∈ F) ∧ F = A
proof
  witness A
  exact ⟨inS, fibre, value⟩

theorem witnessTerm (A x : Set)
  requires inA : x ∈ A
  requires value : A = A
  shows (∃ e, e ∈ A) ∧ A = A
proof
  exact ⟨x, inA, value⟩
`);
});

test("exact with rfl discharges the reflexive premise of a fact", () => {
  load("Reflexive", `
theorem direct (a : Set)
  requires h : a = a → a ∈ a
  shows a ∈ a
proof
  exact h with rfl

theorem apart (a b : Set)
  requires apart : a ≠ b
  requires same : a = b
  shows ⊥
proof
  rw same at apart
  exact apart with rfl
`);
});

test("rw list entries with their own at and with lists are parenthesized, and the message says so", () => {
  const rules = `
theorem swap (x y : Set)
  requires h : x = y
  shows x = y
proof
  exact h

theorem pairwise (A B C D Z : Set)
  requires h : A = B
  requires k : C = D
  requires hBZ : B ∈ Z
  requires hDZ : D ∈ Z
  shows A ∈ Z ∧ C ∈ Z
proof
  rw LIST
  exact ⟨hBZ, hDZ⟩
`;
  load("Parenthesized", rules.replace("LIST", "[(swap at A, B with h), (swap at C, D with k)]"));
  const message = failure("Split", rules.replace("LIST", "[swap at A, B with h, swap at C, D with k]"));
  assert.match(message, /A is a variable, not a local fact; in a rw list, an entry applied with its own at or with list is parenthesized/u);
});

test("a rewrite with no instance left is reported as nothing left to rewrite", () => {
  const message = failure("Exhausted", `
def ident (x : Set) : Set := x

theorem ident.value (Z x : Set)
  requires hx : x ∈ Z
  shows ident(x) = x
proof
  unfold ident
  rfl

theorem twice (A B Z : Set)
  requires hA : A ∈ Z
  requires hB : B ∈ Z
  shows ident(A) ∈ Z ∧ ident(B) ∈ Z
proof
  rw ident.value with *
  rw ident.value with *
  exact ⟨hA, hB⟩
`);
  assert.match(message, /ident\.value: nothing left to rewrite: no instance of the rule's left side ident\(x\) occurs in the goal/u);
});

test("a guard's typing colon ends a line, a mixfix literal begins one, and binder groups wrap", () => {
  load("Wrapped", `
import Grace.Cumulus.Set.Function
notation mixfix "_ : _ →+* _" => FunctionBetween

theorem guard (R S f : Set)
  requires hom : f : R →+* S
  shows f : R →+* S
proof
  have h : f :
    R →+* S
    exact hom
  have k : f : R
    →+* S
    exact hom
  exact k

theorem binders (a : Set) (q : Set)
  (m : Set)
  requires h : a ∈ q
  shows a ∈ q
proof
  exact h
`);
});

test("closed arithmetic on literals is folded in an instantiated statement", () => {
  load("Folded", `
import Grace.Core.Nat

def g (p n : Set) : Set := p

theorem g.succ (p : Set) (n : Nat)
  shows g(p, n + 1) = p
proof
  unfold g
  rfl

theorem stated (A Z : Set)
  requires hA : A ∈ Z
  shows g(A, 2) ∈ Z
proof
  have h := g.succ at A, 1
  rw h
  exact hA

theorem rewritten (A Z : Set)
  requires hA : A ∈ Z
  shows g(A, 2) ∈ Z
proof
  rw g.succ at A, 1
  exact hA

theorem written (A Z : Set)
  requires hA : A ∈ Z
  shows g(A, 1 + 1) ∈ Z
proof
  rw g.succ at A, 1
  exact hA

theorem closed (A : Set)
  shows g(A, 2) = A
proof
  exact g.succ at A, 1

theorem closedWritten (A : Set)
  shows g(A, 1 + 1) = A
proof
  exact g.succ at A, 1

theorem numeralRule (A : Set)
  requires two : 1 + 1 = 2
  shows g(A, 2) = A
proof
  have h := g.succ at A, 1
  rw two at h
  exact h
`);
});

test("a have := whose text is a statement proved by a tactic is told the statement form", () => {
  const message = failure("HaveHint", `
theorem flip (x y : Set)
  requires h : x = y
  shows y = x
proof
  have g := y = x by cc
  exact g
`);
  assert.match(message, /line 7: `have g := …` takes a proof reference; a statement proved by a tactic is written `have g : y = x by cc`/);
});
