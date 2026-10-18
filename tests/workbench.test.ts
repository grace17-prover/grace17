// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { resolveSymbolCandidate } from "../workbench/editor-utils.js";
import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import {
  checkWorkbenchFiles, checkWorkbenchSource, prepareWorkbenchFiles, runWorkbenchFiles, runWorkbenchFunction, theoremRanges, workbenchFailure,
} from "../src/workbench.ts";

const source = `module WorkbenchTest
namespace WorkbenchTest
import Grace.Core
import Grace.Cumulus.Set
open Grace.Core.Nat.Rec
open Grace.Core.Nat.Algebra
open Grace.Cumulus.Set.Basic.Set
open Grace.Cumulus.Set.Finite.FiniteSet

def square (n : Nat) : Nat := mul(n, n)

theorem square.two
  shows square(2) = 4
proof
  settle with square, mul, add

theorem insert.keeps (x A : Set)
  shows x in insert(x, A)
proof
  settle with insert.membership

end WorkbenchTest
`;

test("set-function application and constructed-function application elaborate to apply", () => {
  const result = checkWorkbenchSource(`module FunctionApplication
namespace FunctionApplication
import Grace.Cumulus.Set.Function

theorem variable_application (f X : Set)
  requires given : f(X) = apply(f, X)
  shows f(X) = apply(f, X)
proof
  exact given

theorem constructed_application (X : Set)
  requires given : identity(∅)(X) = apply(identity(∅), X)
  shows identity(∅)(X) = apply(identity(∅), X)
proof
  exact given

end FunctionApplication
`);
  assert.equal(result.ok, true, result.ok ? "" : result.message);
  assert.equal(result.theorems.length, 2);
  assert.match(result.theorems[0]!.statement, /f\(X\) = f\(X\)/);
});

test("theorem source ranges remain aligned across instance declarations", () => {
  assert.deepEqual(theoremRanges(`theorem first
proof
  rfl

instance chosen
proof
  rfl

lemma final
proof
  rfl`), [
    { lineStart: 1, lineEnd: 4 },
    { lineStart: 5, lineEnd: 8 },
    { lineStart: 9, lineEnd: 11 },
  ]);
  assert.deepEqual(theoremRanges(`theorem first
proof
  rfl

def separator : Set := empty

lemma final
proof
  rfl`), [
    { lineStart: 1, lineEnd: 4 },
    { lineStart: 7, lineEnd: 9 },
  ]);
  assert.deepEqual(theoremRanges(`theorem first
proof
  rfl
defgraph sequence (n : Nat) : Nat := succ(n)
lemma final
proof
  rfl`), [
    { lineStart: 1, lineEnd: 3 },
    { lineStart: 5, lineEnd: 7 },
  ]);
});

test("workbench returns source-level states and kernel drill-down", () => {
  const result = checkWorkbenchSource(source);
  assert.equal(result.ok, true);
  assert.equal(result.theorems.length, 3);
  assert.equal(result.theorems[1]!.steps.length, 1);
  assert.equal(result.theorems[1]!.steps[0]!.after.goals.length, 0);
  assert.ok(result.theorems[1]!.kernel.length > 0);
  assert.ok(result.theorems[1]!.kernel.every(node => node.premiseLabels.length === node.children.length));
  const specialization = result.theorems[1]!.kernel.find(node => node.rule === "forallElim");
  assert.equal(specialization?.ruleCode, "∀E");
  assert.equal(specialization?.ruleName, "Universal specialization");
  assert.equal(specialization?.premiseLabels[0], "universal statement");
  assert.ok(specialization?.arguments.some(argument => argument.name === "term"));
  const generalization = result.theorems[2]!.kernel.find(node => node.rule === "forallIntro");
  assert.match(generalization?.sideConditions[0] ?? "", /∉ FV\(Γ\)/);
});

test("finite set equality has the ergonomic extensionality and simp proof", () => {
  const result = checkWorkbenchSource(`module FiniteLiteralExtensionality
namespace FiniteLiteralExtensionality
import Grace.Cumulus.Set
open Grace.Cumulus.Set.Basic.Set
open Grace.Cumulus.Set.Finite.FiniteSet

lemma duplicate.literal
  shows {1, 1, 2} = {1, 2}
proof
  ext x
  simp

end FiniteLiteralExtensionality
`);
  assert.equal(result.ok, true);
  assert.equal(result.theorems[0]!.statement, "{1, 1, 2} = {1, 2}");
  assert.deepEqual(result.theorems[0]!.steps.map(step => step.command), ["ext x", "simp"]);
  assert.equal(result.theorems[0]!.steps[0]!.after.goals[0]!.goal,
    "x ∈ {1, 1, 2} ↔ x ∈ {1, 2}");
  assert.equal(result.theorems[0]!.steps[1]!.after.goals.length, 0);
});

test("workbench follows the residual goal through a calc chain", () => {
  const result = checkWorkbenchSource(`module CalcWorkbench
namespace CalcWorkbench
theorem chain (a b c : Set)
  requires hab : a = b
  requires hbc : b = c
  shows a = c
proof
  calc
    a = b := hab
    _ = c := hbc

end CalcWorkbench
`);
  assert.equal(result.ok, true);
  assert.deepEqual(result.theorems[0]!.steps.map(step => step.command), [
    "calc", "a = b := hab", "_ = c := hbc",
  ]);
  assert.equal(result.theorems[0]!.steps[1]!.after.goals[0]!.goal, "b = c");
  assert.equal(result.theorems[0]!.steps[2]!.after.goals.length, 0);
});

test("calc composes real ≤, <, and equality steps", () => {
  const result = checkWorkbenchSource(`module MixedRealCalc
namespace MixedRealCalc
import Grace.Cumulus.Real.Ring

theorem chain (a b c d : Real)
  requires hab : a ≤ b
  requires hbc : b < c
  requires hcd : c = d
  shows a < d
proof
  calc
    a ≤ b := hab
    _ < c := hbc
    _ = d := hcd

end MixedRealCalc
`);
  assert.equal(result.ok, true);
  assert.deepEqual(result.theorems[0]!.steps.map(step => step.command), [
    "calc", "a ≤ b := hab", "_ < c := hbc", "_ = d := hcd",
  ]);
  assert.equal(result.theorems[0]!.steps.at(-1)!.after.goals.length, 0);
});

test("workbench returns a structured proof map only for annotated proofs", () => {
  const result = checkWorkbenchSource(`module ProofMapWorkbench
namespace ProofMapWorkbench
theorem both (x : Set)
  shows x = x and x = x
proof
  --! Split the goal
  --| The branches are independent.
  split
  . --! First branch
    rfl
  . --! Second branch
    rfl

end ProofMapWorkbench
`);
  assert.deepEqual(result.theorems[0]!.proofMap.map(entry => [entry.kind, entry.text, entry.indent]), [
    ["heading", "Split the goal", 2],
    ["note", "The branches are independent.", 2],
    ["heading", "First branch", 4],
    ["heading", "Second branch", 4],
  ]);
});

test("workbench invokes native computation from the edited module", () => {
  const result = runWorkbenchFunction(source, "square", [12n]);
  assert.equal(result.value, "144");
  assert.ok(result.stats.reductions > 0);
});

test("workbench reports top-level eval results at their source lines", () => {
  const result = checkWorkbenchSource(`${source}\neval WorkbenchTest.square(9)\n`);
  assert.deepEqual(result.evaluations.map(item => [item.file, item.line, item.expression, item.value]), [
    ["Playground.g17", source.split(/\r?\n/).length + 1, "WorkbenchTest.square(9)", "81"],
  ]);
});

test("workbench evaluates closed set propositions with finite-set literals", () => {
  const result = checkWorkbenchSource(`module SetEvaluationWorkbenchTest
namespace SetEvaluationWorkbenchTest
import Grace.Cumulus.Set
eval 1 in {1, 2}

end SetEvaluationWorkbenchTest
`);
  assert.deepEqual(result.evaluations.map(item => [item.expression, item.value, item.kind]), [
    ["1 in {1, 2}", "true", "proposition"],
  ]);
});

test("workbench computes finite recursive structure containing an infinite set", () => {
  const result = checkWorkbenchSource(`module InfinitePayloadWorkbenchTest
namespace InfinitePayloadWorkbenchTest
import Grace.Core
open Grace.Core.Data.ListOps
eval length{A := powerset(omega)}(Grace.Core.Data.List.cons(1, Grace.Core.Data.List.cons(2, Grace.Core.Data.List.cons(omega, Grace.Core.Data.List.nil))))

end InfinitePayloadWorkbenchTest
`);
  assert.deepEqual(result.evaluations.map(item => [item.value, item.stats.reductions]), [["3", 4]]);
});

test("list notation computes over infinite set-valued payloads", () => {
  const result = checkWorkbenchSource(`module InfiniteListNotationWorkbenchTest
namespace InfiniteListNotationWorkbenchTest
import Grace.Cumulus
import Grace.Core.Data
open Grace.Core.Data.ListOps
open Grace.Cumulus.Set.Basic.Set
open Grace.Cumulus.Set.Hierarchy
open Grace.Cumulus.Set.Ordinal
lemma length.infinite_notation
  shows length([ω, V(ω), 𝒫(V(ω))]) = 3 by compute
eval length([ω, V(ω), 𝒫(V(ω))])

end InfiniteListNotationWorkbenchTest
`);
  assert.equal(result.theorems[0]!.statement, "length([ℕ, V(ℕ), 𝒫(V(ℕ))]) = 3");
  assert.deepEqual(result.evaluations.map(item => item.value), ["3"]);
});

test("workbench returns short display names and navigable symbol metadata", () => {
  const result = checkWorkbenchSource(`module SymbolWorkbenchTest
namespace SymbolWorkbenchTest
import Grace.Cumulus.Set
import Grace.Core.Nat
open Grace.Cumulus.Set.Ordinal
lemma ordinal.zero
  shows empty in Ordinal
proof
  settle with Ordinal.empty

end SymbolWorkbenchTest
`);
  assert.equal(result.theorems[0]!.statement, "∅ ∈ Ordinal");
  const ordinal = result.symbols.find(item => item.name === "Grace.Cumulus.Set.Ordinal.Ordinal");
  assert.equal(ordinal?.short, "Ordinal");
  assert.equal(ordinal?.kind, "class");
  assert.ok(ordinal?.line);
  assert.ok(result.documents.some(item => item.module === "Grace.Cumulus.Set.Ordinal"));
  const natural = result.symbols.find(item => item.name === "Nat");
  assert.equal(natural?.kind, "predicate");
  assert.ok(natural?.line);
  assert.ok(result.documents.some(item => item.file === natural?.file && item.module === "Grace.Core.Nat"));
});

test("goal identifiers include navigable metadata for local library definitions", () => {
  const result = checkWorkbenchFiles([{ name: "Rat/Defs.g17", source: readFileSync(
    new URL("../lib/Grace/Cumulus/Rat/Defs.g17", import.meta.url), "utf8") }], "ZFG", ["Rat/Defs.g17"],
  { includeKernelDetails: false });
  const positiveNaturals = result.symbols.filter(symbol => symbol.short === "positiveNaturals");
  assert.equal(positiveNaturals.length, 1);
  assert.equal(positiveNaturals[0]!.kind, "definition");
  assert.equal(positiveNaturals[0]!.file, "Rat/Defs.g17");
  assert.equal(positiveNaturals[0]!.line, 12);
  assert.match(positiveNaturals[0]!.info, /def positiveNaturals : Set/);
  const representatives = [
    ["definition", "Grace.Cumulus.Rat.Defs.positiveNaturals"],
    ["function", "Grace.Core.Data.Bool.false"],
    ["predicate", "Grace.Core.Data.Bool"],
    ["class", "Grace.Cumulus.Set.Classes.Class.Natural"],
    ["theorem", "Naturals.constructor.zero"],
    ["axiom", "set.infinity.minimal"],
  ] as const;
  for (const [kind, name] of representatives) {
    const symbol = result.symbols.find(item => item.name === name);
    assert.equal(symbol?.kind, kind, `${name} has the expected symbol category`);
    assert.match(symbol?.info ?? "", /\S/, `${name} has hover information`);
    assert.ok(symbol?.file, `${name} has a definition source`);
    assert.ok(symbol?.line, `${name} has a definition line`);
    assert.ok(result.documents.some(document => document.file === symbol?.file), `${name} has an openable source document`);
  }
});

test("foundation primitives, constructors, and axioms have hover information and definition targets", () => {
  const result = checkWorkbenchSource(`module FoundationNavigationWorkbenchTest
namespace FoundationNavigationWorkbenchTest
import Grace.Cumulus.Set.Foundation
open Grace.Cumulus.Set.Foundation
lemma navigation (n : Nat)
  requires hn : n in omega
  shows union(pair(zero, succ(n))) = union(pair(zero, succ(n)))
proof
  rfl

end FoundationNavigationWorkbenchTest
`);
  for (const name of ["omega", "union", "zero", "succ", "set.infinity", "nat.succ"]) {
    const symbol = result.symbols.find(item => item.name === name);
    assert.ok(symbol, `missing ${name} symbol metadata`);
    assert.match(symbol.info, /\S/);
    assert.ok(symbol.line, `missing ${name} definition line`);
    assert.ok(result.documents.some(item => item.file === symbol.file && item.module === "Grace.Kernel.Foundation"));
  }
  assert.match(result.symbols.find(item => item.name === "omega")!.info, /distinguished inductive set/i);
  assert.match(result.symbols.find(item => item.name === "zero")!.info, /empty set/i);
  assert.equal(result.symbols.find(item => item.name === "set.infinity")!.kind, "axiom");
  assert.match(result.symbols.find(item => item.name === "set.infinity")!.info, /ω|omega/);
});

test("imported core notation expands arithmetic operators to add and mul", () => {
  const result = checkWorkbenchSource(`module CoreNotationWorkbenchTest
namespace CoreNotationWorkbenchTest
import Grace.Core
open Grace.Core.Nat.Rec

lemma notation.core
  shows 2 * 3 + 4 = add(mul(2, 3), 4)
proof
  rfl

eval 2 * 3 + 4

end CoreNotationWorkbenchTest
`);
  assert.deepEqual(result.evaluations.map(item => item.value), ["10"]);
  assert.equal(result.theorems[0]!.name, "CoreNotationWorkbenchTest.notation.core");
});

test("workbench reports notation targets for membership and ordered pairs", () => {
  const result = checkWorkbenchSource(`module NotationMetadataWorkbenchTest
namespace NotationMetadataWorkbenchTest
import Grace.Cumulus.Set.Relation
open Grace.Cumulus.Set.Relation

lemma notation.targets (x y A : Set)
  requires hx : x ∈ A
  shows (x, y) = orderedPair(x, y)
proof
  rfl

end NotationMetadataWorkbenchTest
`);
  assert.deepEqual(result.notations.find(item => item.token === "∈"), {
    token: "∈", precedence: 50, associativity: "none", kind: "predicate", reversed: false, target: "in",
  });
  assert.equal(result.notations.find(item => item.token === "↦")?.target, "orderedPair");
  assert.equal(result.notations.find(item => item.token === "𝒫")?.target, "powerset");
  assert.equal(result.theorems[0]!.statement, "∀ x, ∀ y, ∀ A, x ∈ A → (x, y) = (x, y)");
});

test("workbench recovers instance-selected notation in proof states", () => {
  const result = checkWorkbenchSource(`module InstanceNotationDisplayWorkbenchTest
namespace InstanceNotationDisplayWorkbenchTest
import Grace.Cumulus.Rat.Operations

theorem inverse_display (x : Rational)
  shows x + (-x) = 0
proof
  exact rationalAddValue.neg_right at x with assumption

end InstanceNotationDisplayWorkbenchTest
`);
  const theorem = result.theorems[0]!;
  assert.match(theorem.statement, /x \+ \(-x\) = 0/);
  assert.doesNotMatch(theorem.statement, /call[12]\(/);
  assert.match(theorem.initial!.goals[0]!.goal, /x \+ \(-x\) = 0/);
  const rationals = result.symbols.find(item => item.name === "Grace.Cumulus.Rat.Defs.rationals");
  assert.equal(rationals?.kind, "definition");
  assert.ok(rationals?.line);
  assert.match(rationals?.info ?? "", /^def ℚ : Set :=/);
  assert.ok(result.documents.some(item => item.file === rationals?.file));
});

test("real division notation jumps to its defining operation", () => {
  const result = checkWorkbenchSource(`module RealDivisionNotationWorkbenchTest
namespace RealDivisionNotationWorkbenchTest
import Grace.Cumulus.Real.Inverse

theorem division_display (A B : Real)
  shows A / B = A * realInvValue(B)
proof
  exact realDiv.eq_mul_inv at A, B with assumption, assumption

end RealDivisionNotationWorkbenchTest
`);
  const theorem = result.theorems[0]!;
  assert.match(theorem.statement, /A \/ B = A \* realInvValue\(B\)/);
  const notation = result.notations.find(item => item.token === "/");
  assert.equal(notation?.target, "Grace.Cumulus.Real.Inverse.realDiv");
  const division = result.symbols.find(item => item.name === notation?.target);
  assert.equal(division?.kind, "definition");
  assert.match(division?.info ?? "", /^def realDiv : Set := fieldDiv/);
  assert.ok(result.documents.some(item => item.file === division?.file));
});

test("real carrier notation exposes its defining line and navigation target", () => {
  const result = checkWorkbenchFiles([{ name: "Real/Defs.g17", source: readFileSync(
    new URL("../lib/Grace/Cumulus/Real/Defs.g17", import.meta.url), "utf8") }], "ZFG", ["Real/Defs.g17"],
  { includeKernelDetails: false });
  const notation = result.notations.find(item => item.token === "ℝ");
  assert.equal(notation?.target, "Grace.Cumulus.Real.Defs.reals");
  const reals = result.symbols.find(item => item.name === notation?.target);
  assert.equal(reals?.kind, "definition");
  assert.equal(reals?.line, 20);
  assert.match(reals?.info ?? "", /^def ℝ : Set := \{ A ∈ 𝒫\(ℚ\)/);
  assert.ok(result.documents.some(item => item.file === reals?.file));
});

test("workbench exposes remainder notation and its definition target", () => {
  const result = checkWorkbenchSource(`module ModNotationWorkbenchTest
namespace ModNotationWorkbenchTest
import Grace.Cumulus.Nat.Mod

lemma notation.mod_unfold (d : Nat)
  shows 0 % d = 0
proof
  unfold %
  rfl

end ModNotationWorkbenchTest
`);
  const notation = result.notations.find(item => item.token === "%");
  assert.equal(notation?.target, "Grace.Cumulus.Nat.Mod.mod");
  assert.ok(result.symbols.some(item => item.name === notation?.target && item.kind === "definition"));
});

test("workbench preserves intermediate goals when a proof is incomplete", () => {
  const incomplete = `module IncompleteWorkbenchTest
namespace IncompleteWorkbenchTest
theorem pair_goals (x : Set)
  shows x = x and x = x
proof
  constructor
  reflexivity

end IncompleteWorkbenchTest
`;
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchSource(incomplete); }
  catch (error) { failure = workbenchFailure(error); }
  assert.equal(failure?.ok, false);
  assert.match(failure?.message ?? "", /1 goal remains/);
  assert.equal(failure?.trace.steps.length, 2);
  assert.deepEqual(failure?.trace.steps[1]!.after.goals.map(goal => goal.goal), ["x = x"]);
});

test("workbench exposes the initial goal for an empty proof block", () => {
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try {
    checkWorkbenchSource(`module EmptyProofWorkbenchTest
namespace EmptyProofWorkbenchTest
theorem reflexive (x : Set)
  shows x = x
proof

end EmptyProofWorkbenchTest
`);
  } catch (error) { failure = workbenchFailure(error); }
  assert.equal(failure?.message, "empty proof block");
  assert.deepEqual(failure?.trace.initial.goals.map(goal => goal.goal), ["x = x"]);
  assert.deepEqual(failure?.trace.steps, []);
});

test("workbench distinguishes admitted sorry obligations from completed proofs", () => {
  const result = checkWorkbenchSource(`module SorryWorkbenchTest
namespace SorryWorkbenchTest
theorem unfinished (x : Set)
  shows x = x
proof
  sorry

theorem downstream (x : Set)
  shows x = x
proof
  exact unfinished at x

end SorryWorkbenchTest
`);
  assert.equal(result.sorries.length, 1);
  assert.equal(result.sorries[0]!.file, "Playground.g17");
  assert.equal(result.sorries[0]!.theorem, "SorryWorkbenchTest.unfinished");
  assert.equal(result.theorems[0]!.sorries.length, 1);
  assert.equal(result.theorems[1]!.sorries.length, 1);
  assert.equal(result.theorems[1]!.sorries[0]!.axiom, result.sorries[0]!.axiom);
  assert.equal(result.files[0]!.sorries, 1);
  assert.equal(result.files[0]!.admittedSorries, 1);
  assert.ok(result.theorems[0]!.dependencies.axioms.includes(result.sorries[0]!.axiom));
});

test("workbench exposes every constructor goal immediately after induction", () => {
  const pending = `module PendingNatInduction
namespace PendingNatInduction
import Grace.Core
open Grace.Core.Nat.Rec
lemma right (x : Nat)
  shows x + 0 = x
proof
  induction x

end PendingNatInduction
`;
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchSource(pending); }
  catch (error) { failure = workbenchFailure(error); }
  assert.match(failure?.message ?? "", /induction on Nat has 2 constructor cases/);
  assert.deepEqual(failure?.trace.steps[0]?.after.goals.map(goal => goal.goal), [
    "0 + 0 = 0", "succ(tail) + 0 = succ(tail)",
  ]);
  assert.equal(failure?.trace.steps[0]?.after.goals[1]?.locals.some(local => local.name === "ih"), true);
});

test("workbench renders a failed compact induction branch as a residual goal", () => {
  const broken = `module FailedInductionWorkbenchTest
namespace FailedInductionWorkbenchTest
define add (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(add(x, y))

theorem add.always_zero (n : Nat)
  shows add(n, 0) = 0
proof
  induction n
  | zero => settle with add
  | succ(k) using ih => settle with add

end FailedInductionWorkbenchTest
`;
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchSource(broken); }
  catch (error) { failure = workbenchFailure(error); }
  assert.equal(failure?.ok, false);
  assert.equal(failure?.line, 12);
  assert.match(failure?.message ?? "", /^settle did not close this goal/);
  assert.doesNotMatch(failure?.message ?? "", /\{"(?:args|tag)"/);
  assert.equal(failure?.trace.steps.length, 5);
  const failed = failure?.trace.steps.at(-1);
  assert.equal(failed?.command, "settle with add");
  assert.deepEqual(failed?.after.goals.map(goal => goal.goal), ["succ(k) + 0 = 0"]);
  assert.deepEqual(failed?.after, failed?.before);
});

test("workbench preserves the goal when a one-line settle tactic fails", () => {
  const broken = `module FailedDirectWorkbenchTest
namespace FailedDirectWorkbenchTest
theorem impossible (x y : Set)
  shows x = y
proof
  settle

end FailedDirectWorkbenchTest
`;
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchSource(broken); }
  catch (error) { failure = workbenchFailure(error); }
  assert.match(failure?.message ?? "", /^settle did not close this goal/);
  assert.deepEqual(failure?.trace.steps[0]!.after.goals.map(goal => goal.goal), ["x = y"]);
});

test("workbench preserves and prettifies a failed kernel computation goal", () => {
  const broken = `module FailedComputeWorkbenchTest
namespace FailedComputeWorkbenchTest
define add (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(add(x, y))

theorem bad_ground
  shows add(2, 2) = 5
proof
  compute

end FailedComputeWorkbenchTest
`;
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchSource(broken); }
  catch (error) { failure = workbenchFailure(error); }
  assert.match(failure?.message ?? "", /different normal forms: 4 and 5/);
  assert.doesNotMatch(failure?.message ?? "", /\{\"(?:args|tag)\"/);
  assert.deepEqual(failure?.trace.steps[0]!.after.goals.map(goal => goal.goal), ["2 + 2 = 5"]);
});

test("workbench checks mutually visible editor tabs as one import graph", () => {
  const files = [{ name: "Lib.g17", source: `module Workbench.Lib
namespace Workbench.Lib
import Grace.Core.Nat
open Grace.Core.Nat.Rec
def next (n : Nat) : Nat := succ(n)

end Workbench.Lib
` }, { name: "Client.g17", source: `module Workbench.Client
namespace Workbench.Client
import Workbench.Lib
open Workbench.Lib
theorem next.two
  shows next(2) = 3
proof
  settle with next

end Workbench.Client
` }];
  const checked = checkWorkbenchFiles(files);
  assert.deepEqual(checked.theorems.map(theorem => [theorem.file, theorem.lineStart]), [["Lib.g17", 5], ["Client.g17", 5]]);
  assert.equal(runWorkbenchFiles(files, "next", [12n]).value, "13");
});

test("active-file checking ignores unrelated broken tabs while retaining buffer overrides", () => {
  const files = [
    { name: "Broken.g17", source: `module Unrelated.Broken
namespace Unrelated.Broken
theorem malformed
  shows
proof
  rfl

end Unrelated.Broken
` },
    { name: "Active.g17", source: `module ActiveTab
namespace ActiveTab
import Grace.Core
open Grace.Core.Nat.Rec
lemma arithmetic
  shows 2 * 3 + 4 = 10
proof
  settle with add, mul

end ActiveTab
` },
  ];
  assert.throws(() => checkWorkbenchFiles(files));
  const result = checkWorkbenchFiles(files, "ZFG", ["Active.g17"]);
  assert.deepEqual(result.checkedFiles, ["Active.g17"]);
  assert.deepEqual(result.theorems.map(theorem => [theorem.file, theorem.lineStart]), [["Active.g17", 5]]);
  assert.equal(runWorkbenchFiles(files, "factorial", [5n], "ZFG", ["Active.g17"]).value, "120");
});

test("active-file checking still reports a broken open-buffer dependency", () => {
  const files = [
    { name: "Dependency.g17", source: `module Active.Dependency
namespace Active.Dependency
theorem malformed
  shows
proof
  rfl

end Active.Dependency
` },
    { name: "Client.g17", source: `module Active.Client
namespace Active.Client
import Active.Dependency

end Active.Client
` },
  ];
  let failure: ReturnType<typeof workbenchFailure> | undefined;
  try { checkWorkbenchFiles(files, "ZFG", ["Client.g17"]); }
  catch (error) { failure = workbenchFailure(error); }
  assert.equal(failure?.file, "Dependency.g17");
});

test("incremental dependency checkpoints are invalidated by exact source changes", () => {
  const client = { name: "CacheClient.g17", source: `module Cache.Client
namespace Cache.Client
import Cache.Dependency
open Cache.Dependency
lemma use
  shows value = value
proof
  rfl

end Cache.Client
` };
  const valid = { name: "CacheDependency.g17", source: `module Cache.Dependency
namespace Cache.Dependency
def value : Set := empty

end Cache.Dependency
` };
  assert.equal(checkWorkbenchFiles([valid, client], "ZFG", [client.name]).ok, true);
  const broken = { ...valid, source: `module Cache.Dependency
namespace Cache.Dependency
def value : Set :=

end Cache.Dependency
` };
  assert.throws(() => checkWorkbenchFiles([broken, client], "ZFG", [client.name]));
});

test("checked leaf and declaration caches reject changed active proofs", () => {
  const valid = { name: "LeafCache.g17", source: `module Leaf.Cache
namespace Leaf.Cache
import Grace.Core
theorem first (x : Set)
  shows x = x
proof
  rfl
theorem second (x : Set)
  shows x = x
proof
  rfl

end Leaf.Cache
` };
  assert.equal(checkWorkbenchFiles([valid], "ZFG", [valid.name]).ok, true);
  assert.equal(checkWorkbenchFiles([valid], "ZFG", [valid.name]).ok, true);
  const broken = { ...valid, source: valid.source.replace(
    "theorem second (x : Set)\n  shows x = x",
    "theorem second (x : Set)\n  shows x = empty",
  ) };
  assert.throws(() => checkWorkbenchFiles([broken], "ZFG", [broken.name]));
});

test("workbench prechecks dependencies and materializes kernel detail only on demand", () => {
  const file = { name: "Prepared.g17", source: `module Prepared
namespace Prepared
import Grace.Core
theorem reflexive (x : Set)
  shows x = x
proof
  rfl

end Prepared
` };
  const prepared = prepareWorkbenchFiles([file], "ZFG", file.name);
  assert.equal(prepared.ok, true);
  assert.ok(prepared.modules > 0);
  const summary = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
  assert.match(summary.digest!, /^[0-9a-f]{64}$/);
  const live = checkWorkbenchFiles([file], "ZFG", [file.name], {
    includeKernelDetails: false, includeEnvironmentDigest: false,
  });
  assert.equal(live.digest, undefined);
  assert.deepEqual(live.theorems, summary.theorems, "omitting an unused digest must retain every goal state");
  assert.equal(summary.theorems[0]!.proofNodes, 0);
  assert.deepEqual(summary.theorems[0]!.kernel, []);
  const detailed = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: true });
  assert.ok(detailed.theorems[0]!.proofNodes > 0);
  assert.ok(detailed.theorems[0]!.kernel.length > 0);
});

test("an opened core source overrides rather than duplicates an imported core module", () => {
  const nat = readFileSync(fileURLToPath(new URL("../lib/Grace/Core/Nat.g17", import.meta.url)), "utf8");
  const result = runWorkbenchFiles([
    { name: "Playground.g17", source: "module Playground\nimport Grace.Core\n" },
    { name: "Nat.g17", source: nat },
  ], "factorial", [5n]);
  assert.equal(result.value, "120");
});

test("with star keeps declaration boundaries across cached and edited dependencies", () => {
  const library = { name: "BoundaryLibrary.g17", source: `module Boundary.Library
namespace Boundary.Library
theorem preserve (n : Nat)
  requires apart : n ≠ zero
  shows n ≠ zero
proof
  exact apart

end Boundary.Library
` };
  const client = { name: "BoundaryClient.g17", source: `module Boundary.Client
namespace Boundary.Client
import Boundary.Library
theorem use (n : Nat)
  requires apart : n ≠ zero
  shows n ≠ zero
proof
  exact Boundary.Library.preserve at n with *

end Boundary.Client
` };
  assert.equal(checkWorkbenchFiles([library, client], "ZFG", [client.name]).ok, true);
  assert.equal(checkWorkbenchFiles([library, client], "ZFG", [client.name]).ok, true);
  // The kernel statement is unchanged, but the declared application boundary moves.
  const edited = { ...library, source: library.source.replace(
    "requires apart : n ≠ zero\n  shows n ≠ zero\nproof\n  exact apart",
    "shows n ≠ zero → n ≠ zero\nproof\n  intro apart\n  exact apart",
  ) };
  assert.throws(() => checkWorkbenchFiles([edited, client], "ZFG", [client.name]));
  const adjusted = { ...client, source: client.source.replace(
    "shows n ≠ zero", "shows n ≠ zero → n ≠ zero") };
  assert.equal(checkWorkbenchFiles([edited, adjusted], "ZFG", [client.name]).ok, true);
  assert.equal(checkWorkbenchFiles([library, client], "ZFG", [client.name]).ok, true);
});


test("Reachability hovers expose both directions of nat.omega and navigate to its theorem", () => {
  const source = readFileSync(new URL("../lib/Grace/Cumulus/GraphTheory/Reachability.g17", import.meta.url), "utf8");
  const result = checkWorkbenchFiles([{ name: "GraphTheory/Reachability.g17", source }]);
  assert.equal(result.ok, true);
  assert.ok(source.includes("nat.omega.forward with oneNat"));
  const base = result.symbols.find(item => item.name === "nat.omega");
  assert.ok(base?.file && base.line);
  for (const direction of ["forward", "backward"]) {
    const symbol = resolveSymbolCandidate(result.symbols, `nat.omega.${direction}`);
    assert.equal(symbol?.kind, "derived proof");
    assert.equal(symbol?.file, base.file);
    assert.equal(symbol?.line, base.line);
    assert.equal(symbol?.info, `${direction === "forward" ? "Forward" : "Backward"} direction of nat.omega\n${base.directions?.[direction]}`);
    assert.match(symbol?.info ?? "", /n : ℕ|Nat\(n\)/);
    assert.doesNotMatch(symbol?.info ?? "", /↔/);
  }
  assert.notEqual(base.directions?.forward, base.directions?.backward);
  assert.equal(resolveSymbolCandidate(result.symbols, "nat.zero.forward"), undefined);
});

test("theorems carry the names their sections and headers bind", () => {
  const source = `module Scoped
namespace Scoped
import Grace.Cumulus.Set.Core
section Pairs
variable (A : Set)
hypothesis nonempty : A ≠ ∅
theorem keep (B : Set)
  requires sub : A ⊆ B
  shows A ⊆ B
proof
  have again : A ⊆ B := sub
  exact again
end Pairs
end Scoped
`;
  const result = checkWorkbenchFiles([{ name: "Scoped.g17", source }], "ZF", ["Scoped.g17"]);
  assert.ok(result.ok);
  const theorem = result.theorems.find(item => item.name === "Scoped.keep")!;
  assert.deepEqual(theorem.scope, [
    { name: "A", kind: "section variable", line: 5, sort: "Set" },
    { name: "nonempty", kind: "section hypothesis", line: 6 },
    { name: "B", kind: "binder", line: 7, sort: "Set" },
    { name: "sub", kind: "premise", line: 8 },
  ]);
  assert.deepEqual(theorem.initial!.goals[0]!.locals.map(local => local.name), ["nonempty", "sub"]);
  assert.ok(theorem.steps[0]!.after.goals[0]!.locals.some(local => local.name === "again"));
});
