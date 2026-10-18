// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import {
  SurfaceError, setSurfaceTraceCapture, app, canonical, createZfgKernel, elaborateModule, eq, exportTheorem, forkSurfaceEnvironment, formulaEquals, formatFormula, instanceReport, loadModuleSourceGraph, moduleReport, tacticReport, termEquals, v, verifyExportedProof,
} from "../src/index.ts";

const source = readFileSync(fileURLToPath(new URL("../examples/Arithmetic.g17", import.meta.url)), "utf8");
const setSource = readFileSync(fileURLToPath(new URL("../examples/Sets.g17", import.meta.url)), "utf8");
const unicodeSource = readFileSync(fileURLToPath(new URL("../examples/Unicode.g17", import.meta.url)), "utf8");

test("parses, elaborates, and kernel-checks the first .g17 module", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, source);
  assert.deepEqual(result.definitions, ["plus", "times"]);
  assert.deepEqual(result.theorems, ["plus.type", "plus.left_unit", "plus.right_unit", "plus.succ_right", "plus.associative", "plus.commutative", "plus.swap", "times.type", "times.right_zero", "times.succ_right", "times.commutative", "times.distributes_right", "times.ground_700", "times.ground_bigint"]);
  assert.deepEqual(result.evaluations.map(item => [item.expression, item.value]), [
    ["7000000000 * 1000000000", "7000000000000000000"],
  ]);
  for (const name of result.theorems) assert.ok(kernel.theorems.has(name));
  assert.deepEqual(kernel.theoremTacticTraces.get("plus.commutative")?.steps.map(step => step.command), [
    "induction n",
    "| zero =>",
    "settle with plus, plus.right_unit",
    "| succ(k) using ih =>",
    "settle with plus, plus.succ_right, ih",
  ]);
  const numeral = (value: number) => {
    let result = app("zero");
    for (let index = 0; index < value; index += 1) result = app("succ", result);
    return result;
  };
  const evaluated = kernel.evaluateCertified(app("times", numeral(6), numeral(7)), 100_000);
  assert.equal(canonical(evaluated.value), canonical(numeral(42)));
  kernel.checkProof(evaluated.proof);
});

test("checks logical formulas and set membership through equivalence rules", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, setSource);
  assert.deepEqual(result.theorems, [
    "pair.left", "pair.right", "equality.or_example", "equality.and_example", "equality.exists_self",
    "membership.identity",
    "epsilon0.less.unfold",
  ]);
  for (const name of result.theorems) assert.ok(kernel.theorems.has(name));
});

test("elaborates readable stepwise tactic proofs", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem implication.manual (x y : Set)
  shows x = y -> x = y
proof
  intro h
  exact h

theorem conjunction.manual (x : Set)
  shows x = x and x = x
proof
  constructor
  rfl
  reflexivity

theorem existence.manual (x : Set)
  shows exists y, y = x
proof
  witness x
  rfl

theorem universal.manual (x : Set)
  shows forall z, z = z
proof
  intro z
  rfl
`);
  assert.deepEqual(result.theorems, ["implication.manual", "conjunction.manual", "existence.manual", "universal.manual"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("carrier premises of an at-list application are discharged on their own", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem typed.identity (n : Nat)
  shows Nat(n) -> Nat(n)
proof
  intro h
  exact h

theorem typed.specialized (n : Nat)
  shows Nat(n)
proof
  have h := typed.identity at n
  exact h
`);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("have introduces a checked local proposition from an indented proof", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem local_have (x : Set)
  shows x = x ∧ x = x
proof
  have diagonal : x = x
    rfl
  constructor
  . exact diagonal
  . exact diagonal

theorem nested_local_have (x : Set)
  shows x = x
proof
  have outer : x = x
    have inner : x = x
      rfl
    exact inner
  exact outer
`);
  assert.deepEqual(result.theorems, ["local_have", "nested_local_have"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
  const steps = kernel.theoremTacticTraces.get("local_have")!.steps;
  assert.deepEqual(steps.map(step => step.command), [
    "have diagonal : x = x", "rfl", "constructor", "exact diagonal", "exact diagonal",
  ]);
  assert.equal(steps[0]!.after.goals[0]!.goal.tag, "eq");
  assert.equal(steps[1]!.after.goals[0]!.locals.some(local => local.name === "diagonal"), true);
});

test("have diagnoses missing and unfinished local proof blocks", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
theorem missing_local_have (x : Set)
  shows x = x
proof
  have diagonal : x = x
  exact diagonal
`), (error: unknown) => error instanceof SurfaceError &&
    /local proof diagonal needs an indented tactic body/.test(error.message));

  assert.throws(() => elaborateModule(kernel, `
theorem unfinished_local_have (x y : Set)
  shows x = x
proof
  have impossible : x = y
    by_contra
  rfl
`), (error: unknown) => error instanceof SurfaceError &&
    /local proof impossible is incomplete; next is/.test(error.message));
});

test("tactics accept indented multiline rule lists", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
theorem multiline.settle (x y : Set)
  shows x in pair(x, y)
proof
  settle with pair.membership,
    set.pairing

theorem multiline.simp (x : Set)
  shows x = x
proof
  simp [
    pair.membership,
    set.pairing
  ]

theorem multiline.pair_left (x y : Set)
  shows x in pair(x, y)
proof
  settle with pair.membership

theorem multiline.term (x y : Set)
  shows x in pair(x, y)
proof
  apply multiline.pair_left at
    x, y
`);
  for (const name of ["multiline.settle", "multiline.simp", "multiline.term"]) {
    kernel.checkProof(kernel.theoremProofs.get(name)!);
  }
  assert.equal(kernel.theoremTacticTraces.get("multiline.settle")?.steps[0]?.command,
    "settle with pair.membership, set.pairing");
  assert.equal(kernel.theoremTacticTraces.get("multiline.simp")?.steps[0]?.command,
    "simp [ pair.membership, set.pairing ]");
});

test("local propositions wrap after Unicode conjunction and disjunction", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
theorem multiline.local_connectives (x y : Set)
  shows (x = x ∧ y = y) ∧ (x = x ∨ y = y)
proof
  have both : x = x ∧
      y = y
    constructor
    . rfl
    . rfl
  have either : x = x ∨
      y = y
    left
    rfl
  refine ⟨both, either⟩
`);
  assert.ok(kernel.theorems.has("multiline.local_connectives"));
  verifyExportedProof(kernel, exportTheorem(kernel, "multiline.local_connectives"));
  assert.throws(() => elaborateModule(createZfgKernel(), `
theorem multiline.bad_local (x y : Set)
  shows x = x
proof
  have both : x = x ∧
  y = y
    constructor
    . rfl
    . rfl
  rfl
`), SurfaceError);
});

test("predicates, classes, and explicit definitions accept multiline bodies", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
def diagonal (x y : Set) : Set :=
  pair(
    x,
    y
  )

predicate Related (x y : Set) :=
  x in pair(x, y)
  and
  y in pair(x, y)

class ReflexivePair (x : Set) := {
  x : Set |
  x in pair(x, x)
}

theorem multiline.declarations (x y : Set)
  shows Related(x, y)
proof
  settle with Related, pair.membership
`);
  assert.deepEqual(result.definitions, ["diagonal", "Related", "ReflexivePair"]);
  assert.deepEqual(result.theorems, ["multiline.declarations"]);
  kernel.checkProof(kernel.theoremProofs.get("multiline.declarations")!);
  assert.equal(kernel.definitions.has("diagonal"), true);
  assert.equal(kernel.definitions.has("Related"), true);
  assert.equal(kernel.definitions.has("ReflexivePair"), true);
});

test("theorem requirements and conclusions accept layout-aware multiline formulas", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
lemma multiline.clauses (a b c : Set)
  requires
    h1 : a = b
  requires h2 :
    b = c
    ∧
    c = c
  shows
    a = b
    ∧
    c = c
proof
  rcases h2 with ⟨hbc, hcc⟩
  constructor
  . exact h1
  . exact hcc
`);
  assert.deepEqual(result.theorems, ["multiline.clauses"]);
  kernel.checkProof(kernel.theoremProofs.get("multiline.clauses")!);
  assert.match(formatFormula(kernel.theorems.get("multiline.clauses")!), /a = b.*b = c.*∧.*c = c.*→.*a = b.*∧.*c = c/);
});

test("multiline theorem clauses reject empty and outdented bodies", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
lemma empty_requirement (a : Set)
  requires
  shows a = a
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError &&
    /requires needs an indented proposition/.test(error.message));

  assert.throws(() => elaborateModule(kernel, `
lemma outdented_conclusion (a : Set)
  shows
a = a
proof
  rfl
`), (error: unknown) => error instanceof SurfaceError &&
    /shows continuation must be indented beneath line/.test(error.message));
});

test("soft-typed predicate binders contribute recoverable domain guards", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
predicate PrimeLike (p : Nat) :=
  1 in p

theorem PrimeLike.natural (p : Set)
  requires hp : PrimeLike(p)
  shows Nat(p)
proof
  settle with PrimeLike
`);
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get("PrimeLike.natural")!));
  assert.match(formatFormula(kernel.definitions.get("PrimeLike")!.properties.get("equation")!),
    /Nat\(p\).*∧/);
});

test("recursive equation bodies accept multiline terms", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
datatype Bit
  | off
  | on

def flip (bit : Bit) -> Bit
  | Bit.off =>
    Bit.on
  | Bit.on =>
    Bit.off

noncomputable foundation def historyPair (x : Set) : Set
  | x using history =>
    pair(
      history,
      history
    )

theorem flip.twice (bit : Bit)
  shows flip(flip(bit)) = bit
proof
  induction bit
  | Bit.off => settle with flip
  | Bit.on => settle with flip
`);
  assert.ok(result.definitions.includes("flip"));
  assert.ok(result.definitions.includes("historyPair"));
  kernel.checkProof(kernel.theoremProofs.get("flip.twice")!);
});

test("legacy define remains a compatibility alias for equation-style def", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
datatype Switch
  | down
  | up
define toggle (value : Switch) -> Switch
  | Switch.down => Switch.up
  | Switch.up => Switch.down
`);
  assert.equal(kernel.definitions.has("toggle"), true);
});

test("runs arbitrary multi-step tactic scripts inside induction cases", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
datatype Bool
  | false
  | true

define negate (b : Bool) -> Bool
  | Bool.false => Bool.true
  | Bool.true => Bool.false

lemma negate.involutive (b : Bool)
  shows negate(negate(b)) = b
proof
  induction b
  | Bool.false =>
    unfold negate
    rfl
  | Bool.true => simp [negate]
`);
  assert.deepEqual(result.theorems, ["negate.type", "negate.involutive"]);
  kernel.checkProof(kernel.theoremProofs.get("negate.involutive")!);
  assert.deepEqual(kernel.theoremTacticTraces.get("negate.involutive")?.steps.map(step => step.command), [
    "induction b", "| Bool.false =>", "unfold negate", "rfl", "| Bool.true =>", "simp [negate]",
  ]);
});

test("structural induction generalizes later binders and dependent requirements", () => {
  const base = createZfgKernel();
  elaborateModule(base, "");
  const kernel = base.fork();
  forkSurfaceEnvironment(base, kernel);
  const source = `
datatype Peano
  | zero
  | succ(pred : self)

theorem generalized (s : Set, n : Peano, t : Set)
  requires self : s = s
  shows s = s ∧ t = t
proof
  induction n generalizing s with
  | Peano.zero =>
    intro s
    intro self
    constructor
    . exact self
    . rfl
  | Peano.succ(k) using ih =>
    intro s
    intro self
    constructor
    . exact self
    . rfl
`;
  const result = elaborateModule(kernel, source);
  assert.deepEqual(result.theorems, ["generalized"]);
  kernel.checkProof(kernel.theoremProofs.get("generalized")!);
  const inductionStep = kernel.theoremTacticTraces.get("generalized")?.steps[0];
  assert.equal(inductionStep?.command, "induction n generalizing s with");
  assert.match(formatFormula(inductionStep!.after.goals[0]!.goal), /∀ s/);
  assert.ok(kernel.theorems.has("generalized.generalized_induction_aux"));
  // A sibling fork shares the declaration cache, but has neither theorem.
  // Restore the generated dependency before checking the cached public proof.
  const warm = base.fork();
  forkSurfaceEnvironment(base, warm);
  assert.ok(!warm.theorems.has("generalized.generalized_induction_aux"));
  elaborateModule(warm, source);
  assert.ok(warm.theorems.has("generalized.generalized_induction_aux"));
  assert.equal(warm.theoremProofs.get("generalized"), kernel.theoremProofs.get("generalized"));
  assert.doesNotThrow(() => verifyExportedProof(warm, exportTheorem(warm, "generalized")));
});

test("generalizing diagnoses unknown and induction variables", () => {
  const source = `
datatype Peano
  | zero
  | succ(pred : self)
theorem generalized (n : Peano, s t : Set)
  shows s = s
proof
  induction n GENERALIZATION
`;
  assert.throws(() => elaborateModule(createZfgKernel(), source.replace("GENERALIZATION", "generalizing missing")),
    /unknown generalized variable missing/);
  assert.throws(() => elaborateModule(createZfgKernel(), source.replace("GENERALIZATION", "generalizing n")),
    /cannot generalize the induction variable n/);
});

test("retains typed constructor goals for an induction awaiting its cases", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `module PendingInduction
namespace PendingInduction
datatype Choice
  | no
  | yes
theorem self (x : Choice)
  shows x = x
proof
  induction x

end PendingInduction
`), (error: unknown) => {
    assert.ok(error instanceof SurfaceError);
    assert.match(error.message, /induction on Choice has 2 constructor cases/);
    assert.match(error.message, /Choice\.no/);
    assert.deepEqual(error.partialTrace?.steps[0]?.after.goals.map(item => formatFormula(item.goal)), [
      "no = no", "yes = yes",
    ]);
    return true;
  });
});

test("supports semicolon tactic sequences and dot subgoal markers", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module CompactTactics
namespace CompactTactics
theorem both (x : Set)
  shows x = x and x = x
proof
  split; . rfl; . rfl

end CompactTactics
`);
  const trace = kernel.theoremTacticTraces.get("CompactTactics.both")!;
  assert.deepEqual(trace.steps.map(step => step.command), ["split", "rfl", "rfl"]);
  assert.ok(trace.steps[0]!.columnStart! < trace.steps[1]!.columnStart!);
  assert.ok(trace.steps[1]!.columnStart! < trace.steps[2]!.columnStart!);
});

test("retains inert proof narrative metadata alongside checked tactic states", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module Narrative
namespace Narrative
theorem both (x : Set)
  shows x = x and x = x
proof
  --! Split the conjunction.
  --| Each branch is reflexive.
  split
  . --! Left branch
    rfl
  . --! Right branch
    rfl

end Narrative
`);
  const trace = kernel.theoremTacticTraces.get("Narrative.both")!;
  assert.deepEqual(trace.narrative, [
    { line: 6, indent: 2, kind: "heading", text: "Split the conjunction." },
    { line: 7, indent: 2, kind: "note", text: "Each branch is reflexive." },
    { line: 9, indent: 4, kind: "heading", text: "Left branch" },
    { line: 11, indent: 4, kind: "heading", text: "Right branch" },
  ]);
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get("Narrative.both")!));
  const exported = exportTheorem(kernel, "Narrative.both");
  assert.equal(exported.tactics?.narrative?.[2]?.text, "Left branch");
  assert.doesNotThrow(() => verifyExportedProof(kernel, exported));
});

test("exact? spells the premises it discharged, specializing a quantified local fact, and ranks that above a typing detour", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Search2.g17", source: `module Search2
import Grace.Cumulus.Set.Function

theorem image_in (f X A B k : Set)
  requires fFunction : f : A → B
  requires inA : ∀ k ∈ A, X(k) ∈ A
  requires hk : k ∈ A
  shows f(X(k)) ∈ B
proof
  exact?
` }], ["lib"]);
  const trace = kernel.theoremTacticTraces.get("Search2.image_in")!;
  const items = trace.steps[0]!.info!.items as string[];
  assert.equal(items[0], "exact FunctionBetween.apply_closed at f, A, B, Xₖ with fFunction, (inA at k with hk)");
  assert.ok(items.every(item => !item.endsWith("with *")), items.join("; "));
  // The spelled suggestion checks when written out, _root_ names included.
  const kernel2 = createZfgKernel();
  loadModuleSourceGraph(kernel2, [{ file: "Search2.g17", source: `module Search2
import Grace.Cumulus.Set.Function

theorem image_in (f X A B k : Set)
  requires fFunction : f : A → B
  requires inA : ∀ k ∈ A, X(k) ∈ A
  requires hk : k ∈ A
  shows f(X(k)) ∈ B
proof
  ${items[0]}

theorem rooted (f A B x : Set)
  requires fFunction : f : A → B
  requires hx : x ∈ A
  shows f(x) ∈ B
proof
  exact _root_.Grace.Cumulus.Set.Function.FunctionBetween.apply_closed with fFunction, hx
` }], ["lib"]);
  assert.ok(kernel2.theorems.has("Search2.image_in") && kernel2.theorems.has("Search2.rooted"));
});

test("proof-search tactics return checked exact, apply, and rewrite suggestions", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module SearchTactics
namespace SearchTactics
theorem helper (x y : Set)
  requires h : x = y
  shows x = y
proof
  exact h

theorem found.exact (x : Set)
  requires h : x = x
  shows x = x
proof
  exact?

theorem found.apply (x y : Set)
  requires h : x = y
  shows x = y
proof
  apply?
  exact h

theorem found.rewrite (x y : Set)
  requires h : x = y
  shows pair(x, x) = pair(y, y)
proof
  rw?
  rfl

end SearchTactics
`);
  for (const name of ["SearchTactics.found.exact", "SearchTactics.found.apply", "SearchTactics.found.rewrite"]) {
    assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get(name)!));
    const trace = kernel.theoremTacticTraces.get(name)!;
    assert.ok(trace.steps[0]!.info?.items.length);
  }
});

test("apply? searches generated definition properties and their directions", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module DefinitionSearch
namespace DefinitionSearch
predicate Marked (x : Set) := x = x

theorem found (x : Set)
  requires hx : x = x
  shows Marked(x)
proof
  apply?
  exact hx

end DefinitionSearch
`);
  const trace = kernel.theoremTacticTraces.get("DefinitionSearch.found")!;
  assert.match(trace.steps[0]!.info?.items[0] ?? "", /Marked\.equation\.backward/);
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get("DefinitionSearch.found")!));
});

test("sorry admits a named tracked obligation without disguising it as a proof", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module SorryTracking
namespace SorryTracking
theorem unfinished (x y : Set)
  requires h : x = y
  shows y = x
proof
  sorry

end SorryTracking
`);
  assert.equal(result.sorries.length, 1);
  const admitted = result.sorries[0]!;
  assert.equal(admitted.theorem, "SorryTracking.unfinished");
  assert.equal(admitted.line, 7);
  assert.match(admitted.axiom, /^sorry\.SorryTracking\.unfinished\.7\.1$/);
  assert.ok(kernel.axioms.has(admitted.axiom));
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get(admitted.theorem)!));
  assert.ok(exportTheorem(kernel, admitted.theorem).dependencies.axioms.includes(admitted.axiom));
});

test("simp computes ground terms and rewrite transforms goals in either direction", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
define add (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(add(x, y))

lemma simp.ground
  shows add(7, 100) = 107
proof
  simp [add]

lemma rewrite.local (x y : Set)
  requires h : x = y
  shows y = x
proof
  rewrite ← h
  rfl

lemma rewrite.definition (n : Nat)
  shows add(0, n) = n
proof
  rw add
  rfl

lemma unfold.compact_numeral
  shows 2 = union(pair(1, pair(1, 1)))
proof
  unfold nat.succ
  rfl
`);
  assert.deepEqual(result.theorems, ["add.type", "simp.ground", "rewrite.local", "rewrite.definition", "unfold.compact_numeral"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("simp may simplify a logical goal incrementally without closing it", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module IncrementalSimp
namespace IncrementalSimp
predicate QuotientMember (C A r : Set) := C ∈ A ∧ ∃ x, x ∈ A ∧ C = x
predicate QuotientSubset (A r : Set) := ∀ C, QuotientMember(C, A, r) → C ∈ A

theorem quotient.subset_powerset (A r : Set)
  shows QuotientSubset(A, r)
proof
  simp with QuotientSubset
  simp with QuotientMember

end IncrementalSimp
`);
  assert.deepEqual(result.theorems, ["IncrementalSimp.quotient.subset_powerset"]);
  assert.deepEqual(kernel.theoremTacticTraces.get(result.theorems[0]!)?.steps.map(step => step.command), [
    "simp with QuotientSubset", "simp with QuotientMember",
  ]);
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get(result.theorems[0]!)!));
});

test("calc chains checked equalities and exposes each residual endpoint", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module CalcTactic
namespace CalcTactic
theorem equality_chain (a b c : Set)
  requires hab : a = b
  requires hbc : b = c
  shows a = c
proof
  calc
    a = b := hab
    _ = c := hbc

theorem inline_step (a b : Set)
  shows pair(a, b) = pair(a, b)
proof
  calc
    _ = pair(a, b) := by rfl

end CalcTactic
`);
  assert.deepEqual(result.theorems, ["CalcTactic.equality_chain", "CalcTactic.inline_step"]);
  const trace = kernel.theoremTacticTraces.get("CalcTactic.equality_chain");
  const firstStep = trace?.steps.find(step => step.command === "a = b := hab");
  assert.ok(firstStep);
  assert.equal(firstStep.after.goals.length, 1);
  assert.deepEqual(firstStep.after.goals[0]!.goal, eq(v("b"), v("c")));
  assert.equal(trace?.steps.find(step => step.command === "_ = c := hbc")?.after.goals.length, 0);
});

test("calc diagnoses broken endpoints and unsupported relations", () => {
  assert.throws(() => elaborateModule(createZfgKernel(), `
module BadCalcEndpoint
namespace BadCalcEndpoint
theorem broken (a b c : Set)
  requires hab : a = b
  shows a = c
proof
  calc
    a = b := hab

end BadCalcEndpoint
`), /calc chain ends at b, but the goal ends at c/);
  assert.throws(() => elaborateModule(createZfgKernel(), `
module BadCalcRelation
namespace BadCalcRelation
predicate P (x : Set) := x = x
theorem broken (a : Set)
  shows P(a)
proof
  calc
    _ = a := by rfl

end BadCalcRelation
`), /calc needs an equality or registered binary relation goal/);
});

test("calc remains stable across a long authored chain", () => {
  const kernel = createZfgKernel();
  const length = 256;
  const chain = Array.from({ length }, () => "    _ = x := by rfl").join("\n");
  elaborateModule(kernel, `
module CalcScaling
namespace CalcScaling
theorem long_chain (x : Set)
  shows x = x
proof
  calc
${chain}

end CalcScaling
`);
  const trace = kernel.theoremTacticTraces.get("CalcScaling.long_chain");
  assert.equal(trace?.steps.length, length + 1);
  assert.ok(kernel.theorems.has("CalcScaling.long_chain"));
});

test("unfold accepts an infix notation token as a definition reference", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module NotationUnfold
namespace NotationUnfold
def left (x y : Set) : Set := x
notation infixl 70 "%" => left

lemma left.unfold (x y : Set)
  shows x % y = x
proof
  unfold %
  rfl

end NotationUnfold
`);
  assert.deepEqual(result.theorems, ["NotationUnfold.left.unfold"]);
  assert.doesNotThrow(() => kernel.checkProof(kernel.theoremProofs.get(result.theorems[0]!)!));
});

test("tactic transformations can target named hypotheses", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
predicate Subset (A B : Set) := forall x, x in A -> x in B

lemma Subset.transitive (A B C : Set)
  requires hAB : Subset(A, B)
  requires hBC : Subset(B, C)
  shows Subset(A, C)
proof
  unfold Subset
  unfold Subset at hAB
  unfold Subset at hBC
  intro a
  intro a at hAB
  intro a at hBC
  intro ha
  apply hBC
  apply hAB
  exact ha

lemma rewrite.hypothesis (x y : Set)
  requires hxy : x = y
  requires h : x = x
  shows y = y
proof
  rw hxy at h
  exact h

lemma simp.proposition (x a b : Set)
  requires h : x in pair(a, b)
  shows x = a or x = b
proof
  simp [pair.membership] at h
  exact h
`);
  assert.deepEqual(result.theorems, ["Subset.transitive", "rewrite.hypothesis", "simp.proposition"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("set literals resolve constructors in the active scope", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module ScopedLiterals
namespace ScopedLiterals
namespace Finite
def singleton (x : Set) : Set := pair(x, x)
def union2 (A B : Set) : Set := union(pair(A, B))
theorem singleton.self (x : Set)
  shows x in singleton(x)
proof
  settle with singleton, pair.membership
theorem union2.left (x A B : Set)
  requires hx : x in A
  shows x in union2(A, B)
proof
  settle with union2, set.union, pair.membership
theorem literal.membership
  shows 1 in {1, 2, 3}
proof
  have h1 := singleton.self at 1
  have h2 := union2.left at 1, singleton(1), pair(2, 3)
  apply h2
  exact h1
end Finite

end ScopedLiterals
`);
  assert.ok(result.theorems.includes("ScopedLiterals.Finite.literal.membership"));
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("a finite set literal can be the complete right-hand side of a definition", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module LiteralDefinition
namespace LiteralDefinition
namespace Finite
def singleton (x : Set) : Set := pair(x, x)
def union2 (A B : Set) : Set := union(pair(A, B))
def unit (x : Set) : Set := {x}
def endpoints (x y : Set) : Set := {x, y}
lemma unit.raw (x : Set)
  shows unit(x) = singleton(x)
proof
  unfold unit
  rfl
lemma endpoints.raw (x y : Set)
  shows endpoints(x, y) = pair(x, y)
proof
  unfold endpoints
  rfl
end Finite

end LiteralDefinition
`);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("empty sets, singletons, and unordered pairs print as ordinary mathematics", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module MathematicalSetNotation
namespace MathematicalSetNotation
lemma notation (x y : Set)
  shows pair(empty, singleton(x)) = {∅, {x}}
proof
  rfl

end MathematicalSetNotation
`);
  const statement = kernel.theorems.get("MathematicalSetNotation.notation")!;
  assert.equal(formatFormula(statement), "∀ x, ∀ y, {∅, {x}} = {∅, {x}}");
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("mathematical notation and raw kernel names elaborate interchangeably", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module NotationRoundTrip
namespace NotationRoundTrip
def singleton (x : Set) : Set := pair(x, x)
def orderedPair (x y : Set) : Set := pair(singleton(x), pair(x, y))
notation infixr 72 "↦" => orderedPair

lemma membership.raw_to_notation (x y : Set)
  requires h : x in singleton(y)
  shows x ∈ {y}
proof
  exact h

lemma membership.notation_to_raw (x y : Set)
  requires h : x ∈ {y}
  shows x in singleton(y)
proof
  exact h

lemma negation.raw_to_notation (x y : Set)
  requires h : not x = y
  shows x ≠ y
proof
  exact h

lemma negation.notation_to_raw (x y : Set)
  requires h : ¬x = y
  shows not x = y
proof
  exact h

lemma maplet.round_trip (x y : Set)
  shows (x ↦ y) = orderedPair(x, y)
proof
  rfl

lemma tuple.round_trip (x y : Set)
  shows (x, y) = orderedPair(x, y)
proof
  rfl

lemma tuple.nested (a b c d : Set)
  shows ((a, b), (c, d)) = orderedPair(orderedPair(a, b), orderedPair(c, d))
proof
  rfl

end NotationRoundTrip
`);
  assert.deepEqual(result.theorems, [
    "NotationRoundTrip.membership.raw_to_notation", "NotationRoundTrip.membership.notation_to_raw",
    "NotationRoundTrip.negation.raw_to_notation", "NotationRoundTrip.negation.notation_to_raw",
    "NotationRoundTrip.maplet.round_trip", "NotationRoundTrip.tuple.round_trip",
    "NotationRoundTrip.tuple.nested",
  ]);
  assert.equal(formatFormula(kernel.theorems.get("NotationRoundTrip.negation.raw_to_notation")!),
    "∀ x, ∀ y, x ≠ y → x ≠ y");
  assert.equal(formatFormula(kernel.theorems.get("NotationRoundTrip.maplet.round_trip")!),
    "∀ x, ∀ y, (x, y) = (x, y)");
  assert.equal(formatFormula(kernel.theorems.get("NotationRoundTrip.tuple.nested")!),
    "∀ a, ∀ b, ∀ c, ∀ d, ((a, b), (c, d)) = ((a, b), (c, d))");
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("two-index matrix entries elaborate to application at an ordered pair", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module MatrixEntryNotation
namespace MatrixEntryNotation
def orderedPair (i j : Set) : Set := pair(i, j)
def apply (f x : Set) : Set := pair(f, x)

theorem entry (M i j : Set)
  shows M[i, j] = M[(i, j)]
proof
  rfl

end MatrixEntryNotation
`);
  const statement = kernel.theorems.get("MatrixEntryNotation.entry")!;
  // The application at a pair prints as the two-argument form, the
  // spelling of call2, and as M((i, j)) when printed for reading back.
  assert.equal(formatFormula(statement), "∀ M, ∀ i, ∀ j, M(i, j) = M(i, j)");
  assert.equal(formatFormula(statement, { reparse: true }), "∀ M, ∀ i, ∀ j, M((i, j)) = M((i, j))");
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("big union and equivalence classes elaborate to their raw constructors", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module StructuredNotationRoundTrip
namespace StructuredNotationRoundTrip
def equivalenceClass (A r x : Set) : Set := pair(A, pair(r, x))

lemma union.round_trip (A : Set)
  shows ⋃ A = union(A)
proof
  rfl

lemma class.round_trip (A r x : Set)
  shows ⟦x⟧[A, r] = equivalenceClass(A, r, x)
proof
  rfl

end StructuredNotationRoundTrip
`);
  assert.equal(formatFormula(kernel.theorems.get("StructuredNotationRoundTrip.union.round_trip")!),
    "∀ A, ⋃ A = ⋃ A");
  assert.equal(formatFormula(kernel.theorems.get("StructuredNotationRoundTrip.class.round_trip")!),
    "∀ A, ∀ r, ∀ x, ⟦x⟧[A, r] = ⟦x⟧[A, r]");
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("number carriers and subset relations have transparent mathematical aliases", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module CarrierNotationRoundTrip
namespace CarrierNotationRoundTrip
predicate Subset (A B : Set) := ∀ x, x ∈ A -> x ∈ B
notation infix 50 "⊆" => Subset
def ℤ : Set := empty
def ℚ : Set := ℤ
def ℝ : Set := ℚ

lemma naturals.alias
  shows ℕ = omega
proof
  rfl

lemma integers.alias
  shows ℤ = integers
proof
  rfl

lemma rationals.alias
  shows ℚ = rationals
proof
  rfl

lemma reals.alias
  shows ℝ = reals
proof
  rfl

lemma subset.alias (A B : Set)
  shows (A ⊆ B) ↔ Subset(A, B)
proof
  settle with Subset

end CarrierNotationRoundTrip
`);
  assert.deepEqual(result.definitions, ["CarrierNotationRoundTrip.Subset", "CarrierNotationRoundTrip.integers", "CarrierNotationRoundTrip.rationals", "CarrierNotationRoundTrip.reals"]);
  assert.equal(formatFormula(kernel.theorems.get("CarrierNotationRoundTrip.reals.alias")!), "ℝ = ℝ");
  assert.equal(formatFormula(kernel.theorems.get("CarrierNotationRoundTrip.subset.alias")!),
    "∀ A, ∀ B, A ⊆ B ↔ A ⊆ B");
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("offers familiar natural-deduction tactics with explicit structural control", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem logic.and_commute (x y : Set)
  requires h : x = x and y = y
  shows y = y and x = x
proof
  rcases h with ⟨hx, hy⟩
  split
  exact hy
  exact hx

theorem logic.or_commute (x y : Set)
  requires h : x = x or y = y
  shows y = y or x = x
proof
  cases h with hx | hy
  right
  exact hx
  left
  exact hy

theorem logic.iff_reflexive (x : Set)
  shows x = x <-> x = x
proof
  split
  intro h
  exact h
  intro h
  exact h

theorem logic.explosion (x y : Set)
  requires absurd : false
  shows x = y
proof
  exfalso
  exact absurd

theorem logic.weakening (x y : Set)
  requires used : x = x
  requires unused : y = y
  shows x = x
proof
  clear unused
  exact used

theorem logic.revert (x : Set)
  requires h : x = x
  shows x = x
proof
  revert h
  intro h2
  exact h2

theorem logic.contradiction (x y : Set)
  requires p : x = x
  requires np : not x = x
  shows x = y
proof
  contradiction

theorem logic.classical (x : Set)
  requires p : x = x
  shows x = x
proof
  by_contra np
  contradiction

theorem logic.many_introductions
  shows forall x, x = x -> forall y, y = y -> x = x and y = y
proof
  intros x, hx y hy
  constructor
  exact hx
  exact hy
`);
  assert.equal(result.theorems.length, 9);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("obtain and rcases recursively destructure existentials and conjunctions", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem logic.deep_obtain (x : Set)
  requires packed : exists a, a = x and exists b, b = a and (x = x and b = b)
  shows x = x
proof
  obtain ⟨a, ha, b, hb, hx, _⟩ := packed
  exact hx

theorem logic.deep_rcases (x : Set)
  requires packed : x = x and (x = x and x = x)
  shows x = x
proof
  rcases packed with ⟨first, second, third⟩
  exact second
`);
  assert.deepEqual(result.theorems, ["logic.deep_obtain", "logic.deep_rcases"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("obtain equality patterns substitute discovered representations", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem logic.substitute_coordinate (q : Set)
  requires packed : ∃ x, q = x ∧ x = x
  shows q = q
proof
  obtain ⟨x, rfl, diagonal⟩ := packed
  exact diagonal
`);
  assert.deepEqual(result.theorems, ["logic.substitute_coordinate"]);
  kernel.checkProof(kernel.theoremProofs.get("logic.substitute_coordinate")!);
});

test("cases and rcases flatten right-associated disjunctions", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem logic.three_cases (x y z : Set)
  requires choice : x = x ∨ y = y ∨ z = z
  shows z = z ∨ y = y ∨ x = x
proof
  rcases choice with hx | hy | hz
  . right
    right
    exact hx
  . right
    left
    exact hy
  . left
    exact hz
`);
  kernel.checkProof(kernel.theoremProofs.get("logic.three_cases")!);
});

test("typecheck and proof applications reconstruct soft-type evidence", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem typed.accepts (n : Nat)
  requires diagonal : n = n
  shows n = n
proof
  exact diagonal

theorem typed.inferred (n : Nat)
  requires diagonal : n = n
  shows n = n
proof
  exact typed.accepts at n with diagonal

theorem typed.checked (n : Nat)
  shows Nat(n)
proof
  typecheck

theorem typed.wildcard (n : Nat)
  requires diagonal : n = n
  shows n = n
proof
  exact typed.accepts at n with *
`);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("simpa closes a goal from a simplified checked fact", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
predicate Same (x y : Set) := x = y

theorem logic.simpa (x y : Set)
  requires h : Same(x, y)
  shows x = y
proof
  simpa [Same] using h
`);
  kernel.checkProof(kernel.theoremProofs.get("logic.simpa")!);
});

test("refine recursively constructs existentials and conjunctions", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
predicate Packed (x : Set) := exists a, a = x and x = x

theorem logic.deep_refine (x y : Set)
  requires hy : y = y
  shows exists a, a = x and exists b, b = y and x = x
proof
  refine ⟨x, rfl, y, hy, _⟩
  rfl

theorem logic.closed_refine (x : Set)
  requires hx : x = x
  shows exists a, a = x and x = x
proof
  refine ⟨x, hx, hx⟩

theorem logic.transparent_refine (x : Set)
  requires hx : x = x
  shows Packed(x)
proof
  refine ⟨x, hx, hx⟩

theorem logic.transparent_rcases (x : Set)
  requires packed : Packed(x)
  shows x = x
proof
  rcases packed with ⟨a, ha, hx⟩
  exact hx
`);
  assert.deepEqual(result.theorems, ["logic.deep_refine", "logic.closed_refine", "logic.transparent_refine", "logic.transparent_rcases"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("intros diagnoses an overlong introduction list at the first unmatched name", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
theorem logic.too_many
  shows forall x, x = x
proof
  intros x extra
  rfl
`), (error: unknown) => error instanceof SurfaceError &&
    /before it could introduce extra/.test(error.message));
});

test("proof expressions consume universal arguments and premises with with", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem logic.applied (x y : Set)
  requires fact : forall z, z = z -> x = x
  requires hy : y = y
  shows x = x
proof
  exact fact
    with y, hy
`);
  assert.deepEqual(result.theorems, ["logic.applied"]);
  kernel.checkProof(kernel.theoremProofs.get("logic.applied")!);
  assert.equal(kernel.theoremTacticTraces.get("logic.applied")?.steps[0]?.command,
    "exact fact with y, hy");
});

test("expands checked userland tactic macros with parameters and bounded recursion", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
tactic finish := assumption
tactic solve(rule) := settle with $rule

theorem tactic.identity (x : Set)
  requires h : x = x
  shows x = x
proof
  finish

theorem tactic.compute (x y : Set)
  shows x in pair(x, y)
proof
  solve(pair.membership)
`);
  assert.deepEqual(result.theorems, ["tactic.identity", "tactic.compute"]);
  assert.deepEqual(tacticReport(kernel).map(item => [item.name, item.parameters]), [
    ["finish", []], ["solve", ["rule"]],
  ]);
  assert.deepEqual(kernel.theoremTacticTraces.get("tactic.identity")?.steps.map(item => item.command), ["finish"]);
});

test("accepts lemma declarations and evaluates closed top-level expressions", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
define add (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(add(x, y))

lemma add.two_three
  shows add(2, 3) = 5
proof
  settle with add

eval add(12, 5)
`);
  assert.deepEqual(result.theorems, ["add.type", "add.two_three"]);
  assert.equal(kernel.theorems.has("add.two_three"), true);
  assert.deepEqual(result.evaluations.map(item => [item.line, item.expression, item.value]), [
    [11, "add(12, 5)", "17"],
  ]);
  assert.ok(result.evaluations[0]!.stats.reductions > 0);
});

test("infers brace-bound implicit arguments without changing kernel arity", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
datatype Parcel(A : Set)
  | empty
  | wrap(value : A)

def tag {A : Set} (p : Parcel(A)) : Set := p

lemma tag.identity {A : Set} (p : Parcel(A))
  shows tag(p) = p
proof
  settle with tag

lemma parcel.reflexive {A : Set} (p : Parcel(A))
  shows p = p
proof
  rfl

lemma parcel.use {A : Set} (p : Parcel(A))
  shows p = p
proof
  have h := parcel.reflexive at p
  exact h

eval tag{A := omega}(Parcel.empty)
eval tag{omega}(Parcel.empty)
`);
  assert.equal(kernel.functions.get("tag"), 2);
  assert.equal(formatFormula(kernel.theorems.get("tag.identity")!),
    "∀ A, ∀ p, Parcel(A, p) → tag(A, p) = p");
  assert.deepEqual(result.evaluations.map(item => item.value), ["empty", "empty"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("diagnoses genuinely ambiguous implicit arguments with an explicit escape hatch", () => {
  assert.throws(() => elaborateModule(createZfgKernel(), `
datatype Parcel(A : Set)
  | empty
def tag {A : Set} (p : Parcel(A)) : Set := p
eval tag(Parcel.empty)
`), /cannot infer implicit argument A for tag; use tag\{A := \.\.\.\}\(\.\.\.\)/);
});

test("desugars arithmetic notation with multiplication precedence and left associativity", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
define plus (x y : Nat) -> Nat
  | zero, y => y
  | succ(x), y => succ(plus(x, y))

notation infixl 60 "+" => plus

define times (x y : Nat) -> Nat
  | zero, y => zero
  | succ(x), y => y + times(x, y)

notation infixl 70 "*" => times
notation infixr 50 "⊕" => plus
notation infixl 80 "++" => times

lemma notation.precedence
  shows 2 * 3 + 4 = plus(times(2, 3), 4)
proof
  rfl

lemma notation.left_associative
  shows 2 + 3 + 4 = plus(plus(2, 3), 4)
proof
  rfl

lemma notation.parentheses
  shows (2 + 3) * 4 = times(plus(2, 3), 4)
proof
  rfl

lemma notation.custom_right_associative
  shows 1 ⊕ 2 ⊕ 3 = plus(1, plus(2, 3))
proof
  rfl

lemma notation.longest_token
  shows 2++3 = times(2, 3)
proof
  rfl

eval 2 * 3 + 4
eval (2 + 3) * 4
`);
  assert.deepEqual(result.theorems, ["plus.type", "times.type", "notation.precedence", "notation.left_associative", "notation.parentheses", "notation.custom_right_associative", "notation.longest_token"]);
  assert.deepEqual(result.evaluations.map(item => [item.expression, item.value]), [
    ["2 * 3 + 4", "10"],
    ["(2 + 3) * 4", "20"],
  ]);
});

test("typed prefix notation resolves overloads and respects precedence", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module PrefixNotation
namespace PrefixNotation
predicate Whole (x : Set) := x = x
predicate Fraction (x : Set) := x = x
def wholeNeg (x : Whole) : Whole := x
def fractionNeg (x : Fraction) : Fraction := x
def wholeMul (x y : Whole) : Whole := x
notation prefix 75 "-" => wholeNeg for Whole
notation prefix 75 "-" => fractionNeg for Fraction
notation infixl 70 "*" => wholeMul for Whole

lemma prefix.whole (x y : Whole)
  shows -x * y = wholeMul(wholeNeg(x), y)
proof
  rfl

lemma prefix.fraction (x : Fraction)
  shows -x = fractionNeg(x)
proof
  rfl

lemma prefix.iterated (x : Whole)
  shows -(-x) = wholeNeg(wholeNeg(x))
proof
  rfl

end PrefixNotation
`);
  assert.deepEqual(result.theorems, ["PrefixNotation.wholeNeg.type", "PrefixNotation.fractionNeg.type", "PrefixNotation.wholeMul.type", "PrefixNotation.prefix.whole", "PrefixNotation.prefix.fraction", "PrefixNotation.prefix.iterated"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("typed infix notation supports heterogeneous operand types", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module HeterogeneousNotation
namespace HeterogeneousNotation
predicate Whole (x : Set) := x = x
def wholePow (x : Whole, n : Nat) : Whole := x
def natPow (x n : Nat) : Nat := x
notation infixr 80 "^" => wholePow for Whole, Nat
notation infixr 80 "^" => natPow for Nat

lemma power.whole (x : Whole)
  shows x ^ 2 = wholePow(x, 2)
proof
  rfl

lemma power.natural
  shows 2 ^ 3 = natPow(2, 3)
proof
  rfl

end HeterogeneousNotation
`);
  assert.deepEqual(result.theorems, ["HeterogeneousNotation.wholePow.type", "HeterogeneousNotation.natPow.type", "HeterogeneousNotation.power.whole", "HeterogeneousNotation.power.natural"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("notation obtains operations and constants from output-producing instances", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module InstanceNotation
namespace InstanceNotation
class Fruit (x : Set) := x = x
predicate HasAdd (carrier operation : Set) := carrier = carrier
predicate OfNat (carrier numeral value : Set) := carrier = carrier
def fruitCarrier : Set := empty
def fruitAdd : Set := pair(empty, empty)
def fruitZero : Set := empty
def call2 (operation left right : Set) : Set := operation
instance fruit_add
  shows HasAdd(fruitCarrier, fruitAdd)
proof
  unfold HasAdd
  rfl
instance fruit_zero
  shows OfNat(fruitCarrier, 0, fruitZero)
proof
  unfold OfNat
  rfl
notation infixl 60 "+" => call2 via HasAdd(fruitCarrier, _) for Fruit
notation numeral "0" via OfNat(fruitCarrier, 0, _) for Fruit

theorem names_are_irrelevant (banana : Fruit)
  shows banana + 0 = fruitAdd
proof
  unfold call2
  rfl

end InstanceNotation
`);
  assert.deepEqual(result.theorems, [
    "InstanceNotation.fruit_add", "InstanceNotation.fruit_zero",
    "InstanceNotation.names_are_irrelevant",
  ]);
});

test("product bounds type numerals in function graph maplets", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module ContextualMapletNotation
namespace ContextualMapletNotation
def singleton (x : Set) : Set := pair(x, x)
def union2 (A B : Set) : Set := union(pair(A, B))
def orderedPair (x y : Set) : Set := pair(singleton(x), pair(x, y))
def product (A B : Set) : Set := powerset(union2(A, B))
notation infixr 72 "↦" => orderedPair
notation infixr 70 "×" => product
def fruitCarrier : Set := empty
class Fruit (x : Set) := x ∈ fruitCarrier
predicate OfNat (carrier numeral value : Set) := carrier = carrier
def fruitZero : Set := empty
instance fruit_zero
  shows OfNat(fruitCarrier, 0, fruitZero)
proof
  unfold OfNat
  rfl
notation numeral "0" via OfNat(fruitCarrier, 0, _) for Fruit
def zeroGraph : Set :=
  { p ∈ fruitCarrier × fruitCarrier |
    ∃ x ∈ fruitCarrier, p = (x ↦ 0) }

end ContextualMapletNotation
`);
  assert.ok(result.definitions.includes("ContextualMapletNotation.zeroGraph"));
  assert.deepEqual(result.theorems, ["ContextualMapletNotation.fruit_zero"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("soft-typed function parameters type numeral arguments", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module TypedFunctionNumeral
namespace TypedFunctionNumeral
def fruitCarrier : Set := empty
class Fruit (x : Set) := x ∈ fruitCarrier
predicate OfNat (carrier numeral value : Set) := carrier = carrier
def fruitZero : Set := empty
instance fruit_zero
  shows OfNat(fruitCarrier, 0, fruitZero)
proof
  unfold OfNat
  rfl
notation numeral "0" via OfNat(fruitCarrier, 0, _) for Fruit
def preserve (x : Fruit) : Fruit := x

theorem typed_argument
  shows preserve(0) = fruitZero
proof
  unfold preserve
  rfl

end TypedFunctionNumeral
`);
  assert.deepEqual(result.theorems, ["TypedFunctionNumeral.fruit_zero", "TypedFunctionNumeral.preserve.type", "TypedFunctionNumeral.typed_argument"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("userland predicate notation supports ASCII, Unicode, and reversed arguments", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
predicate Below (x y : Set) := x = y
notation infix 50 "<=" => Below
notation infix 50 "≤" => Below
notation infix 50 ">=" => reverse Below
notation infix 50 "≥" => reverse Below

lemma relation.ascii (x y : Set)
  requires h : x >= y
  shows y <= x
proof
  exact h

lemma relation.unicode (x y : Set)
  requires h : x ≥ y
  shows y ≤ x
proof
  exact h
`);
  assert.deepEqual(result.theorems, ["relation.ascii", "relation.unicode"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("instance-selected predicate notation supports overloaded relations", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
predicate Carrier (x : Set) := x = x
predicate HasLess (A relation : Set) := relation = relation
predicate Relates (relation x y : Set) := x = y
def chosenRelation : Set := ∅
instance chosen.less
  shows HasLess(∅, chosenRelation)
proof
  unfold HasLess
  rfl
notation infix 50 "<" => Relates via HasLess(∅, _) for Carrier

lemma selected (x y : Carrier)
  requires h : x < y
  shows Relates(chosenRelation, x, y)
proof
  exact h
`);
  assert.deepEqual(result.theorems, ["chosen.less", "selected"]);
  result.theorems.forEach(name => kernel.checkProof(kernel.theoremProofs.get(name)!));
});

test("rejects conflicting notation declarations in one module", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
module ConflictingNotation
namespace ConflictingNotation
def first (x y : Set) : Set := x
def second (x y : Set) : Set := y
notation infixl 50 "⊙" => first
notation infixr 60 "⊙" => second

end ConflictingNotation
`), (error: unknown) => error instanceof SurfaceError && /already declared/.test(error.message));
});

test("typed notation implementations resolve from checked soft types", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module TypedNotation
namespace TypedNotation
predicate Whole (x : Set) := x = x
predicate Fraction (x : Set) := x = x
def wholePlus (x y : Whole) : Whole := x
def fractionPlus (x y : Fraction) : Fraction := y
notation infixl 60 "+" => wholePlus for Whole
notation infixl 60 "+" => fractionPlus for Fraction

lemma whole.notation (x y : Whole)
  shows x + y = x
proof
  unfold +
  rfl

lemma fraction.notation (x y : Fraction)
  shows x + y = y
proof
  unfold +
  rfl

end TypedNotation
`);
  assert.deepEqual(result.theorems, ["TypedNotation.wholePlus.type", "TypedNotation.fractionPlus.type", "TypedNotation.whole.notation", "TypedNotation.fraction.notation"]);
});

test("typed notation resolves from checked proof-local soft types", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module LocalTypedNotation
namespace LocalTypedNotation
predicate Whole (x : Set) := x = x
predicate Fraction (x : Set) := x = x
def wholePlus (x y : Whole) : Whole := x
def fractionPlus (x y : Fraction) : Fraction := y
notation infixl 60 "+" => wholePlus for Whole
notation infixl 60 "+" => fractionPlus for Fraction

lemma local.notation (x y : Set)
  requires xWhole : Whole(x)
  requires yWhole : Whole(y)
  shows x = x
proof
  have sumWhole : Whole(x + y)
    unfold Whole
    rfl
  rfl

end LocalTypedNotation
`);
  assert.deepEqual(result.theorems, ["LocalTypedNotation.wholePlus.type", "LocalTypedNotation.fractionPlus.type", "LocalTypedNotation.local.notation"]);
});

test("rejects ambiguous notation imported from independent modules", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module Notation.Left
namespace Notation.Left
def first (x y : Set) : Set := x
notation infixl 50 "⊙" => first

end Notation.Left
`);
  elaborateModule(kernel, `module Notation.Right
namespace Notation.Right
def second (x y : Set) : Set := y
notation infixr 60 "⊙" => second

end Notation.Right
`);
  assert.throws(() => elaborateModule(kernel, `module Notation.Client
namespace Notation.Client
import Notation.Left
import Notation.Right
lemma collision (x y : Set)
  shows x ⊙ y = x
proof
  rfl

end Notation.Client
`), (error: unknown) => error instanceof SurfaceError && /ambiguous notation ⊙/.test(error.message));
});

test("bounded quantifiers elaborate membership and refine carrier notation", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module BoundedQuantifiers
namespace BoundedQuantifiers
def Q : Set := ω
class Elem (x : Set) := x ∈ Q
predicate before (x y : Set) := x = x
notation infix 50 "≺" => before for Elem

theorem exists_self (q : Elem)
  shows ∃ p ∈ Q, p ≺ q
proof
  have qElem : Elem(q)
    assumption
  unfold Elem at qElem
  witness q
  constructor
  . exact qElem
  . unfold before
    rfl

theorem all_reflexive
  shows forall p in Q, p = p
proof
  intros p member
  rfl

end BoundedQuantifiers
`);
  assert.deepEqual(result.theorems, [
    "BoundedQuantifiers.exists_self", "BoundedQuantifiers.all_reflexive",
  ]);
  assert.equal(formatFormula(kernel.theorems.get("BoundedQuantifiers.exists_self")!),
    "∀ q, Elem(q) → ∃ p ∈ Q, before(p, q)");
  assert.equal(formatFormula(kernel.theorems.get("BoundedQuantifiers.all_reflexive")!),
    "∀ p ∈ Q, p = p");
});

test("natural bounded quantifiers refine primitive Nat notation", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module NaturalBoundedQuantifiers
namespace NaturalBoundedQuantifiers
predicate NatLe (a b : Nat) := a = a
notation infix 50 "≤" => NatLe for Nat
theorem eventual_reflexivity
  shows ∀ N ∈ ℕ, ∀ n ∈ ℕ, N ≤ n → N ≤ n
proof
  intros N hN n hn le
  exact le

end NaturalBoundedQuantifiers
`);
  assert.deepEqual(result.theorems, ["NaturalBoundedQuantifiers.eventual_reflexivity"]);
});

test("reports the focused goal when a tactic proof is unfinished", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
theorem unfinished (x y : Set)
  shows x = x or x = y
proof
  left
`), (error: unknown) => error instanceof SurfaceError && /1 goal remains; next is x = x/.test(error.message));
});

test("a spaced unavailable predicate gets an import-oriented diagnostic", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
module MissingImport
namespace MissingImport
theorem unavailable (x : Set)
  shows Mystery (x)
proof
  sorry

end MissingImport
`), (error: unknown) => error instanceof SurfaceError &&
    /unknown predicate Mystery; it may be unavailable in the current imports/.test(error.message));
});

test("elaborates Unicode notation to ordinary kernel objects and certified computation", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, source);
  elaborateModule(kernel, setSource);
  const result = elaborateModule(kernel, unicodeSource);
  assert.deepEqual(result.definitions, ["διπλό"]);
  assert.deepEqual(result.theorems, ["διπλό.type", "διπλό.correct", "pair.both_unicode", "equality.exists_unicode", "equality.iff_unicode", "epsilon0.less.unicode", "logic.unicode_quantifiers", "logic.unicode_implication"]);
  assert.equal(formulaEquals(
    kernel.theorems.get("epsilon0.less.unicode")!,
    kernel.theorems.get("epsilon0.less.unfold")!,
  ), true);
  const numeral = (value: number) => {
    let result = app("zero");
    for (let index = 0; index < value; index += 1) result = app("succ", result);
    return result;
  };
  const evaluated = kernel.evaluateCertified(app("διπλό", numeral(4)));
  assert.equal(termEquals(evaluated.value, numeral(8)), true);
  kernel.checkProof(evaluated.proof);
});

test("reports surface errors with source line numbers", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
define bad (x : Nat) -> Nat
  | succ(x) => bad(succ(x))
  | zero => zero
  descends x
`), (error: unknown) => error instanceof SurfaceError && error.line === 2 && /structurally smaller/.test(error.message));
});

test("identifiers use underscores and reserve hyphens for operators", () => {
  assert.throws(() => elaborateModule(createZfgKernel(), `module IdentifierMigration
namespace IdentifierMigration
theorem old-name (x : Set)
  shows x = x
proof
  rfl

end IdentifierMigration
`), (error: unknown) => error instanceof SurfaceError && error.line === 3 &&
    /hyphens are not permitted in theorem identifiers; use old_name/.test(error.message));

  assert.throws(() => elaborateModule(createZfgKernel(), `module IdentifierReference
namespace IdentifierReference
theorem good_name (x : Set)
  shows x = x
proof
  exact old-name

end IdentifierReference
`), (error: unknown) => error instanceof SurfaceError && error.line === 6 &&
    /hyphens are not permitted in proof identifiers; use old_name/.test(error.message));
});

test("a trailing by clause accepts exactly one goal-closing tactic", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `module InlineProof
namespace InlineProof
lemma reflexive (x : Set)
  shows x = x by rfl

end InlineProof
`);
  assert.deepEqual(result.theorems, ["InlineProof.reflexive"]);
  kernel.checkProof(kernel.theoremProofs.get("InlineProof.reflexive")!);

  assert.throws(() => elaborateModule(createZfgKernel(), `module InlineSequence
namespace InlineSequence
lemma reflexive (x : Set)
  shows x = x by rfl; rfl

end InlineSequence
`), /trailing by expects exactly one tactic/);

  assert.throws(() => elaborateModule(createZfgKernel(), `module InlineIncomplete
namespace InlineIncomplete
lemma both (x : Set)
  shows x = x and x = x by constructor

end InlineIncomplete
`), /2 goals remain/);
});

test("requires disambiguation only when multiple structural arguments qualify", () => {
  const kernel = createZfgKernel();
  assert.throws(() => elaborateModule(kernel, `
define ambiguous (x y : Nat) -> Nat
  | zero, zero => zero
  | succ(x), succ(y) => ambiguous(x, y)
`), (error: unknown) => error instanceof SurfaceError && /ambiguous.*descends/.test(error.message));
});

test("exposes deterministic JSON results for agent callers", () => {
  const run = spawnSync(process.execPath, ["bin/g17.ts", "check", "--json", "examples/Arithmetic.g17"], {
    cwd: fileURLToPath(new URL("..", import.meta.url)),
    encoding: "utf8",
  });
  assert.equal(run.status, 0, run.stderr);
  const result = JSON.parse(run.stdout);
  assert.equal(result.ok, true);
  assert.equal(result.checked[0].theorems.length, 14);
  assert.equal(result.foundation.profile, "ZFG");
  assert.deepEqual(result.modules, []);
  assert.match(result.digest, /^[0-9a-f]{64}$/);
});

test("CLI foundation selection is explicit and reflected in agent output", () => {
  const run = spawnSync(process.execPath, ["bin/g17.ts", "check", "--json", "--foundation", "ZF", "examples/Sets.g17"], {
    cwd: fileURLToPath(new URL("..", import.meta.url)),
    encoding: "utf8",
  });
  assert.equal(run.status, 0, run.stderr);
  const result = JSON.parse(run.stdout);
  assert.equal(result.foundation.profile, "ZF");
  assert.equal(result.foundation.axioms.includes("set.choice"), false);
});

test("loads modules, namespaces, imports, and open declarations deterministically", () => {
  const kernel = createZfgKernel();
  const core = elaborateModule(kernel, readFileSync(fileURLToPath(new URL("../examples/CoreNat.g17", import.meta.url)), "utf8"));
  const client = elaborateModule(kernel, readFileSync(fileURLToPath(new URL("../examples/ModuleCompute.g17", import.meta.url)), "utf8"));
  assert.deepEqual(core.definitions, ["Grace.Core.Nat.Rec.add"]);
  assert.deepEqual(core.theorems, ["Grace.Core.Nat.Rec.add.type", "Grace.Core.Nat.Rec.add.left_unit"]);
  assert.deepEqual(client.definitions, ["Grace.Examples.Compute.Demo.double"]);
  assert.deepEqual(client.theorems, [
    "Grace.Examples.Compute.Demo.double.type",
    "Grace.Examples.Compute.Demo.double.three",
    "Grace.Examples.Compute.Demo.imported_add",
  ]);
  assert.deepEqual(moduleReport(kernel).map(item => [item.name, item.imports]), [
    ["Grace.Core.Nat", []],
    ["Grace.Examples.Compute", ["Grace.Core.Nat"]],
  ]);
  const numeral = (value: number) => {
    let result = app("zero");
    for (let index = 0; index < value; index += 1) result = app("succ", result);
    return result;
  };
  const run = kernel.evaluateFastWithStats(app("Grace.Examples.Compute.Demo.double", numeral(100)));
  assert.equal(canonical(run.value), canonical(numeral(200)));
  assert.equal(run.stats.reductions, 101);
});

test("export open composes curated entrypoint scopes without leaking ordinary opens", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `module Prelude.Base
namespace Prelude.Base
namespace Public
def chosen : Set := empty
end Public
namespace Private
def hidden : Set := empty
end Private
open Prelude.Base.Private
export open Prelude.Base.Public

end Prelude.Base
`);
  elaborateModule(kernel, "module Prelude.Bundle\nimport Prelude.Base");
  const client = elaborateModule(kernel, `module Prelude.Client
namespace Prelude.Client
import Prelude.Bundle
lemma chosen.reflexive
  shows chosen = chosen
proof
  rfl

end Prelude.Client
`);
  assert.deepEqual(client.theorems, ["Prelude.Client.chosen.reflexive"]);
  assert.deepEqual(moduleReport(kernel).find(item => item.name === "Prelude.Bundle")?.exportedOpens,
    ["Prelude.Base", "Prelude.Base.Public"]);
  assert.throws(() => elaborateModule(kernel, `module Prelude.BadClient
namespace Prelude.BadClient
import Prelude.Bundle
lemma hidden.reflexive
  shows hidden = hidden
proof
  rfl

end Prelude.BadClient
`), /unknown (?:nullary function|variable or constant) hidden/);
});

test("rejects unimported opens and mismatched namespace endings", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, "module A\nnamespace N\nend N");
  assert.throws(() => elaborateModule(kernel, "module B\nopen A.N"), /unimported namespace/);
  assert.throws(() => elaborateModule(kernel, "module C\nnamespace N\nend Wrong"), /expected end N/);
});

test("instance declarations drive proof-producing synthesis and with-star insertion", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module Instances
namespace Instances
predicate Marked (x : Set) := x = x
def witness : Set := empty

instance marked_witness
  shows Marked(witness)
proof
  unfold Marked
  rfl

theorem Marked.copy (x : Set)
  requires marked : Marked(x)
  shows Marked(x)
proof
  exact marked

lemma synthesized
  shows Marked(witness)
proof
  synthesize

lemma inserted
  shows Marked(witness)
proof
  exact Marked.copy at witness with *

end Instances
`);
  assert.deepEqual(result.theorems, [
    "Instances.marked_witness", "Instances.Marked.copy",
    "Instances.synthesized", "Instances.inserted",
  ]);
  assert.deepEqual(instanceReport(kernel), [
    { name: "Instances.marked_witness", module: "Instances" },
  ]);
});

test("instance synthesis rejects ambiguity, unsafe heads, and malformed declarations", () => {
  const ambiguous = createZfgKernel();
  assert.throws(() => elaborateModule(ambiguous, `
module AmbiguousInstances
namespace AmbiguousInstances
predicate Marked (x : Set) := x = x
def witness : Set := empty
instance first
  shows Marked(witness)
proof
  unfold Marked
  rfl
instance second
  shows Marked(witness)
proof
  unfold Marked
  rfl
lemma selected
  shows Marked(witness)
proof
  synthesize

end AmbiguousInstances
`), /ambiguous instance.*first.*second/);

  assert.throws(() => elaborateModule(createZfgKernel(), `
module MalformedInstance
namespace MalformedInstance
instance equality
  shows empty = empty
proof
  rfl

end MalformedInstance
`), /instance conclusion must be a predicate application/);

  assert.throws(() => elaborateModule(createZfgKernel(), `
module UnsafeInstance
namespace UnsafeInstance
predicate P (x : Set) := x = x
instance loses_parameter (x y : Set)
  requires source : P(y)
  shows P(x)
proof
  unfold P
  rfl

end UnsafeInstance
`), /instance variables must occur in its conclusion(?: or in a hypothesis-shaped premise)?; unconstrained: y/);
});

test("instance visibility follows transitive imports and never global load order", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module Registry.Schema
predicate Marked (x : Set) := x = x
def witness : Set := empty
`);
  elaborateModule(kernel, `
module Registry.Base
import Registry.Schema
instance marked
  shows Marked(witness)
proof
  unfold Marked
  rfl
`);
  elaborateModule(kernel, "module Registry.Bundle\nimport Registry.Base");
  const client = elaborateModule(kernel, `
module Registry.Client
namespace Registry.Client
import Registry.Bundle
lemma found
  shows Registry.Schema.Marked(Registry.Schema.witness)
proof
  synthesize

end Registry.Client
`);
  assert.deepEqual(client.theorems, ["Registry.Client.found"]);
  assert.throws(() => elaborateModule(kernel, `
module Registry.Unrelated
import Registry.Schema
namespace Registry.Unrelated
lemma hidden
  shows Registry.Schema.Marked(Registry.Schema.witness)
proof
  synthesize

end Registry.Unrelated
`), /synthesize found no instance/);
});

test("structured show and symmetry produce checked equalities and reject a mismatched conclusion", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
module StructuredProofs
namespace StructuredProofs

theorem reverse (x y : Set)
  requires h : x = y
  shows y = x
proof
  symm
  show x = y := h

theorem reverse_fact (x y : Set)
  requires h : x = y
  shows y = x
proof
  have original := h
  symm at original
  exact original

end StructuredProofs
`);
  assert.deepEqual(result.theorems, ["StructuredProofs.reverse", "StructuredProofs.reverse_fact"]);
  for (const name of result.theorems) kernel.checkProof(kernel.theoremProofs.get(name)!);
  assert.throws(() => elaborateModule(createZfgKernel(), `
theorem invalid_show (x y : Set)
  requires h : x = y
  shows y = x
proof
  show x = y := h
`), /show states .* but the goal is/);
});

test("induction previews resolve nested namespace constructors", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
namespace Outer
namespace Inner
datatype Token(A : Set)
  | value(payload : A)
end Inner
end Outer

theorem token_shape (A : Set, token : Outer.Inner.Token(A))
  shows ∃ x ∈ A, token = Outer.Inner.Token.value(x)
proof
  induction token
  | Outer.Inner.Token.value(x) =>
    refine ⟨x, assumption, rfl⟩
`);
  assert.deepEqual(result.theorems, ["token_shape"]);
  kernel.checkProof(kernel.theoremProofs.get("token_shape")!);
  const trace = kernel.theoremTacticTraces.get("token_shape")!;
  assert.equal(trace.steps[0]!.after.goals.length, 1);
  assert.match(JSON.stringify(trace.steps[0]!.after.goals[0]!.goal), /Outer\.Inner\.Token\.value/);
});

test("bulleted local proofs retain branch indentation and isolate sibling locals", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
theorem bullet_local (x : Set)
  shows x = x ∧ x = x
proof
  constructor
  . have diagonal : x = x
      rfl
    exact diagonal
  . calc
      x = x := by rfl
`);
  kernel.checkProof(kernel.theoremProofs.get("bullet_local")!);
  assert.throws(() => elaborateModule(createZfgKernel(), `
theorem bullet_leak (x y : Set)
  shows x = x ∧ x = y
proof
  constructor
  . have local : x = x
      rfl
    exact local
  . exact local
`), /unknown.*local/);
  assert.throws(() => elaborateModule(createZfgKernel(), `
theorem bullet_unfinished (x y : Set)
  shows x = x ∧ x = x
proof
  constructor
  . have local : x = y
      by_contra
    rfl
  . rfl
`), /local proof local is incomplete/);
});

test("local universal lemmas are scoped cuts reusable beneath later binders", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
theorem scoped_cut
  shows ∀ y, y = y → y = y
proof
  have diagonal : ∀ y, y = y
    intro y
    rfl
  have reusable : ∀ y, y = y → y = y
    intros y hy
    exact diagonal at y
  exact reusable
`);
  kernel.checkProof(kernel.theoremProofs.get("scoped_cut")!);
  assert.throws(() => elaborateModule(createZfgKernel(), `
theorem cut_does_not_assume (x y : Set)
  shows x = y
proof
  have wish : x = y
    exact wish
  exact wish
`), /unknown.*wish/);
});


test("with star accepts already inferred binder guards but preserves unmet requirements", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
theorem guard_only (n : Nat)
  shows n = n
proof
  rfl

theorem guard_client (n : Nat)
  shows n = n
proof
  exact guard_only at n with *

theorem still_needs_equality (n : Nat)
  requires zero : n = zero
  shows n = zero
proof
  exact zero
`);
  verifyExportedProof(kernel, exportTheorem(kernel, "guard_client"));
  assert.throws(() => elaborateModule(kernel, `
theorem missing_requirement (n : Nat)
  shows n = zero
proof
  exact still_needs_equality at n with *
`), /with \* cannot find evidence/);
  assert.throws(() => elaborateModule(kernel, `
theorem missing_guard (x : Set)
  shows x = x
proof
  exact guard_only at x with *
`), /with \* cannot find evidence/);
});

test("with star stops at declared implication and negation conclusions", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
namespace Boundary

theorem conditional (n : Nat)
  requires diagonal : n = n
  shows n = n → n = n
proof
  intro same
  exact same

theorem negative (n : Nat)
  requires nonzero : n ≠ zero
  shows n ≠ zero
proof
  exact nonzero

theorem conditional_client (n : Nat)
  requires diagonal : n = n
  shows n = n → n = n
proof
  exact conditional at n with *

theorem mixed_client (n : Nat)
  requires diagonal : n = n
  shows n = n → n = n
proof
  exact conditional at n with diagonal, *

theorem explicit_elimination (n : Nat)
  requires diagonal : n = n
  shows n = n
proof
  exact conditional at n with *, diagonal

theorem negative_client (n : Nat)
  requires nonzero : n ≠ zero
  shows n ≠ zero
proof
  exact negative at n with *

theorem negative_with_antecedent (n : Nat)
  requires nonzero : n ≠ zero
  requires zero : n = zero
  shows n ≠ zero
proof
  exact negative at n with *

theorem closed_conditional
  shows zero = zero → zero = zero
proof
  intro same
  exact same

theorem closed_client
  shows zero = zero → zero = zero
proof
  exact closed_conditional with *

theorem two_binders (n m : Nat)
  requires diagonal : n = n
  shows m = m → m = m
proof
  intro same
  exact same

theorem partial_arguments (n m : Nat)
  requires diagonal : n = n
  shows m = m → m = m
proof
  exact two_binders at n with m, *

end Boundary
`);
  for (const name of result.theorems) verifyExportedProof(kernel, exportTheorem(kernel, name));
  assert.throws(() => elaborateModule(kernel, `
theorem missing_negative (n : Nat)
  shows n ≠ zero
proof
  exact Boundary.negative at n with *
`), /with \* cannot find evidence/);
});

test("with star handles equivalence directions without consuming their consequents", () => {
  const kernel = createZfgKernel();
  const result = elaborateModule(kernel, `
theorem negative_iff (n : Nat)
  requires diagonal : n = n
  shows (n ≠ zero) ↔ (n = zero → ⊥)
proof
  tauto

theorem forward_client (n : Nat)
  requires diagonal : n = n
  requires nonzero : n ≠ zero
  shows n ≠ zero
proof
  exact negative_iff.forward at n with *

theorem backward_client (n : Nat)
  requires diagonal : n = n
  requires nonzero : n ≠ zero
  shows n ≠ zero
proof
  exact negative_iff.backward at n with diagonal, *

theorem local_chain (n : Nat)
  requires diagonal : n = n
  requires local : n = n → n = n
  shows n = n
proof
  exact local with *
`);
  for (const name of result.theorems) verifyExportedProof(kernel, exportTheorem(kernel, name));
  assert.throws(() => elaborateModule(kernel, `
theorem missing_iff_side (n : Nat)
  requires diagonal : n = n
  shows n ≠ zero
proof
  exact negative_iff.forward at n with *
`), /with \* cannot find evidence/);
});

test("interactive declaration reuse upgrades dependency-only tactic and induction traces", () => {
  const base = createZfgKernel();
  elaborateModule(base, "module TraceSeed\n");
  const source = `module TraceUpgrade
namespace TraceUpgrade
theorem both (x : Set)
  shows x = x ∧ x = x
proof
  constructor
  . rfl
  . rfl

theorem inductive (n : Nat)
  shows n = n
proof
  induction n
  | zero => rfl
  | succ(k) using ih => rfl

end TraceUpgrade
`;
  const run = (capture: boolean) => {
    const kernel = base.fork();
    forkSurfaceEnvironment(base, kernel);
    setSurfaceTraceCapture(kernel, capture);
    elaborateModule(kernel, source);
    return kernel;
  };
  const dependency = run(false);
  assert.equal(dependency.theoremTacticTraces.has("TraceUpgrade.both"), false);
  const interactive = run(true);
  for (const name of ["TraceUpgrade.both", "TraceUpgrade.inductive"]) {
    const trace = interactive.theoremTacticTraces.get(name)!;
    assert.ok(trace?.initial.goals.length, name);
    assert.ok(trace.steps.length >= 3, name);
    assert.ok(trace.steps.some(step => step.before.goals.length > 0), name);
    assert.equal(trace.steps.at(-1)!.after.goals.length, 0, name);
    verifyExportedProof(interactive, exportTheorem(interactive, name));
  }
  const cached = run(true);
  assert.deepEqual([...cached.theoremTacticTraces], [...interactive.theoremTacticTraces]);
});

test("notation result carriers survive structurally rebuilt applications", () => {
  const kernel = createZfgKernel();
  elaborateModule(kernel, `
module RebuiltNotation
namespace RebuiltNotation
predicate Whole (x : Set) := x = x
def zero : Set := ∅
def operation (x y : Set) : Set := x
notation numeral "0" => zero for Whole
notation infixl 60 "+" => operation for Whole

theorem rebuilt (y : Set)
  shows operation(zero, y) = zero
proof
  calc
    operation(zero, y) = 0 := by simp [operation]
    _ = zero := by rfl
end RebuiltNotation
`);
  assert.ok(kernel.theorems.has("RebuiltNotation.rebuilt"));
});
