// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  createZfKernel, createZfgKernel, formatFormula, loadModuleSourceGraph,
} from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

// Every definition form may stand inside a theorem section: the section
// variables are its leading parameters, a form with proof obligations takes
// the section hypotheses as premises, and inside the section it is applied
// without them.
const forms = `module Forms
import Grace.Cumulus.Nat
import Grace.Cumulus.Algebra.Ring

section Counting
variable (A : Set)
hypothesis inhabited : Nonempty(A)

def repeatPair (n : Nat, x : Set) → Set
  | zero, x => x
  | succ(n), x => (A, repeatPair(n, x))

class Inhabitant (x : Set) := x ∈ A

structure Pointed (B : Set)
  | point : Set
  where
    member : point ∈ A
    other : point ∈ B

theorem repeat_zero (x : Set)
  shows repeatPair(0, x) = x
proof
  rw repeatPair
  rfl

end Counting

theorem repeat_outside (B x : Set)
  shows repeatPair(B, 0, x) = x
proof
  rw repeatPair
  rfl

section Fields
variable (A add zero neg mul one a : Set)
notation ring R := (A, add, zero, neg, mul, one)
hypothesis ring : IsRing(R)
hypothesis left : a ∈ R

def pairUp (y : Set) : Set := (a, y)
predicate Marked (y : Set) := y ∈ A ∧ y = a

defgraph shiftBy (x ∈ A) : A := x + a
proof
  exact IsRing.add_closed with ring, member, left

defunique shiftedZero (z ∈ A) := z = a
proof
  witness a
  refine ⟨left, rfl⟩
uniqueness
  intro z
  intro zMember
  intro zValue
  intro y
  intro yMember
  intro yValue
  cc

theorem shift_value (x : Set)
  requires member : x ∈ A
  shows shiftBy(x) = x + a
proof
  exact shiftBy.value with ring, left, member

theorem shifted_marked
  shows Marked(shiftedZero)
proof
  unfold Marked
  exact shiftedZero.selected with ring, left

theorem pair_first (y : Set)
  shows fst(pairUp(y)) = a
proof
  unfold pairUp
  exact fst.pair at a, y

end Fields

theorem outside (B plus z minus times unit b : Set)
  requires ring : IsRing(B, plus, z, minus, times, unit)
  requires hb : b ∈ B
  shows shiftedZero(B, plus, z, minus, times, unit, b) ∈ B
proof
  have h := shiftedZero.selected at B, plus, z, minus, times, unit, b
    with ring, hb
  exact h.left
`;

function load(text: string, file = "Forms.g17", zfg = false) {
  const kernel = zfg ? createZfgKernel() : createZfKernel();
  const loaded = loadModuleSourceGraph(kernel, [{ file, source: text }],
    ["lib"]);
  return {
    kernel, warnings: loaded.find(item => item.file === file)!.warnings,
  };
}

const sectionParameters = "A, add, zero, neg, mul, one, a";

test("every definition form stands inside a section, takes the section " +
  "variables and hypotheses, and is applied without them there", () => {
  const { kernel, warnings } = load(forms);
  assert.equal(kernel.functions.get("Forms.repeatPair"), 3);
  assert.equal(kernel.predicates.get("Forms.Inhabitant"), 2);
  assert.equal(kernel.predicates.get("Forms.Pointed"), 3);
  assert.equal(kernel.functions.get("Forms.pairUp"), 8);
  assert.equal(kernel.predicates.get("Forms.Marked"), 8);
  assert.equal(kernel.functions.get("Forms.shiftBy"), 7);
  assert.equal(kernel.functions.get("Forms.shiftedZero"), 7);
  assert.equal(kernel.functions.get("Forms.shiftedZero.candidates"), 7);
  const statement = (name: string): string =>
    formatFormula(kernel.theorems.get(`Forms.${name}`)!);
  const premises = /IsRing\(A, add, zero, neg, mul, one\) → a ∈ A →/;
  const selected = statement("shiftedZero.selected");
  assert.match(selected,
    /^∀ A, ∀ add, ∀ zero, ∀ neg, ∀ mul, ∀ one, ∀ a, /);
  assert.match(selected, premises);
  assert.match(selected,
    /shiftedZero\(A, add, zero, neg, mul, one, a\) ∈ A/);
  assert.match(statement("shiftBy.value"),
    /IsRing\(A, add, zero, neg, mul, one\) → a ∈ A → x ∈ A →/);
  assert.match(statement("shift_value"),
    /shiftBy\(A, add, zero, neg, mul, one, a\)/);
  assert.match(statement("shifted_marked"),
    new RegExp(`Marked\\(${sectionParameters}, ` +
      `shiftedZero\\(${sectionParameters}\\)\\)`));
  // The hypothesis the existence and uniqueness proofs leave unused is
  // reported once, for the definition.
  const unused = warnings.filter(item => item.theorem === "Forms.shiftedZero");
  assert.deepEqual(unused.map(item => item.message), [
    "section hypothesis ring is a premise of the laws of shiftedZero " +
    "that its proofs do not use",
  ]);
  assert.ok(warnings.every(item => !item.theorem.endsWith(".candidates")));
});

test("a definition that restates a section variable, the short defgraph " +
  "form, a repeated premise name, and an unsupported form are told why", () => {
  const closure = "defgraph shiftBy (x ∈ A) : A := x + a\nproof\n" +
    "  exact IsRing.add_closed with ring, member, left";
  const unique = "defunique shiftedZero (z ∈ A) := z = a\nproof";
  for (const [from, to, error] of [
    ["def pairUp (y : Set)", "def pairUp (a y : Set)",
      /the section already binds a; a definition in a section takes the/],
    ["defunique shiftedZero (z ∈ A)",
      "defunique shiftedZero (A : Set) (z ∈ A)",
      /the section already binds A; a definition in a section/],
    ["theorem shift_value (x : Set)", "theorem shift_value (a x : Set)",
      /the section already binds a; a theorem in a section takes the/],
    [closure, "defgraph shiftBy (n : Nat) : Real := a",
      /the short defgraph form takes no parameters; in a section write/],
    [unique,
      "defunique shiftedZero (z ∈ A) := z = a\nrequires left : a ∈ A\n" +
        "proof",
      /duplicate section\/definition binder or hypothesis left/],
    ["class Inhabitant (x : Set) := x ∈ A", "datatype Marker\n  | mark",
      /defgraph, defunique, and defchoose; datatype/],
  ] as const) {
    assert.ok(forms.includes(from), from);
    assert.throws(() => load(forms.replace(from, to)), error);
  }
});

test("the Workbench symbol index locates a definition inside a section", () => {
  const result = checkWorkbenchFiles(
    [{ name: "Forms.g17", source: forms }], "ZFG");
  assert.ok(result.ok, JSON.stringify(result).slice(0, 400));
  const lines = forms.split("\n");
  for (const [name, header] of [
    ["Forms.shiftedZero", "defunique shiftedZero (z ∈ A) := z = a"],
    ["Forms.shiftBy", "defgraph shiftBy (x ∈ A) : A := x + a"],
    ["Forms.repeatPair", "def repeatPair (n : Nat, x : Set) → Set"],
    ["Forms.Marked", "predicate Marked (y : Set) := y ∈ A ∧ y = a"],
  ] as const) {
    const symbol = result.symbols.find(item => item.name === name);
    assert.ok(symbol, name);
    assert.equal(symbol.line, lines.indexOf(header) + 1, name);
  }
});

// An instance in a section takes only the section context its conclusion
// fixes, and of the section hypotheses only those of predicate shape.
const instances = `module Instances
import Grace.Cumulus.Real

def twice (x : Set) : Set := realAdd(x, x)

section Terms
variable (x y : Set)
hypothesis hx : Real(x)
hypothesis hy : Real(y)
hypothesis nonzero : x ≠ (0:R)

instance twice.real
  shows Real(twice(x))
proof
  unfold twice
  typecheck

theorem twice_zero
  shows twice(x) = (0:R) → x = (0:R)
proof
  intro h
  unfold twice at h
  linarith

end Terms

theorem use_twice (a : Set)
  requires ha : Real(a)
  shows Real(twice(a))
proof
  exact twice.real with ha
`;

test("an instance in a section takes the predicate hypotheses about the " +
  "variables its conclusion mentions and no other section context", () => {
  const { kernel, warnings } = load(instances, "Instances.g17", true);
  assert.equal(formatFormula(kernel.theorems.get("Instances.twice.real")!),
    "∀ x : ℝ, twice(x) : ℝ");
  // The theorem of the same section keeps every variable and hypothesis.
  assert.equal(formatFormula(kernel.theorems.get("Instances.twice_zero")!),
    "∀ x y : ℝ, x ≠ realZero → twice(x) = realZero → x = realZero");
  // No warning about a hypothesis the instance does not take.
  const about = (name: string) =>
    warnings.filter(item => item.theorem === `Instances.${name}`);
  assert.deepEqual(about("twice.real"), []);
  assert.equal(about("twice_zero").length, 2);
});

// A hypothesis-shaped premise fixes its other variables from a fact of its
// shape, so an instance about M under Module(M, R) takes R and the premise.
const bound = `module Bound
import Grace.Cumulus.Algebra.Module

section Laws
variable (R M : Set)
hypothesis ring : Ring(R)
hypothesis module : Module(M, R)

instance zero_mem
  shows M.zero ∈ M
proof
  exact Module.zero_mem with ring, module

end Laws
`;

test("a hypothesis-shaped section premise sharing a variable with the " +
  "conclusion stays, with the variables it fixes", () => {
  const { kernel } = load(bound, "Bound.g17", true);
  assert.equal(formatFormula(kernel.theorems.get("Bound.zero_mem")!),
    "∀ R, ∀ M, Ring(R) → Module(M, R) → M.zero ∈ M.carrier");
});

test("an instance proof reaching for section context the instance does not " +
  "take is told why it is absent", () => {
  const reaching = (fact: string): string =>
    instances.replace("  unfold twice\n  typecheck",
      `  unfold twice\n  have h := ${fact}\n  typecheck`);
  assert.throws(() => load(reaching("nonzero"), "Instances.g17", true),
    /nonzero is absent because an instance's premises must be predicates/);
  assert.throws(() => load(reaching("hy"), "Instances.g17", true),
    /hy is absent because the conclusion does not mention y/);
});
