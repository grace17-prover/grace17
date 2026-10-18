// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Bundled orders: an ordered set is one set P, a `structure` with P.points
// and P.le,
// `a ≤ b`, `a ⊔ b`, and `a ⊓ b` resolve from the structure hypothesis in
// scope and print back, carrier binders supply the memberships that the
// closure instances turn into `a ⊔ b ∈ points(P)`, the typed `≤` of ℕ and
// ℝ is unaffected, the lattice rewrite set closes the absorption and
// idempotency goals, and the pilot theorems stay within their line budgets.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { createZfKernel, formulaEquals, loadModuleSourceGraph, SurfaceError } from "../src/index.ts";
import { checkWorkbenchFiles, rememberFailureDisplay, workbenchFailure } from "../src/workbench.ts";

const header = "module BundledLattices\nimport Grace.Cumulus.Lattice\n";

const lattice = (body: string) => header + `
section S
variable (P : Set)
hypothesis lattice : Lattice(P)
${body}
end S
`;

function load(source: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "BundledLattices.g17", source }], ["lib"]);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "BundledLattices.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

test("a ≤ b is Le(P, a, b) and a ⊔ b is call2(sup(P), a, b) for the Lattice hypothesis in scope", () => {
  const written = load(lattice(`
theorem upper (a b ∈ points(P))
  shows a ≤ a ⊔ b
proof
  exact le_sup_left with *
`));
  const spelled = load(header + `
theorem upper (P : Set) (a b ∈ points(P))
  requires lattice : Lattice(P)
  shows Le(P, a, call2(sup(P), a, b))
proof
  exact le_sup_left with *
`);
  assert.ok(formulaEquals(written.theorems.get("BundledLattices.upper")!, spelled.theorems.get("BundledLattices.upper")!));
});

test("statements and goals print ≤, ⊔, and ⊓ back with their precedences", () => {
  const result = check(lattice(`
theorem absorb (a b ∈ points(P))
  shows a ⊓ (a ⊔ b) ≤ a ⊔ a ⊓ b
proof
  rw [inf_absorb, sup_absorb]
  exact le_refl with *
`));
  const statement = result.theorems.find(item => item.name === "BundledLattices.absorb")!.statement;
  assert.match(statement, /→ a ⊓ \(a ⊔ b\) ≤ a ⊔ a ⊓ b$/u);
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, [{ file: "BundledLattices.g17", source: lattice(`
theorem open (a b c ∈ points(P))
  requires hab : a ≤ b
  shows (a ⊔ b) ⊔ c = b ⊔ c
proof
  have same : a ⊔ b = b := sup_eq_right with *
  exact hab
`) }], ["lib"]);
    assert.fail("the proof should not check");
  } catch (error) {
    assert.ok(error instanceof SurfaceError);
    rememberFailureDisplay(error, kernel);
    const goal = workbenchFailure(error).trace!.steps.at(-1)!.after.goals[0]!;
    assert.equal(goal.goal, "a ⊔ b ⊔ c = b ⊔ c");
    assert.equal(goal.locals.find(item => item.name === "same")!.formula, "a ⊔ b = b");
    assert.equal(goal.locals.find(item => item.name === "hab")!.formula, "a ≤ b");
  }
});

test("carrier binders feed the closure instances: a ⊔ b ∈ points(P) and nested joins are synthesized", () => {
  check(lattice(`
theorem closed (a b c ∈ points(P))
  shows (a ⊔ b) ⊓ c ∈ points(P)
proof
  exact inf.member with *

theorem nested (a b c ∈ points(P))
  shows (a ⊔ b) ⊔ c ≤ (a ⊔ b) ⊔ c
proof
  exact le_refl with *

theorem bound (a b c ∈ points(P))
  shows (a ⊓ b) ⊓ c ≤ a ⊔ c
proof
  have first : (a ⊓ b) ⊓ c ≤ a ⊓ b := inf_le_left with *
  have second : a ⊓ b ≤ a ⊔ c := inf_le_of_left_le with (le_sup_left with *)
  exact le_trans with *
`));
});

test("the typed ≤ of ℕ and ℝ and ≼ on sets are untouched by the order notation", () => {
  check(header + `
import Grace.Cumulus.Real
import Grace.Cumulus.Cardinal.Dominance

theorem natural (m n : Nat)
  requires h : m ≤ n
  shows m ≤ n + 1
proof
  arith

theorem real (X Y : Real)
  requires h : X ≤ Y
  shows X ≤ Y + 1
proof
  linarith

theorem dominated (A : Set)
  shows A ≼ A
proof
  exact Dominated.reflexive at A
`);
});

test("without a supplying hypothesis ≤ keeps its typed declarations, and the operands' carrier chooses between them and the order", () => {
  const typedHeader = header + "import Grace.Cumulus.Nat.Order\n";
  const bare = load(typedHeader + `
theorem unsupplied (a b : Set)
  shows a ≤ b → a ≤ b
proof
  intros h
  exact h
`);
  const natural = load(typedHeader + `
theorem unsupplied (a b : Set)
  shows LessEqual(a, b) → LessEqual(a, b)
proof
  intros h
  exact h
`);
  assert.ok(formulaEquals(bare.theorems.get("BundledLattices.unsupplied")!, natural.theorems.get("BundledLattices.unsupplied")!));
  // Inside an order section the naturals keep their order and the points
  // of P theirs, decided by where the operands lie.
  const mixed = load(typedHeader + `
section S
variable (P : Set)
hypothesis lattice : Lattice(P)

theorem natural (m n : Nat) (a b ∈ points(P))
  requires h : m ≤ n
  requires hab : a ≤ b
  shows m ≤ n + 1 ∧ a ≤ a ⊔ b
proof
  constructor
  . arith
  . exact le_sup_left with *
end S
`);
  const spelled = load(typedHeader + `
theorem natural (P : Set) (m n : Nat) (a b ∈ points(P))
  requires lattice : Lattice(P)
  requires h : LessEqual(m, n)
  requires hab : Le(P, a, b)
  shows LessEqual(m, n + 1) ∧ Le(P, a, call2(sup(P), a, b))
proof
  constructor
  . arith
  . exact le_sup_left with *
`);
  assert.ok(formulaEquals(mixed.theorems.get("BundledLattices.natural")!, spelled.theorems.get("BundledLattices.natural")!));
  // A compound operand is placed by the closure instances and by the
  // codomain of a function into the points, with no membership binder.
  check(header + `
section M
variable (P Q f : Set)
hypothesis monotone : MonotoneMap(f, P, Q)

theorem image (a b ∈ points(P))
  requires hab : a ≤ b
  shows f(a) ≤ f(b)
proof
  exact MonotoneMap.map_le with *
end M

section B
variable (P : Set)
hypothesis bounded : BoundedLattice(P)

theorem least (a ∈ points(P))
  shows bot(P) ≤ a ⊔ a
proof
  exact bot_le with *
end B
`);
});

test("a binder (a b : P) under an order hypothesis is membership in P.points, and prints back as written", () => {
  const written = load(header + `
section O
variable (P : Set)
hypothesis order : PartialOrder(P)

theorem same (a b : P)
  requires hab : a ≤ b
  requires hba : b ≤ a
  shows a = b
proof
  exact le_antisymm with *
end O
`);
  const spelled = load(header + `
theorem same (P a b : Set)
  requires aIn : a ∈ points(P)
  requires bIn : b ∈ points(P)
  requires order : PartialOrder(P)
  requires hab : Le(P, a, b)
  requires hba : Le(P, b, a)
  shows a = b
proof
  exact le_antisymm with *
`);
  assert.ok(formulaEquals(written.theorems.get("BundledLattices.same")!, spelled.theorems.get("BundledLattices.same")!));
});

test("lattice_simp closes idempotency and absorption goals, and one line lifts a ≤ b to a ≤ b ⊔ c", () => {
  check(lattice(`
theorem rewrite (a b c ∈ points(P))
  shows (a ⊔ a) ⊔ (a ⊓ (a ⊔ c)) = a
proof
  lattice_simp

theorem lift (a b c ∈ points(P))
  requires hab : a ≤ b
  shows a ≤ b ⊔ c
proof
  exact le_sup_of_le_left with *
`));
});

test("⊥, ⊤, ⨆ S, ⨅ S, and aᶜ are read off the hypothesis in scope and print back", () => {
  const bounds = (shows: string) => header + `
section B
variable (P : Set)
hypothesis bounded : BoundedLattice(P)

theorem bounds (a ∈ points(P))
  shows ${shows}
proof
  constructor
  . exact bot_le with *
  . exact le_top with *
end B
`;
  const written = load(bounds("⊥ ≤ a ∧ a ≤ ⊤"));
  const spelled = load(bounds("Le(P, bot(P), a) ∧ Le(P, a, top(P))"));
  assert.ok(formulaEquals(written.theorems.get("BundledLattices.bounds")!, spelled.theorems.get("BundledLattices.bounds")!));
  assert.match(check(bounds("⊥ ≤ a ∧ a ≤ ⊤")).theorems.find(item => item.name === "BundledLattices.bounds")!.statement,
    /→ ⊥ ≤ a ∧ a ≤ ⊤$/u);
  const result = check(header + `
section C
variable (P : Set)
hypothesis complete : CompleteLattice(P)

theorem big (S a : Set)
  requires hS : S ⊆ points(P)
  requires aIn : a ∈ S
  shows ⨅ S ≤ a ∧ a ≤ ⨆ S
proof
  constructor
  . exact sInf_le with *
  . exact le_sSup with *
end C

section A
variable (P : Set)
hypothesis boolean : BooleanAlgebra(P)

theorem twice (a ∈ points(P))
  shows (aᶜ)ᶜ = a ∧ a ⊓ aᶜ = ⊥
proof
  constructor
  . exact compl_compl with *
  . exact inf_compl_eq_bot with *
end A
`);
  const statement = (name: string) => result.theorems.find(item => item.name === `BundledLattices.${name}`)!.statement;
  assert.match(statement("big"), /→ ⨅ S ≤ a ∧ a ≤ ⨆ S$/u);
  assert.match(statement("twice"), /→ \(aᶜ\)ᶜ = a ∧ a ⊓ aᶜ = ⊥$/u);
});

test("a definition inside a section takes the section variables as leading parameters, dropped at its uses in the section", () => {
  const source = header + `
section D
variable (P : Set)
hypothesis bounded : BoundedLattice(P)

def capped (a : Set) : Set := a ⊔ ⊤

theorem inside (a ∈ points(P))
  shows capped(a) = ⊤
proof
  unfold capped
  exact sup_top_eq with *
end D

theorem outside (P : Set) (a ∈ points(P))
  requires bounded : BoundedLattice(P)
  shows capped(P, a) = top(P)
proof
  exact inside with *
`;
  const kernel = load(source);
  assert.ok(formulaEquals(kernel.theorems.get("BundledLattices.inside")!, kernel.theorems.get("BundledLattices.outside")!));
  const result = check(source);
  assert.match(result.theorems.find(item => item.name === "BundledLattices.inside")!.statement, /→ capped\(P, a\) = ⊤$/u);
});

test("the unbundled forms bridge to the bundled ones: Lattice.mk, sup.join, and the powerset lattice with ⊔ = ∪", () => {
  check(header + `
theorem bridge (A r x y : Set)
  requires lattice : IsLattice(A, r)
  requires xIn : x ∈ A
  requires yIn : y ∈ A
  shows call2(sup(Order.mk(A, r)), x, y) = join(A, r, x, y)
proof
  have bundled := Lattice.mk with lattice
  have xIn2 : x ∈ points(Order.mk(A, r))
    rw Order.mk.points
    exact xIn
  have yIn2 : y ∈ points(Order.mk(A, r))
    rw Order.mk.points
    exact yIn
  have value := sup.join with bundled, xIn2, yIn2
  rw [Order.mk.points, Order.mk.le] at value
  exact value

section Powerset
variable (X : Set)
hypothesis complete : CompleteLattice(powersetLattice(X))

theorem union (B C ∈ 𝒫(X))
  shows B ⊔ C = B ∪ C
proof
  exact powersetLattice.sup with *
end Powerset
`);
});

test("the pilot theorems stay within their line budgets", () => {
  const lines = (file: string, name: string): number => {
    const source = readFileSync(`lib/Grace/Cumulus/Lattice/${file}`, "utf8");
    const match = new RegExp(`^(?:theorem|instance) ${name.replace(/\./g, "\\.")}\\b[\\s\\S]*?\\nproof\\n([\\s\\S]*?)\\n\\n`, "mu").exec(source);
    assert.ok(match, `${name} in ${file}`);
    return match![1]!.split("\n").filter(line => line.trim()).length;
  };
  assert.ok(lines("Join.g17", "sup_comm") <= 4);
  assert.ok(lines("Join.g17", "sup_assoc") <= 8);
  assert.ok(lines("Join.g17", "sup_absorb") <= 4);
  assert.ok(lines("OrderHom.g17", "MonotoneMap.comp") <= 3);
  assert.ok(lines("OrderHom.g17", "GaloisConnection.l_u_l_eq_l") <= 6);
  assert.ok(lines("FixedPoints.g17", "lfp_fixed") <= 12);
  const fixed = readFileSync("lib/Grace/Cumulus/Lattice/FixedPoints.g17", "utf8");
  assert.match(fixed, /theorem lfp_fixed\n  shows f\(lfp\(f\)\) = lfp\(f\)/u);
});
