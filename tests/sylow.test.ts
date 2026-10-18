// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Sylow's theorems over a bundled group: stated for Group(G) with
// order(G) = p ^ k * m and p prime not dividing m, a Sylow p-subgroup
// exists, every p-subgroup lies in a conjugate of it, any two Sylow
// p-subgroups are conjugate, and their number divides m and is 1 modulo p.
// The group-action infrastructure underneath prints with g ·ₐ x, orbit(x),
// and stabilizer(x), and the orbit–stabilizer theorem reads as on the board.

import assert from "node:assert/strict";
import test from "node:test";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module SylowTest\nimport Grace.Cumulus.Algebra.Group\n";

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "SylowTest.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

function statement(result: ReturnType<typeof check>, name: string): string {
  return result.theorems.find(item => item.name === `SylowTest.${name}`)!.statement;
}

const hypotheses = `  requires finite : Finite(G)
  requires prime : Prime(p)
  requires notDivides : ¬(p ∣ m)
  requires count : order(G) = p ^ k * m`;

test("Sylow's theorems are stated over Group(G) with order(G) = p ^ k * m and print as written", () => {
  const result = check(header + `
section S
variable (G : Set)
hypothesis group : Group(G)

theorem first (p k m : Nat)
${hypotheses}
  shows ∃ P, Subgroup(P, G) ∧ cardinality(P) = p ^ k
proof
  exact sylow.exists_subgroup with *

theorem contained (P Q : Set) (p : Nat)
  requires finite : Finite(G)
  requires prime : Prime(p)
  requires sylow : SylowSubgroup(P, G, p)
  requires pSubgroup : PSubgroup(Q, G, p)
  shows ∃ g ∈ G, Q ⊆ conjugateSet(G, g, P)
proof
  exact sylow.subset_conjugate with *

theorem second (P Q : Set) (p : Nat)
  requires finite : Finite(G)
  requires prime : Prime(p)
  requires sylowP : SylowSubgroup(P, G, p)
  requires sylowQ : SylowSubgroup(Q, G, p)
  shows ∃ g ∈ G, Q = conjugateSet(G, g, P)
proof
  exact sylow.conjugate with group, finite, prime, sylowP, sylowQ

theorem thirdDivides (p k m : Nat)
${hypotheses}
  shows cardinality(sylowSubgroups(G, p)) ∣ m
proof
  exact sylow.count_dvd with *

theorem thirdModulo (p k m : Nat)
${hypotheses}
  shows cardinality(sylowSubgroups(G, p)) % p = 1
proof
  exact sylow.count_mod with *
end S
`);
  const prefix = "∀ G, ∀ p k m : ℕ, Group(G) → Finite(G) → Prime(p) → ¬p ∣ m → order(G) = p ^ k * m → ";
  assert.equal(statement(result, "first"), prefix + "∃ P, Subgroup(P, G) ∧ cardinality(P) = p ^ k");
  assert.equal(statement(result, "thirdDivides"), prefix + "cardinality(sylowSubgroups(G, p)) ∣ m");
  assert.equal(statement(result, "thirdModulo"), prefix + "cardinality(sylowSubgroups(G, p)) % p = 1");
  assert.equal(statement(result, "contained"),
    "∀ G P Q, ∀ p : ℕ, Group(G) → Finite(G) → Prime(p) → SylowSubgroup(P, G, p) → PSubgroup(Q, G, p) → ∃ g ∈ G.carrier, Q ⊆ conjugateSet(G, g, P)");
  assert.equal(statement(result, "second"),
    "∀ G P Q, ∀ p : ℕ, Group(G) → Finite(G) → Prime(p) → SylowSubgroup(P, G, p) → SylowSubgroup(Q, G, p) → ∃ g ∈ G.carrier, Q = conjugateSet(G, g, P)");
});

test("an action hypothesis act : G ↷ X supplies g ·ₐ x, orbit(x), and stabilizer(x), and orbit–stabilizer reads as on the board", () => {
  const result = check(header + `
section A
variable (act G X : Set)
hypothesis action : act : G ↷ X

theorem laws (g h : G) (x : Set)
  requires hx : x ∈ X
  shows (g * h) ·ₐ x = g ·ₐ h ·ₐ x ∧ G.one ·ₐ x = x ∧ g ·ₐ x ∈ orbit(x)
proof
  refine ⟨(mul_act with *), (one_act with *), (orbit.act_mem with *)⟩

theorem stabilizerSubgroup (x : Set)
  requires hx : x ∈ X
  shows Subgroup(stabilizer(x), G)
proof
  exact stabilizer.subgroup with *

theorem orbitStabilizer (x : Set)
  requires hx : x ∈ X
  requires finite : Finite(G)
  shows cardinality(orbit(x)) * cardinality(stabilizer(x)) = order(G)
proof
  exact orbit_stabilizer with *

theorem typed (g : G) (x : Set)
  requires hx : x ∈ X
  shows g⁻¹ ·ₐ g ·ₐ x ∈ X
proof
  typecheck
end A
`);
  assert.equal(statement(result, "laws"),
    "∀ act G X, ∀ (g h : G), ∀ x, Action(act, G, X) → x ∈ X → (g * h) ·ₐ x = g ·ₐ h ·ₐ x ∧ G.one ·ₐ x = x ∧ g ·ₐ x ∈ orbit(x)");
  assert.equal(statement(result, "orbitStabilizer"),
    "∀ act, ∀ G, ∀ X, ∀ x, Action(act, G, X) → x ∈ X → Finite(G) → cardinality(orbit(x)) * cardinality(stabilizer(x)) = order(G)");
  assert.equal(statement(result, "stabilizerSubgroup"),
    "∀ act, ∀ G, ∀ X, ∀ x, Action(act, G, X) → x ∈ X → Subgroup(stabilizer(x), G)");
});

test("conjugation: the class equation, conjugate subgroups, and the normalizer check under a group hypothesis", () => {
  check(header + `
section C
variable (G : Set)
hypothesis group : Group(G)

theorem classes (p : Nat)
  requires finite : Finite(G)
  requires dividesOrder : p ∣ order(G)
  requires dividesClasses : ∀ x ∈ G, ¬x ∈ center(G) → p ∣ index(G, centralizer(G, {x}))
  shows p ∣ cardinality(center(G))
proof
  exact center.dvd_of_classes with *

theorem conjugateSubgroup (g : G) (H : Set)
  requires subgroup : Subgroup(H, G)
  shows Subgroup(conjugateSet(G, g, H), G) ∧ H ⊆ normalizer(G, H)
proof
  refine ⟨(conjugateSet.subgroup with *), (normalizer.contains with *)⟩

theorem normalInNormalizer (H : Set)
  requires subgroup : Subgroup(H, G)
  shows NormalSubgroup(H, subgroupGroup(G, normalizer(G, H)))
proof
  exact normalizer.normal with *
end C
`);
});

const area = "lib/Grace/Cumulus/Algebra/Group/";

test("the library states Sylow's theorems and the class equation as written on the board", () => {
  const sylow = readFileSync(area + "Sylow.g17", "utf8");
  assert.match(sylow, /theorem sylow\.exists_subgroup \(p k m : Nat\)\n  requires finite : Finite\(G\)\n  requires prime : Prime\(p\)\n  requires notDivides : ¬\(p ∣ m\)\n  requires count : order\(G\) = p \^ k \* m\n  shows ∃ P, Subgroup\(P, G\) ∧ cardinality\(P\) = p \^ k/u);
  assert.match(sylow, /theorem sylow\.conjugate \(P Q : Set\) \(p : Nat\)\n(?:  requires [^\n]+\n){4}  shows ∃ g ∈ G, Q = conjugateSet\(G, g, P\)/u);
  assert.match(sylow, /theorem sylow\.count_dvd \(p k m : Nat\)\n(?:  requires [^\n]+\n){4}  shows cardinality\(sylowSubgroups\(G, p\)\) ∣ m/u);
  assert.match(sylow, /theorem sylow\.count_mod \(p k m : Nat\)\n(?:  requires [^\n]+\n){4}  shows cardinality\(sylowSubgroups\(G, p\)\) % p = 1/u);
  assert.doesNotMatch(sylow, /sorry/u);
  const action = readFileSync(area + "Action.g17", "utf8");
  assert.match(action, /theorem orbit_stabilizer \(x : Set\)\n  requires hx : x ∈ X\n  requires finite : Finite\(G\)\n  shows cardinality\(orbit\(x\)\) \* cardinality\(stabilizer\(x\)\) = order\(G\)/u);
  const conjugation = readFileSync(area + "Conjugation.g17", "utf8");
  assert.match(conjugation, /theorem class_equation\n  requires finite : Finite\(G\)\n  shows order\(G\) = cardinality\(center\(G\)\) \+\n    natSum\(noncentralClasses\(G\), sizeMap\(noncentralClasses\(G\)\)\)/u);
});
