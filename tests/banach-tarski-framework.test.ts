// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The Banach–Tarski framework: words and the free group on two generators
// (Algebra/Group/Words, FreeGroup), and paradoxical decompositions with the
// transfer theorem (Algebra/Group/Paradox). The three modules are checked
// through the machine interface's check and audit methods: every
// theorem is proved, the statements print as written, the free group's
// decomposition checks, and the transfer theorem's audit names the choice
// axiom and nothing beyond the ZF axioms.

import test from "node:test";
import assert from "node:assert/strict";
import { callMachineMethod } from "../src/index.ts";

const prefix = "Grace.Cumulus.Algebra.Group.";
const modules = ["Words", "FreeGroup", "Paradox"];

interface Audit {
  complete: boolean;
  hereditary: string[];
}

interface Theorem {
  name: string;
  status: string;
  statement?: string;
  audit?: Audit;
}

interface CheckResult {
  status: string;
  theorems: Theorem[];
  sorries: unknown[];
}

// Each module is checked in its own one-file workspace with the audit
// attached to every theorem, which is the fast route: a workspace of
// several files is reported in one call, but the audit method rebuilds
// the environment per call.
const checked = new Map<string, CheckResult>();

function framework(module: string): CheckResult {
  let result = checked.get(module);
  if (!result) {
    result = callMachineMethod("check", {
      files: [{ name: `lib/Grace/Cumulus/Algebra/Group/${module}.g17` }],
      audit: true,
    }) as CheckResult;
    checked.set(module, result);
  }
  return result;
}

function theorem(name: string): Theorem {
  const module = name.slice(0, name.indexOf("."));
  const found = framework(module).theorems.find(item => item.name === prefix + name);
  assert.ok(found, `${name} is a theorem of the framework`);
  return found;
}

function audit(name: string): Audit {
  const found = theorem(name).audit;
  assert.ok(found, `${name} carries an audit`);
  return found;
}

const zfAxioms = /^(set\.(empty|extensionality|foundation|infinity|infinity\.minimal|pairing|powerset|union)|function\.apply)$/u;

test("the three framework modules check with every theorem proved", t => {
  let count = 0;
  for (const module of modules) {
    const result = framework(module);
    assert.equal(result.status, "checked", module);
    assert.deepEqual(result.sorries, [], module);
    const unproved = result.theorems.filter(item => item.status !== "proved").map(item => item.name);
    assert.deepEqual(unproved, [], module);
    count += result.theorems.length;
  }
  t.diagnostic(`${count} theorems proved`);
});

test("the statements print as written", () => {
  assert.equal(theorem("FreeGroup.freeGroup.group").statement, "Group(freeGroup)");
  assert.equal(
    theorem("Paradox.Paradoxical.of_free_action").statement,
    "∀ act, ∀ G, ∀ X, ∀ φ, Action(act, G, X) → FreeAction(act, G, X) → GroupHom(φ, freeGroup, G) → InjectiveBetween(φ, reducedWords, G.carrier) → Paradoxical(act, G, X)",
  );
  assert.equal(
    theorem("Paradox.Paradoxical.of_free_freeGroup").statement,
    "∀ act, ∀ X, Action(act, freeGroup, X) → FreeAction(act, freeGroup, X) → Paradoxical(act, freeGroup, X)",
  );
  assert.equal(
    theorem("Paradox.Equidecomposable.reflexive").statement,
    "∀ act, ∀ G, ∀ X, ∀ A, Action(act, G, X) → A ⊆ X → Equidecomposable(act, G, X, A, A)",
  );
  assert.equal(
    theorem("Paradox.Equidecomposable.symmetric").statement,
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, Action(act, G, X) → Equidecomposable(act, G, X, A, B) → Equidecomposable(act, G, X, B, A)",
  );
  assert.equal(
    theorem("Paradox.Equidecomposable.transitive").statement,
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ C, Action(act, G, X) → Equidecomposable(act, G, X, A, B) → Equidecomposable(act, G, X, B, C) → Equidecomposable(act, G, X, A, C)",
  );
  assert.equal(
    theorem("Paradox.Equidecomposable.disjoint_union").statement,
    "∀ act, ∀ G, ∀ X, ∀ A, ∀ B, ∀ C, ∀ D, Action(act, G, X) → Equidecomposable(act, G, X, A, C) → Equidecomposable(act, G, X, B, D) → Disjoint(A, B) → Disjoint(C, D) → Equidecomposable(act, G, X, A ∪ B, C ∪ D)",
  );
  assert.equal(
    theorem("Words.reduce.concat").statement,
    "∀ u, ∀ v, List(4, u) → List(4, v) → reduce(concat(u, v)) = reduce(concat(reduce(u), reduce(v)))",
  );
  assert.equal(
    theorem("Words.reduce.inverse_left").statement,
    "∀ w, List(4, w) → reduce(concat(inverseWord(w), w)) = []",
  );
  assert.equal(
    theorem("Words.reducedWords.mem_iff").statement,
    "∀ w, w ∈ reducedWords ↔ List(4, w) ∧ Reduced(w)",
  );
});

test("the free group's paradoxical decomposition checks", () => {
  assert.equal(
    theorem("FreeGroup.reducedWords.decomposition").statement,
    "reducedWords = {[]} ∪ startsWith(0) ∪ startsWith(1) ∪ startsWith(2) ∪ startsWith(3)",
  );
  assert.equal(
    theorem("FreeGroup.freeGroup.decomposition_a").statement,
    "startsWith(0) ∪ leftCoset(freeGroup, freeA, startsWith(1)) = reducedWords ∧ Disjoint(startsWith(0), leftCoset(freeGroup, freeA, startsWith(1)))",
  );
  assert.equal(
    theorem("FreeGroup.freeGroup.decomposition_b").statement,
    "startsWith(2) ∪ leftCoset(freeGroup, freeB, startsWith(3)) = reducedWords ∧ Disjoint(startsWith(2), leftCoset(freeGroup, freeB, startsWith(3)))",
  );
  assert.equal(
    theorem("FreeGroup.leftCoset.letter").statement,
    "∀ ℓ m ∈ 4, m = inverseLetter(ℓ) → leftCoset(freeGroup, [ℓ], startsWith(m)) = reducedWords ∖ startsWith(ℓ)",
  );
  assert.equal(
    theorem("FreeGroup.startsWith.disjoint").statement,
    "∀ ℓ m ∈ 4, ℓ ≠ m → Disjoint(startsWith(ℓ), startsWith(m))",
  );
  for (const name of ["FreeGroup.freeGroup.group", "FreeGroup.reducedWords.decomposition", "FreeGroup.freeGroup.decomposition_a", "FreeGroup.freeGroup.decomposition_b"]) {
    assert.equal(theorem(name).status, "proved", name);
  }
});

test("the transfer theorem's audit names the choice axiom and nothing beyond ZF", t => {
  assert.equal(theorem("Paradox.Paradoxical.of_free_action").status, "proved");
  const transfer = audit("Paradox.Paradoxical.of_free_action");
  assert.equal(transfer.complete, true);
  assert.ok(transfer.hereditary.includes("set.choice"));
  const others = transfer.hereditary.filter(axiom => axiom !== "set.choice");
  assert.deepEqual(others.filter(axiom => !zfAxioms.test(axiom)), []);
  assert.deepEqual(transfer.hereditary.filter(axiom => /sorry|globalChoice/u.test(axiom)), []);
  t.diagnostic(`transfer theorem axioms: ${transfer.hereditary.join(", ")}`);
});

test("everything about words and the free group is a theorem of ZF", t => {
  const names = ["Words", "FreeGroup"].flatMap(module => framework(module).theorems.map(item => item.name));
  assert.ok(names.length > 100);
  for (const name of names) {
    const axioms = audit(name.slice(prefix.length));
    assert.equal(axioms.complete, true, name);
    assert.deepEqual(axioms.hereditary.filter(axiom => !zfAxioms.test(axiom)), [], name);
  }
  t.diagnostic(`${names.length} word and free-group theorems audited without choice`);
});
