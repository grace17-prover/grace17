// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Typing rules and guard predicates are visible only through imports, as
// declarations and instances are: a module checks the same way whether or
// not an unrelated module was loaded before it, so a library's load order
// cannot change which operator a token resolves to or which side condition
// a tactic discharges.

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, loadModuleSourceGraph } from "../src/index.ts";

interface Entry { readonly file: string; readonly source: string }

// A predicate shared by the modules below.
const sharedPredicate: Entry = { file: "VisibilityC.g17", source: `module VisibilityC
import Grace.Cumulus.Int

predicate Letter (ℓ : Set) := ℓ ∈ 4
predicate Guard (f a b : Set) := f ∈ a ∧ b ∈ a
` };

// The bare-variable instance and a typing lemma of one module.
const typingModule: Entry = { file: "VisibilityA.g17", source: `module VisibilityA
import VisibilityC

instance letter.natural (ℓ : Set)
  requires member : ℓ ∈ 4
  shows Nat(ℓ)
proof
  exact natural.member at 4 with ℓ, member

theorem letter.typed (ℓ : Set)
  requires member : Letter(ℓ)
  shows Nat(ℓ)
proof
  unfold Letter at member
  exact natural.member at 4 with ℓ, member
` };

const dependent = (name: string, imports: readonly string[], body: string): Entry => ({
  file: `${name}.g17`,
  source: `module ${name}\n${imports.map(item => `import ${item}`).join("\n")}\n\n${body}`,
});

const bodies = {
  typecheck: `theorem typed (ℓ : Set)
  requires member : ℓ ∈ 4
  shows Nat(ℓ)
proof
  typecheck
`,
  ring: `theorem product (ℓ : Set)
  requires member : ℓ ∈ 4
  shows ℓ * 1 = ℓ
proof
  ring
`,
  // The typed `*` between a letter and a numeral resolves only once the
  // letter is known to be natural.
  operator: `theorem product (ℓ : Set)
  requires member : Letter(ℓ)
  shows ℓ * 1 = ℓ
proof
  sorry
`,
  withStar: `theorem largest (ℓ : Set)
  requires member : ℓ ∈ 4
  shows natMax(ℓ, 0) = ℓ
proof
  exact natMax.zero_right with *
`,
};

/** The outcome of loading a module graph: its checked theorems, or the error. */
function outcome(entries: readonly Entry[], module: string): string {
  const kernel = createZfKernel();
  try {
    loadModuleSourceGraph(kernel, entries, ["lib"]);
  } catch (error) {
    return `error: ${(error as Error).message}`;
  }
  return [...kernel.theorems].filter(([name]) => name.startsWith(`${module}.`))
    .map(([name, formula]) => `${name}: ${JSON.stringify(formula)}`).join("\n");
}

for (const [tactic, body] of Object.entries(bodies)) {
  test(`${tactic} in a module that does not import the typing lemma is the same with it loaded or not`, () => {
    const alone = outcome([sharedPredicate, dependent("VisibilityB", ["VisibilityC"], body)], "VisibilityB");
    const after = outcome([sharedPredicate, typingModule, dependent("VisibilityB", ["VisibilityC"], body)], "VisibilityB");
    assert.match(alone, /^error: line \d+: /);
    assert.equal(after, alone);
  });
}

test("the typing lemma reaches a module through its import", () => {
  for (const body of [bodies.typecheck, bodies.ring, bodies.operator, bodies.withStar]) {
    const checked = outcome([sharedPredicate, typingModule, dependent("VisibilityD", ["VisibilityA"], body)], "VisibilityD");
    assert.doesNotMatch(checked, /^error/);
    assert.match(checked, /^VisibilityD\./);
  }
});

// A guard predicate declared by one module over the shared predicate.
const guardModule: Entry = { file: "GuardA.g17", source: `module GuardA
import VisibilityC

notation guard "_ : _ ⇝ _" => Guard
` };
const openedGuard = `theorem opened (f a b : Set)
  requires g : Guard(f, a, b)
  shows f ∈ a
proof
  typecheck
`;

test("a guard registered by one module does not open the predicate in a module that does not import it", () => {
  const alone = outcome([sharedPredicate, dependent("GuardB", ["VisibilityC"], openedGuard)], "GuardB");
  const after = outcome([sharedPredicate, guardModule, dependent("GuardB", ["VisibilityC"], openedGuard)], "GuardB");
  assert.match(alone, /^error: line \d+: typecheck could not infer f ∈ a/);
  assert.equal(after, alone);
  const imported = outcome([sharedPredicate, guardModule, dependent("GuardD", ["GuardA"], openedGuard)], "GuardD");
  assert.match(imported, /^GuardD\.opened/);
});
