// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Top 100 entry 93, the birthday problem: among 23 people with uniformly
// random birthdays in a year of 365 days, two share a birthday with
// probability above 1/2. The counting form (the injective assignments are
// fewer than half of all assignments), the probability form on the uniform
// space of all assignments, and the general formula 1 - d(d - 1)⋯(d - n + 1)/dⁿ
// are restated in a workbench file as they are meant to be read, closed by
// the library theorems, and their printed forms are pinned. The module is
// then audited admission-free.

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { createZfgKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const header = "module Top100Birthday\nimport Grace.Cumulus.Probability.Birthday\n\n";

function check(body: string) {
  const result = checkWorkbenchFiles([{ name: "Top100Birthday.g17", source: header + body }], "ZFG",
    ["Top100Birthday.g17"], { includeKernelDetails: false });
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 1200));
  assert.equal(result.sorries.length, 0);
  for (const theorem of result.theorems) assert.equal(theorem.sorries.length, 0, theorem.name);
  return new Map(result.theorems.map(item => [item.name.replace("Top100Birthday.", ""), item.statement]));
}

test("birthday problem, counting form: fewer than half of the assignments of 365 days to 23 people are injective", () => {
  const statements = check(`theorem birthdayCounting
  shows 2 * fallingFactorial(365, 23) < 365 ^ 23
proof
  exact birthday.counting

theorem birthdayInjections (A B : Set)
  requires finiteA : Finite(A)
  requires finiteB : Finite(B)
  requires people : cardinality(A) = 23
  requires days : cardinality(B) = 365
  shows 2 * cardinality(injections(A, B)) < cardinality(functionSpace(A, B))
proof
  exact birthday.injections with *
`);
  assert.equal(statements.get("birthdayCounting"), "2 * fallingFactorial(365, 23) < 365 ^ 23");
  assert.equal(statements.get("birthdayInjections"),
    "∀ A, ∀ B, Finite(A) → Finite(B) → cardinality(A) = 23 → cardinality(B) = 365 → " +
    "2 * cardinality(injections(A, B)) < cardinality(functionSpace(A, B))");
});

test("birthday problem, probability form: two of 23 people share one of 365 birthdays with probability above 1/2", () => {
  const statements = check(`theorem birthdayProblem (A B : Set)
  requires finiteA : Finite(A)
  requires finiteB : Finite(B)
  requires people : cardinality(A) = 23
  requires days : cardinality(B) = 365
  shows (1:R) / 2 <
    (prob(uniformWeight(functionSpace(A, B)), sharedBirthday(A, B)):R)
proof
  exact birthday.problem with *

theorem birthdayFormula (A B : Set)
  requires finiteA : Finite(A)
  requires finiteB : Finite(B)
  requires inhabited : Nonempty(B)
  shows prob(uniformWeight(functionSpace(A, B)), sharedBirthday(A, B)) =
    (1:R) - (realNat(fallingFactorial(cardinality(B), cardinality(A))):R) /
      (realNat(cardinality(B) ^ cardinality(A)):R)
proof
  exact sharedBirthday.probability with *

theorem sharedBirthdayMembership (f A B : Set)
  shows f ∈ sharedBirthday(A, B) ↔
    (f : A → B) ∧ (∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ f(x) = f(y))
proof
  exact sharedBirthday.membership at f, A, B
`);
  assert.equal(statements.get("birthdayProblem"),
    "∀ A, ∀ B, Finite(A) → Finite(B) → cardinality(A) = 23 → cardinality(B) = 365 → " +
    "1 / 2 < prob(uniformWeight(functionSpace(A, B)), sharedBirthday(A, B))");
  assert.equal(statements.get("birthdayFormula"),
    "∀ A, ∀ B, Finite(A) → Finite(B) → Nonempty(B) → " +
    "prob(uniformWeight(functionSpace(A, B)), sharedBirthday(A, B)) = " +
    "1 - realNat(fallingFactorial(cardinality(B), cardinality(A))) / realNat(cardinality(B) ^ cardinality(A))");
  assert.equal(statements.get("sharedBirthdayMembership"),
    "∀ f, ∀ A, ∀ B, f ∈ sharedBirthday(A, B) ↔ FunctionBetween(f, A, B) ∧ ∃ x ∈ A, ∃ y ∈ A, x ≠ y ∧ f(x) = f(y)");
});

test("the birthday module is admission-free and its proofs use no choice", t => {
  const kernel = createZfgKernel();
  const file = "lib/Grace/Cumulus/Probability/Birthday.g17";
  const modules = loadModuleSourceGraph(kernel, [{ file, source: readFileSync(file, "utf8") }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  const names = [...kernel.theorems.keys()].filter(name => /^Grace\.Cumulus\.Probability\.Birthday\./.test(name));
  for (const expected of ["birthday.counting", "birthday.injections", "birthday.problem",
    "sharedBirthday.probability", "sharedBirthday.membership"]) {
    assert.ok(names.some(name => name.endsWith(`.${expected}`)), expected);
  }
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorems audited`);
});
