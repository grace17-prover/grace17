// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine, forall, imp, pred, v, formulaEquals } from "../src/index.ts";
import { checkWorkbenchFiles, theoremRanges } from "../src/workbench.ts";
import { declarationHelpAtTextOffset } from "../workbench/tactics-guide.js";

const source = `module Sections
namespace Sections
import Grace.Cumulus.Set
section Shared
variable (A x : Set)
hypothesis hx : x ∈ A

theorem member
  shows x ∈ A
proof
  exact hx

section Nested
variable (y : Set)
hypothesis hy : y ∈ A

theorem both
  shows x ∈ A ∧ y ∈ A
proof
  refine ⟨hx, hy⟩
end Nested

theorem after
  shows x ∈ A
proof
  exact hx
end Shared

theorem outside (x : Set)
  shows x = x
proof
  rfl
end Sections
`;
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "Sections.g17", source: text }], ["lib"]);
  return kernel;
}

test("sections export ordinary universally quantified theorems and nested assumptions do not leak", () => {
  const kernel = load(source);
  const member = pred("in", v("x"), v("A"));
  const expected = forall("A", forall("x", imp(member, member)));
  assert.ok(formulaEquals(kernel.theorems.get("Sections.member")!, expected));
  assert.ok(formulaEquals(kernel.theorems.get("Sections.after")!, expected));
  assert.ok(!kernel.theorems.has("Sections.Shared.member"));
  for (const name of ["member", "both", "after", "outside"]) {
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, `Sections.${name}`)]));
  }
});

test("section boundaries preserve theorem source ranges and declaration hover", () => {
  const lines = source.split("\n");
  const ranges = theoremRanges(source);
  assert.equal(ranges.length, 4);
  assert.equal(ranges[0]!.lineEnd, lines.indexOf("section Nested"));
  assert.equal(ranges[1]!.lineEnd, lines.indexOf("end Nested"));
  for (const word of ["section", "variable", "hypothesis"]) {
    const hover = declarationHelpAtTextOffset(source, source.indexOf(word) + 1);
    assert.equal(hover?.form, word);
  }
});

test("section hypothesis edits invalidate cached proofs", () => {
  const file = { name: "Sections.g17", source };
  const result = checkWorkbenchFiles([file], "ZF", [file.name]);
  assert.equal(result.ok, true);
  const symbol = result.symbols.find(item => item.name === "Sections.outside");
  assert.equal(symbol?.line, source.split("\n").findIndex(line => line.startsWith("theorem outside")) + 1);
  assert.equal(checkWorkbenchFiles([file], "ZF", [file.name]).ok, true);
  const broken = source.replace("hypothesis hx : x ∈ A", "hypothesis hx : x = x");
  assert.throws(() => checkWorkbenchFiles([{ ...file, source: broken }], "ZF", [file.name]));
});

test("section scope rejects leaked assumptions, shadowing, mismatched ends, and unclosed frames", () => {
  for (const [text, error] of [
    [source.replace("theorem outside (x : Set)\n  shows x = x\nproof\n  rfl", "theorem outside (x A : Set)\n  shows x ∈ A\nproof\n  exact hx"), /hx/],
    [source.replace("theorem member", "theorem member (x : Set)"), /distinct/],
    [source.replace("hypothesis hy : y ∈ A", "hypothesis hx : y ∈ A"), /distinct/],
    [source.replace("end Nested", "end Shared"), /expected end Nested/],
    [source.slice(0, source.indexOf("end Shared")), /not closed/],
    [source.replace("section Shared\n", ""), /variable requires an open/],
  ] as const) assert.throws(() => load(text), error);
});

test("section theorem hypotheses cannot become axioms", () => {
  assert.throws(() => load(source.replace("theorem member\n  shows x ∈ A", "theorem member\n  shows x = A")), /exact|goal|prove/);
  const kernel = load(source);
  assert.ok(![...kernel.axioms.keys()].some(name => /Sections|hx|hy/.test(name)));
});
