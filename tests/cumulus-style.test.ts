// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";

function graceFiles(root: string): string[] {
  return readdirSync(root, { withFileTypes: true }).flatMap(entry => {
    const path = join(root, entry.name);
    return entry.isDirectory() ? graceFiles(path) : entry.name.endsWith(".g17") ? [path] : [];
  });
}

test("Cumulus declarations use underscores rather than hyphens", () => {
  const failures: string[] = [];
  const declaration = /^\s*(?:noncomputable\s+(?:transfinite|foundation)\s+)?(?:theorem|lemma|def|predicate|class|axiom|namespace)\s+([^\s(]+)/u;
  for (const file of graceFiles("lib/Grace/Cumulus")) {
    const lines = readFileSync(file, "utf8").split("\n");
    for (let index = 0; index < lines.length; index += 1) {
      const name = declaration.exec(lines[index]!)?.[1];
      if (name?.includes("-")) failures.push(`${file}:${index + 1}: ${name}`);
    }
  }
  assert.deepEqual(failures, []);
});

test("Cumulus proofs avoid mechanical verbosity", () => {
  const failures: string[] = [];
  for (const file of graceFiles("lib/Grace/Cumulus")) {
    const lines = readFileSync(file, "utf8").split("\n");
    for (let index = 0; index + 1 < lines.length; index += 1) {
      const first = lines[index]!;
      const second = lines[index + 1]!;
      const location = `${file}:${index + 1}`;
      const have = /^(\s*)(?:\. )?have ([\p{L}_][\p{L}\p{M}\p{N}_]*) := /u.exec(first);
      if (have && new RegExp(`^${have[1]}(?:\\. )?specialize ${have[2]} with `, "u").test(second)) {
        failures.push(`${location}: apply the fact directly with with`);
      }
      if (have && new RegExp(`^${have[1]}(?:\\. )?exact ${have[2]}$`, "u").test(second)) {
        failures.push(`${location}: inline the one-use fact after exact`);
      }
      const intro = /^(\s*)(?:\. )?intro\s+/u.exec(first);
      if (intro && new RegExp(`^${intro[1]}(?:\\. )?intro\\s+`, "u").test(second)) {
        failures.push(`${location}: use intros for adjacent introductions`);
      }
      const unfold = /^(\s*)(?:\. )?unfold \S+ at (\S+)$/u.exec(first);
      if (unfold && new RegExp(`^${unfold[1]}(?:\\. )?(?:rcases ${unfold[2]} with |obtain .+ := ${unfold[2]}$)`, "u").test(second)) {
        failures.push(`${location}: recursive destructuring follows transparent predicates directly`);
      }
    }
  }
  assert.deepEqual(failures, []);
});

test("Cumulus reserves maplets for function-like graph entries", () => {
  const expected = new Map<string, number>([
    ["lib/Grace/Cumulus/Cardinal/Finite.g17", 2],
    ["lib/Grace/Cumulus/Cardinal/Hartogs.g17", 2],
    ["lib/Grace/Cumulus/Cardinal/LeastCode.g17", 1],
    ["lib/Grace/Cumulus/Cardinal/Product.g17", 3],
    ["lib/Grace/Cumulus/Cardinal/Sum.g17", 3],
    ["lib/Grace/Cumulus/Algebra/Field/Core.g17", 1],
    ["lib/Grace/Cumulus/Algebra/Group/Product.g17", 3],
    ["lib/Grace/Cumulus/Algebra/Group/Conjugation.g17", 2],
    ["lib/Grace/Cumulus/Algebra/Group/Translation.g17", 1],
    ["lib/Grace/Cumulus/Category/Opposite.g17", 1],
    ["lib/Grace/Cumulus/Category/SetMorphism.g17", 4],
    ["lib/Grace/Cumulus/Metric/Discrete.g17", 2],
    ["lib/Grace/Cumulus/Metric/Product.g17", 1],
    ["lib/Grace/Cumulus/Rat/Operations.g17", 5],
    ["lib/Grace/Cumulus/Real/AbsoluteValue.g17", 1],
    ["lib/Grace/Cumulus/Real/Analysis/Sequences.g17", 1],
    ["lib/Grace/Cumulus/Real/Addition.g17", 1],
    ["lib/Grace/Cumulus/Real/Embedding.g17", 1],
    ["lib/Grace/Cumulus/Real/Inverse.g17", 3],
    ["lib/Grace/Cumulus/Real/Multiplication.g17", 1],
    ["lib/Grace/Cumulus/Real/Negation.g17", 1],
    ["lib/Grace/Cumulus/Real/Uncountable/Final.g17", 1],
    ["lib/Grace/Cumulus/Set/Function.g17", 6],
    ["lib/Grace/Cumulus/Set/Hierarchy.g17", 10],
    ["lib/Grace/Cumulus/Set/Ordinal/Arithmetic.g17", 4],
    ["lib/Grace/Cumulus/Topology/CantorBendixson/Iterate.g17", 2],
    ["lib/Grace/Cumulus/Topology/CantorBendixson/Stabilise.g17", 1],
    ["lib/Grace/Cumulus/Topology/CantorBendixson/Theorem.g17", 1],
  ]);
  const actual = new Map<string, number>();
  for (const file of graceFiles("lib/Grace/Cumulus")) {
    const source = readFileSync(file, "utf8")
      .split("\n")
      .filter(line => !line.trimStart().startsWith("--"))
      .filter(line => !line.includes('notation infixr 72 "↦"'))
      .join("\n");
    const count = [...source.matchAll(/↦/gu)].length;
    if (count > 0) actual.set(file, count);
  }
  assert.deepEqual(actual, expected,
    "use (x, y) for products, relation pairs, and structural encodings; reserve x ↦ y for graph entries");
});
