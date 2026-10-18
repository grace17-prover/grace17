// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { checkWorkbenchFiles } from "../src/workbench.ts";
import { forbiddenTacticUsed, levelSource, worlds } from "../workbench/game-levels.js";

// Every level of the Set Theory Game is a real theorem: the starter proof
// checks modulo its sorry, and the solution checks with no sorry at all.
test("every Set Theory Game level has a checked solution and a starter with a hole", () => {
  const ids = new Set<string>();
  for (const world of worlds) {
    assert.ok(world.levels.length > 0, `${world.id} has levels`);
    for (const level of world.levels) {
      const id = `${world.id}.${level.id}`;
      assert.ok(!ids.has(id), `${id} is unique`);
      ids.add(id);
      assert.ok(level.hints.length > 0, `${id} has hints`);
      assert.equal(forbiddenTacticUsed(level, level.solution), undefined, `${id} solution respects the switched-off tactics`);
      const name = `${world.id}-${level.id}.g17`;
      for (const [mode, proof] of [["starter", level.starter], ["solution", level.solution]] as const) {
        const source = levelSource(world, level, proof);
        const result = checkWorkbenchFiles([{ name, source }], "ZFG", [name], { includeKernelDetails: false });
        assert.equal(result.ok, true, `${id} ${mode}: ${result.message}`);
        const sorries = result.theorems.flatMap((theorem: { sorries?: unknown[] }) => theorem.sorries ?? []).length;
        if (mode === "solution") assert.equal(sorries, 0, `${id} solution leaves ${sorries} sorry`);
        else assert.ok(sorries > 0, `${id} starter has no hole`);
      }
    }
  }
});
