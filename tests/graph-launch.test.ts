// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

test("graph counting and Pythagoras survive edited workbench reloads and reject a false variant", () => {
  const files = ["GraphTheory/Counting.g17", "Geometry/Pythagoras.g17"].map(name => ({
    name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8"),
  }));
  for (const file of files) {
    prepareWorkbenchFiles(files, "ZF", file.name);
    assert.equal(checkWorkbenchFiles(files, "ZF", [file.name], { includeKernelDetails: false }).ok, true);
    // Invalidate the leaf cache while retaining unchanged declarations.
    file.source += "\n-- warm edit regression\n";
    assert.equal(checkWorkbenchFiles(files, "ZF", [file.name], { includeKernelDetails: false }).ok, true);
  }
  const broken = files.map(file => file.name === "Geometry/Pythagoras.g17" ? {
    ...file, source: file.source.replace(
      "distanceSquared(a₁, a₂, c₁, c₂) + distanceSquared(b₁, b₂, c₁, c₂)",
      "distanceSquared(a₁, a₂, c₁, c₂)",
    ),
  } : file);
  assert.throws(() => checkWorkbenchFiles(broken, "ZF", ["Geometry/Pythagoras.g17"]), /different normal forms/);
});

test("crossing-edge applications require connectedness and a nontrivial cut", () => {
  const source = `module CutExample
import Grace.Cumulus.GraphTheory.Connectivity
theorem exit (V E A : Set)
  requires connected : GraphConnected(V, E)
  requires included : A ⊆ V
  requires inhabited : Nonempty(A)
  requires proper : A ≠ V
  shows ∃ u ∈ A, ∃ v ∈ V, ¬(v ∈ A) ∧ Adjacent(E, u, v)
proof
  exact GraphConnected.crossing_edge at V, E, A with *
`;
  assert.equal(checkWorkbenchFiles([{ name: "CutExample.g17", source }]).ok, true);
  for (const requirement of [
    "  requires connected : GraphConnected(V, E)\n",
    "  requires inhabited : Nonempty(A)\n",
    "  requires proper : A ≠ V\n",
  ]) assert.throws(() => checkWorkbenchFiles([{ name: "CutExample.g17", source: source.replace(requirement, "") }]),
    /with \* cannot find evidence/);
});
