// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

test("multigraph parity survives cold and edited Workbench checks", () => {
  const file = { name: "GraphTheory/Multigraph.g17", source: readFileSync("lib/Grace/Cumulus/GraphTheory/Multigraph.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  file.source += "\n-- edited parity regression\n";
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
});

test("parallel edges remain distinct and loops count twice", () => {
  const source = readFileSync("examples/MultigraphStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "MultigraphStarter.g17", source }]).ok, true);
  for (const equation of [
    "Multigraph.incidences(leftEnd, rightEnd, edges, x, 2) = 2",
    "Multigraph.incidences(leftEnd, rightEnd, edges, x, 1) = 2",
  ]) {
    const wrong = source.replace(equation, equation.replace("= 2", "= 1"));
    assert.notEqual(wrong, source);
    assert.throws(() => checkWorkbenchFiles([{ name: "MultigraphStarter.g17", source: wrong }]));
  }
});

test("Euler obstruction requires a complete enumeration, distinct vertices, and three degree hypotheses", () => {
  const full = readFileSync("examples/MultigraphStarter.g17", "utf8");
  const theorem = full.slice(full.indexOf("theorem three_noneven"));
  const source = "module Obstruction\nimport Grace.Cumulus.GraphTheory\n" + theorem;
  for (const line of theorem.split("\n").filter(line => line.startsWith("  requires"))) {
    assert.throws(() => checkWorkbenchFiles([{ name: "Obstruction.g17", source: source.replace(line + "\n", "") }]),
      /with \* cannot find evidence/);
  }
});
