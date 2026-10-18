// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

test("Konigsberg checks cold, after an edit, and through the public graph entrypoint", () => {
  const file = { name: "GraphTheory/Konigsberg.g17", source: readFileSync("lib/Grace/Cumulus/GraphTheory/Konigsberg.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  file.source += "\n-- edited concrete bridge theorem\n";
  assert.equal(checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false }).ok, true);
  const source = readFileSync("examples/KonigsbergStarter.g17", "utf8");
  assert.equal(checkWorkbenchFiles([{ name: "KonigsbergStarter.g17", source }]).ok, true);
});

test("changing a bridge endpoint invalidates the claimed degree table", () => {
  const original = readFileSync("lib/Grace/Cumulus/GraphTheory/Konigsberg.g17", "utf8");
  const source = original.replace("chooseNat(equalNat(i, 6), 2,", "chooseNat(equalNat(i, 6), 0,");
  assert.notEqual(source, original);
  assert.throws(() => checkWorkbenchFiles([{ name: "GraphTheory/Konigsberg.g17", source }]));
});

test("an even numeral cannot be certified as non-even by the parity proof", () => {
  const original = readFileSync("lib/Grace/Cumulus/Nat/Parity.g17", "utf8");
  const source = original.replace("shows ¬Even(3)", "shows ¬Even(4)");
  assert.throws(() => checkWorkbenchFiles([{ name: "Nat/Parity.g17", source }]));
});

test("bounded defgraph supports no parameters, including conditional generated laws", () => {
  for (const requires of ["", "requires premise : 0 ∈ {0}\n"]) {
    const source = `module NullaryGraph
import Grace.Cumulus.Set.Function
defgraph idZero (x ∈ {0}) : {0} := x
${requires}proof
  exact member

theorem value
  shows idZero[0] = 0
proof
  have member := singleton.self at 0
  exact idZero.value at 0 with *
`;
    assert.equal(checkWorkbenchFiles([{ name: "NullaryGraph.g17", source }]).ok, true);
    assert.throws(() => checkWorkbenchFiles([{ name: "NullaryGraph.g17", source: source.replace(":= x", ":= 1") }]));
  }
});
