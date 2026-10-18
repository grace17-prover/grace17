// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfgKernel, loadModuleSourceGraph } from "../src/index.ts";
import { tacticGuideSections } from "../workbench/tactics-guide.js";

test("definition Help examples are the checked examples, including generated interfaces", () => {
  const source = readFileSync("examples/Definitions.g17", "utf8");
  const entries = tacticGuideSections.flatMap(section => section.entries).filter(entry =>
    entry.forms?.some(form => ["def", "defgraph", "defchoose", "defunique", "predicate", "def.recursive", "datatype",
      "def.separation", "def.replacement", "transfinite", "foundation", "well-founded"].includes(form)));
  for (const entry of entries) assert.ok(source.includes(entry.example), entry.syntax);
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "Definitions.g17", source }], ["lib"]);
  for (const name of ["inclusionMap.closed", "inclusionMap.function", "inclusionMap.value", "selected.exists", "selected.selected", "inclusion_value", "selected_member"])
    assert.ok(kernel.theorems.has(`DefinitionExamples.${name}`), name);
  assert.ok(kernel.definitions.has("DefinitionExamples.rankOn"));
  assert.equal(kernel.recursiveFunctions.has("DefinitionExamples.rankOn"), false);
  for (const [current, old] of [["defgraph", "graphdef"], ["defchoose", "choosedef"]]) {
    const example = entries.find(entry => entry.forms?.includes(current))!.example;
    const legacy = "module RejectedDefinition\n" + example.replaceAll(`${current} `, `${old} `);
    assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "Definitions.g17", source: legacy }], ["lib"]), /expected a module directive/);
  }
  const alias = source.replace("def copies (", "define copies (");
  assert.doesNotThrow(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "Definitions.g17", source: alias }], ["lib"]));
});
