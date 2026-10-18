// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import assert from "node:assert/strict";
import test from "node:test";
import { createZfKernel, moduleReport } from "../src/index.ts";
import { loadModuleSourceGraphResolved } from "../src/module-source-loader.ts";
import { importCandidates, moduleNameFromPath } from "../src/module-names.ts";

const inner = `module Inner
import Grace.Cumulus.Set.Core

theorem pair.left_in (x y : Set)
  shows x ∈ {x, y}
proof
  simp
`;

function load(files: readonly { file: string; source: string }[]) {
  const kernel = createZfKernel();
  const byName = new Map<string, { file: string; source: string }>();
  for (const item of files) {
    const name = moduleNameFromPath(item.file, ["root"]);
    if (name) byName.set(name, item);
  }
  loadModuleSourceGraphResolved(kernel, files, files.map(item => item.file),
    name => byName.get(name), [], file => moduleNameFromPath(file, ["root", "lib"]));
  return kernel;
}

test("a bare module name is qualified by the file's path and exports its own namespace", () => {
  const kernel = load([
    { file: "root/Demo/Inner.g17", source: inner },
    { file: "root/Demo/Outer.g17", source: `module Outer
import Inner

theorem use (a b : Set)
  shows a ∈ {a, b}
proof
  exact pair.left_in at a, b

theorem use_qualified (a b : Set)
  shows a ∈ {a, b}
proof
  exact Demo.Inner.pair.left_in at a, b
` },
  ]);
  const names = moduleReport(kernel).map(item => item.name);
  assert.ok(names.includes("Demo.Inner"));
  assert.ok(names.includes("Demo.Outer"));
  assert.ok(moduleReport(kernel).find(item => item.name === "Demo.Inner")!.theorems.includes("Demo.Inner.pair.left_in"));
});

test("relative imports resolve innermost first, then through the enclosing namespaces", () => {
  assert.deepEqual(importCandidates("Grace.Cumulus.FixedPoint.NashMap", "WeightedSums"), [
    "Grace.Cumulus.FixedPoint.NashMap.WeightedSums",
    "Grace.Cumulus.FixedPoint.WeightedSums",
    "Grace.Cumulus.WeightedSums",
    "Grace.WeightedSums",
    "WeightedSums",
  ]);
  const kernel = load([
    { file: "root/Demo/Inner.g17", source: inner },
    { file: "root/Demo.g17", source: `module Demo
import Inner
` },
  ]);
  assert.deepEqual(moduleReport(kernel).find(item => item.name === "Demo")!.imports, ["Demo.Inner"]);
});

test("the module's own namespace may still be opened and closed explicitly", () => {
  const kernel = load([{ file: "root/Demo/Inner.g17", source: `module Inner
namespace Demo.Inner
import Grace.Cumulus.Set.Core

theorem pair.left_in (x y : Set)
  shows x ∈ {x, y}
proof
  simp

end Demo.Inner
` }]);
  assert.ok(moduleReport(kernel).find(item => item.name === "Demo.Inner")!.theorems.includes("Demo.Inner.pair.left_in"));
});

test("a bare module name must match the file", () => {
  assert.throws(() => load([{ file: "root/Demo/Inner.g17", source: inner.replace("module Inner", "module Elsewhere") }]),
    /does not match its file/);
});

test("qualified module declarations keep their explicit namespaces", () => {
  const kernel = load([{ file: "root/Demo/Legacy.g17", source: `module Demo.Legacy
namespace Demo.Legacy
import Grace.Cumulus.Set.Core
export open Demo.Legacy

theorem pair.left_in (x y : Set)
  shows x ∈ {x, y}
proof
  simp

end Demo.Legacy
` }]);
  assert.ok(moduleReport(kernel).find(item => item.name === "Demo.Legacy")!.theorems.includes("Demo.Legacy.pair.left_in"));
});

test("a root-anchored namespace is shared across modules", () => {
  const kernel = load([
    { file: "root/Geo/Plane.g17", source: `module Plane
import Grace.Cumulus.Set.Core

namespace _root_.Euclidean
export open _root_.Euclidean

theorem pair.left_in (x y : Set)
  shows x ∈ {x, y}
proof
  simp

end Euclidean
` },
    { file: "root/Geo/Use.g17", source: `module Use
import Plane

namespace _root_.Euclidean

theorem use (a b : Set)
  shows a ∈ {a, b}
proof
  exact pair.left_in at a, b

end Euclidean
` },
  ]);
  assert.ok(moduleReport(kernel).find(item => item.name === "Geo.Plane")!.theorems.includes("Euclidean.pair.left_in"));
  assert.ok(moduleReport(kernel).find(item => item.name === "Geo.Use")!.theorems.includes("Euclidean.use"));
});

test("module names from paths", () => {
  assert.equal(moduleNameFromPath("lib/Grace/Cumulus/Real/FiniteSum.g17", ["lib"]), "Grace.Cumulus.Real.FiniteSum");
  assert.equal(moduleNameFromPath("/home/x/repo/lib/Grace/Cumulus.g17", ["lib"]), "Grace.Cumulus");
  assert.equal(moduleNameFromPath("/home/x/repo/lib/Grace/Cumulus.g17", ["/home/x/repo/lib"]), "Grace.Cumulus");
  assert.equal(moduleNameFromPath("notes.txt", ["lib"]), undefined);
});
