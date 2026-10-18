// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

test("point geometry survives cold and edited workbench checks and rejects a wrong angle", t => {
  const files = ["Geometry/Plane.g17", "Geometry/Isosceles.g17", "Geometry/Circle.g17", "Geometry/Midpoint.g17", "Geometry/Lines.g17", "Geometry/Parallelogram.g17", "Geometry/Centroid.g17", "Geometry/TriangleCenters.g17", "LinearAlgebra/TwoByTwo.g17", "Geometry/Circumcenter.g17"].map(name => ({
    name, source: readFileSync(`lib/Grace/Cumulus/${name}`, "utf8"),
  }));
  for (const file of files) {
    const start = performance.now();
    prepareWorkbenchFiles(files, "ZF", file.name);
    const prepared = performance.now();
    assert.equal(checkWorkbenchFiles(files, "ZF", [file.name], { includeKernelDetails: false }).ok, true);
    const checked = performance.now();
    file.source += "\n-- edited geometry regression\n";
    assert.equal(checkWorkbenchFiles(files, "ZF", [file.name], { includeKernelDetails: false }).ok, true);
    t.diagnostic(`${file.name}: dependencies ${(prepared - start).toFixed(0)} ms; cold ${(checked - prepared).toFixed(0)} ms; edited ${(performance.now() - checked).toFixed(0)} ms`);
  }
  const broken = files.map(file => file.name === "Geometry/Isosceles.g17" ? {
    ...file, source: file.source.replace("shows EqualAngle(c, a, b, c, b, a)",
      "shows EqualAngle(c, a, b, a, c, b)"),
  } : file);
  assert.throws(() => checkWorkbenchFiles(broken, "ZF", ["Geometry/Isosceles.g17"]));
  const wrongLength = files.map(file => file.name === "Geometry/Lines.g17" ? {
    ...file, source: file.source.replace(
      "Euclidean.distanceSquared(m, n) + Euclidean.distanceSquared(m, n) +\n    Euclidean.distanceSquared(m, n) + Euclidean.distanceSquared(m, n)",
      "Euclidean.distanceSquared(m, n) + Euclidean.distanceSquared(m, n) + Euclidean.distanceSquared(m, n)",
    ),
  } : file);
  assert.notEqual(wrongLength.find(file => file.name === "Geometry/Lines.g17")!.source,
    files.find(file => file.name === "Geometry/Lines.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(wrongLength, "ZF", ["Geometry/Lines.g17"]));
  const wrongOrder = files.map(file => file.name === "Geometry/Parallelogram.g17" ? {
    ...file, source: file.source.replace("shows Parallelogram(m, n, p, q)", "shows Parallelogram(m, p, n, q)"),
  } : file);
  assert.notEqual(wrongOrder.find(file => file.name === "Geometry/Parallelogram.g17")!.source,
    files.find(file => file.name === "Geometry/Parallelogram.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(wrongOrder, "ZF", ["Geometry/Parallelogram.g17"]));

  const reversedRatio = files.map(file => file.name === "Geometry/Centroid.g17" ? {
    ...file, source: file.source.replace("shows MedianRatio(a, g, m)", "shows MedianRatio(m, g, a)"),
  } : file);
  assert.notEqual(reversedRatio.find(file => file.name === "Geometry/Centroid.g17")!.source,
    files.find(file => file.name === "Geometry/Centroid.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(reversedRatio, "ZF", ["Geometry/Centroid.g17"]));
  const wrongMedianLength = files.map(file => file.name === "Geometry/Centroid.g17" ? {
    ...file, source: file.source.replace(
      "Euclidean.distanceSquared(g, m) + Euclidean.distanceSquared(g, m) +\n    Euclidean.distanceSquared(g, m) + Euclidean.distanceSquared(g, m)",
      "Euclidean.distanceSquared(g, m) + Euclidean.distanceSquared(g, m) + Euclidean.distanceSquared(g, m)",
    ),
  } : file);
  assert.notEqual(wrongMedianLength.find(file => file.name === "Geometry/Centroid.g17")!.source,
    files.find(file => file.name === "Geometry/Centroid.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(wrongMedianLength, "ZF", ["Geometry/Centroid.g17"]));
  const reversedEulerRatio = files.map(file => file.name === "Geometry/TriangleCenters.g17" ? {
    ...file, source: file.source.replace(
      "shows MedianRatio(orthocenter(o, a, b, c), g, o)",
      "shows MedianRatio(o, g, orthocenter(o, a, b, c))",
    ),
  } : file);
  assert.notEqual(reversedEulerRatio.find(file => file.name === "Geometry/TriangleCenters.g17")!.source,
    files.find(file => file.name === "Geometry/TriangleCenters.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(reversedEulerRatio, "ZF", ["Geometry/TriangleCenters.g17"]));
  // A singular system or collinear triangle must not receive the
  // nonsingularity evidence required by the public API.
  for (const [name, source] of [
    ["MissingDeterminant", `
import Grace.Cumulus.LinearAlgebra.TwoByTwo
theorem unsupported (a b c d u v : Real)
  shows a * LinearSystem2.solutionX(a, b, c, d, u, v) + b * LinearSystem2.solutionY(a, b, c, d, u, v) = u ∧
    c * LinearSystem2.solutionX(a, b, c, d, u, v) + d * LinearSystem2.solutionY(a, b, c, d, u, v) = v
proof
  exact LinearSystem2.correct at a, b, c, d, u, v with *
`],
    ["MissingNoncollinearity", `
import Grace.Cumulus.Geometry
theorem unsupported (a b c : Euclidean.Point)
  shows ∃ o, Euclidean.Point(o) ∧ Euclidean.Circumcenter(o, a, b, c)
proof
  exact Euclidean.circumcenter.exists at a, b, c with *
`],
    ["MissingUniquenessCondition", `
import Grace.Cumulus.Geometry
theorem unsupported (a b c o p : Euclidean.Point)
  requires first : Euclidean.Circumcenter(o, a, b, c)
  requires second : Euclidean.Circumcenter(p, a, b, c)
  shows o = p
proof
  exact Euclidean.circumcenter.unique at a, b, c, o, p with *
`],
  ]) {
    assert.throws(() => checkWorkbenchFiles([{ name: `${name}.g17`,
      source: `module ${name}\n${source}
namespace ${name}\n${source}

end ${name}\n${source}
` }], "ZF", [`${name}.g17`]),
      /with \* cannot find evidence/);
  }
  const wrongCramerSign = files.map(file => file.name === "LinearAlgebra/TwoByTwo.g17" ? {
    ...file, source: file.source.replace("(d * u - b * v)", "(d * u + b * v)"),
  } : file);
  assert.notEqual(wrongCramerSign.find(file => file.name === "LinearAlgebra/TwoByTwo.g17")!.source,
    files.find(file => file.name === "LinearAlgebra/TwoByTwo.g17")!.source);
  assert.throws(() => checkWorkbenchFiles(wrongCramerSign, "ZF", ["LinearAlgebra/TwoByTwo.g17"]));

  const missingCenter = (requirement: string) => [{ name: "MissingCenter.g17", source: `
module MissingCenter
namespace MissingCenter
import Grace.Cumulus.Geometry
theorem unsupported_centers (o a b c g : Euclidean.Point)
  ${requirement}
  shows ∃ h, Euclidean.Point(h) ∧ Euclidean.Orthocenter(h, a, b, c) ∧
    Euclidean.Collinear(h, g, o) ∧ Euclidean.MedianRatio(h, g, o)
proof
  exact Euclidean.euler_line at o, a, b, c, g with *

end MissingCenter
` }];
  for (const requirement of [
    "requires center : Euclidean.Centroid(g, a, b, c)",
    "requires circle : Euclidean.Circumcenter(o, a, b, c)",
  ]) {
    assert.throws(() => checkWorkbenchFiles(missingCenter(requirement), "ZF", ["MissingCenter.g17"]),
      /with \* cannot find evidence/);
  }

  const absentMidpoint = [{ name: "MissingMidpoint.g17", source: `
module MissingMidpoint
namespace MissingMidpoint
import Grace.Cumulus.Geometry
theorem arbitrary_point_is_not_a_median (a b c g m : Euclidean.Point)
  requires center : Euclidean.Centroid(g, a, b, c)
  shows Euclidean.MedianRatio(a, g, m)
proof
  exact Euclidean.centroid.median_ratio at a, b, c, g, m with *

end MissingMidpoint
` }];
  assert.throws(() => checkWorkbenchFiles(absentMidpoint, "ZF", ["MissingMidpoint.g17"]),
    /with \* cannot find evidence/);

  const absentDiagonals = [{ name: "MissingDiagonals.g17", source: `
module MissingDiagonals
namespace MissingDiagonals
import Grace.Cumulus.Geometry

theorem collapsed_is_not_a_parallel_figure (a : Euclidean.Point)
  shows Euclidean.ParallelSegments(a, a, a, a) ∧ Euclidean.ParallelSegments(a, a, a, a)
proof
  have middle : Euclidean.Midpoint(a, a, a)
    unfold Euclidean.Midpoint
    constructor
    . rfl
    . rfl
  exact Euclidean.varignon.parallel at a, a, a, a, a, a, a, a with *

end MissingDiagonals
` }];
  assert.throws(() => checkWorkbenchFiles(absentDiagonals, "ZF", ["MissingDiagonals.g17"]));

});

test("orthocenter uniqueness requires noncollinearity", () => {
  const source = `module OrthocenterGuard
import Grace.Cumulus.Geometry
namespace Test
theorem unique (a b c h k : Euclidean.Point)
  requires first : Euclidean.Orthocenter(h, a, b, c)
  requires second : Euclidean.Orthocenter(k, a, b, c)
  shows h = k
proof
  exact Euclidean.orthocenter.unique at a, b, c, h, k with *
end Test
`;
  assert.throws(() => checkWorkbenchFiles([{ name: "OrthocenterGuard.g17", source }]),
    /with \* cannot find evidence/);
  const valid = source.replace("  requires first", "  requires triangle : ¬Euclidean.Collinear(a, b, c)\n  requires first");
  assert.equal(checkWorkbenchFiles([{ name: "OrthocenterGuard.g17", source: valid }]).ok, true);
});
