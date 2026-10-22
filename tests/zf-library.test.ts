// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, theoremDependencies } from "../src/index.ts";

test("the ordinary mathematics imports and every migrated selection law check under ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, [
    "Int", "NumberTheory", "Cardinal", "Geometry", "LinearAlgebra", "GraphTheory",
    // Group theory up to Lagrange's theorem, Sylow's theorems, and the free group load under ZF;
    // only CosetSplit (a chosen coset representative) and Paradox (orbit representatives) select.
    "Algebra/Group/Lagrange", "Algebra/Group/Sylow", "Algebra/Group/GroupOrder", "Algebra/Group/Abelian",
    "Algebra/Group/FirstIsomorphism", "Algebra/Group/Product", "Algebra/Group/FreeGroup",
    // Combinatorics loads under ZF except the infinite Ramsey theorem (RamseyChain, RamseyInfinite).
    "Combinatorics/Multinomial", "Combinatorics/ErdosSzekeres", "Combinatorics/DerangementCount",
    "Combinatorics/DerangementFormula", "Combinatorics/MoebiusInversion", "Combinatorics/MoebiusMultiplicative",
    "Combinatorics/CoprimeDivisors", "NumberTheory/FibonacciGCD",
    // Point-set topology through bases, the real line, Heine–Borel, and Cantor–Bendixson loads under ZF;
    // only the chosen originals of a cover (CompactImage, CompactMore, Tube) and what imports them select.
    "Topology/CantorBendixson", "Topology/Real/RationalBase", "Topology/HeineBorel",
  ].map(name => `lib/Grace/Cumulus/${name}.g17`), ["lib"]);
  assert.equal(kernel.axioms.has("set.globalChoice"), false);
  for (const name of [
    "Grace.Cumulus.Cardinal.Enumeration.cardinality",
    "Grace.Cumulus.Set.Indicator.indicator",
    "Grace.Cumulus.Geometry.Plane.Euclidean.coordinateX", "Grace.Cumulus.Geometry.Plane.Euclidean.coordinateY",
    "Grace.Cumulus.LinearAlgebra.Matrix.matrixFirstIndex",
    "Grace.Cumulus.LinearAlgebra.Matrix.matrixSecondIndex",
    "Grace.Cumulus.LinearAlgebra.Matrix.diagonalCoefficient",
  ]) {
    for (const law of ["exists", "unique", "selected"]) {
      assert.ok(kernel.theorems.has(`${name}.${law}`), `${name}.${law}`);
    }
  }
  for (const name of kernel.theorems.keys()) {
    assert.deepEqual(theoremDependencies(kernel, name).axioms.filter(a => /choice/i.test(a)), [], name);
  }
});
