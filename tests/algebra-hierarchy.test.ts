// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { fileURLToPath } from "node:url";
import { createZfgKernel, loadModuleGraph } from "../src/index.ts";

const root = fileURLToPath(new URL("../lib", import.meta.url));
const algebra = fileURLToPath(new URL("../lib/Grace/Cumulus/Algebra/Foundation.g17", import.meta.url));

test("builds algebraic interfaces from set-theoretic function and relation graphs", () => {
  const kernel = createZfgKernel();
  loadModuleGraph(kernel, [algebra], [root]);
  for (const name of [
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsMagma", "Grace.Cumulus.Algebra.Foundation.Algebra.IsGroup",
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsSemiring", "Grace.Cumulus.Algebra.Foundation.Algebra.IsRing",
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsPartialOrder",
  ]) assert.equal(kernel.predicates.has(name), true, name);
  for (const name of [
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsMonoid.semigroup", "Grace.Cumulus.Algebra.Foundation.Algebra.IsGroup.monoid",
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsSemiring.additive", "Grace.Cumulus.Algebra.Foundation.Algebra.IsSemiring.multiplicative",
    "Grace.Cumulus.Algebra.Foundation.Algebra.IsPartialOrder.preorder",
  ]) kernel.checkProof(kernel.theoremProofs.get(name)!);
});
