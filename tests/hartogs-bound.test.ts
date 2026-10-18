// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

const prefix = "Grace.Cumulus.Cardinal.Hartogs.";

test("Hartogs and transported ordinal collapse have complete hereditary ZF audits", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Cardinal/Hartogs.g17"], ["lib"]);
  for (const theorem of ["wellOrderCollapse.on_ordinal", "wellOrderType.on_ordinal",
    "hartogsBound.ordinal", "hartogsBound.not_represented", "hartogsBound.not_order_type",
    "hartogsBound.above_ordinal_subset", "wellOrderType.on_injected_ordinal",
    "hartogsBound.no_injection", "Hartogs.theorem"]) {
    const audit = auditTheoremAxioms(kernel, prefix + theorem);
    assert.equal(audit.complete, true, JSON.stringify(audit.unavailable));
    assert.deepEqual(audit.hereditary.filter(name => /choice|sorry/i.test(name)), [], theorem);
  }
});

test("the public bound applies to the empty carrier and ordinary ordinal subsets", () => {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "HartogsBoundExample.g17", source: `
module HartogsBoundExample
import Grace.Cumulus.Cardinal.Hartogs

theorem empty_below (A : Set)
  shows empty ∈ hartogsBound(A)
proof
  exact hartogsBound.above_ordinal_subset at empty, A with Ordinal.empty, empty.subset at A

theorem ordinal_below (α : Set)
  requires ordinal : α ∈ Ordinal
  shows α ∈ hartogsBound(α)
proof
  have subset := Subset.reflexive at α
  exact hartogsBound.above_ordinal_subset at α, α with *
` }], ["lib"]);
});

test("an arbitrary ordinal cannot be claimed below a bound without the subset premise", () => {
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "HartogsMissing.g17", source: `
module HartogsMissing
import Grace.Cumulus.Cardinal.Hartogs
theorem invalid (α A : Set)
  requires ordinal : α ∈ Ordinal
  shows α ∈ hartogsBound(A)
proof
  exact hartogsBound.above_ordinal_subset at α, A with *
` }], ["lib"]));
});

test("well-order transport requires injectivity, not merely a function", () => {
  const kernel = createZfKernel();
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "TransportMissing.g17", source: `
module TransportMissing
import Grace.Cumulus.Order
theorem invalid (f A B r : Set)
  requires function : FunctionBetween(f, A, B)
  requires order : WellOrder(A, r)
  shows WellOrder(functionImage(f, A, B), transportedOrder(f, A, B, r))
proof
  exact transportedOrder.well_order at f, A, B, r with *
` }], ["lib"]));
});
