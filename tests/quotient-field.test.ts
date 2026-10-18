// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { createSetTheoryKernel, createZfKernel, loadModuleGraph, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";

test("canonical inverses and maximal quotient characterization are exposed in the field quotient module and entirely ZF", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Field/Quotient.g17"], ["lib"]);
  assert.ok(kernel.theorems.has("Grace.Cumulus.Algebra.Field.Quotient.idealQuotient.is_field_iff_maximal"));
  loadModuleGraph(kernel, ["examples/QuotientFieldStarter.g17"], ["lib"]);
  const names = [
    ...["idealAdjoin.ideal", "idealAdjoin.least", "IsMaximalIdeal.bezout"].map(n => `Grace.Cumulus.Algebra.Ring.IdealAdjoin.${n}`),
    ...["fieldInverseValue.exists", "fieldInverseValue.unique", "fieldInverse.function", "fieldInverse.zero", "IsField.field", "IsFieldWithInverse.is_field", "IsField.iff_exists_inverse"].map(n => `Grace.Cumulus.Algebra.Field.Construction.${n}`),
    ...["IsMaximalIdeal.unit_modulo", "idealQuotient.is_field_iff_maximal", "idealQuotient.field_of_maximal"].map(n => `Grace.Cumulus.Algebra.Field.Quotient.${n}`),
    ...["field_iff_maximal", "canonical_field", "inverse_at_zero"].map(n => `QuotientFieldStarter.${n}`),
  ];
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

test("field quotient existence above a proper ideal inherits ordinary AC", () => {
  const kernel = createSetTheoryKernel({ profile: "ZFC" });
  loadModuleGraph(kernel, ["examples/ZornApplications.g17"], ["lib"]);
  const audit = auditTheoremAxioms(kernel, "ZornApplications.exists_field_quotient");
  assert.equal(audit.complete, true);
  assert.deepEqual(audit.hereditary.filter(a => /choice/i.test(a)), ["set.choice"]);
  assert.ok(!audit.hereditary.some(a => /sorry/.test(a)));
});

test("a commutative ring alone cannot supply a field inverse", () => {
  const kernel = createZfKernel();
  loadModuleGraph(kernel, ["lib/Grace/Cumulus/Algebra/Field/Construction.g17"], ["lib"]);
  assert.throws(() => loadModuleSourceGraph(kernel, [{ file: "MissingField.g17", source: `
module MissingField
import Grace.Cumulus.Algebra.Field.Construction
theorem invalid (A add zero neg mul one : Set)
  requires ring : IsCommRing(A, add, zero, neg, mul, one)
  shows IsFieldWithInverse(A, add, zero, neg, mul, one, fieldInverse(A, add, zero, neg, mul, one))
proof
  exact IsField.field at A, add, zero, neg, mul, one with *
` }], ["lib"]), /IsField/);
});
