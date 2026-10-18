// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";
const source = readFileSync("examples/PolynomialNonvanishing.g17", "utf8");
function load(text: string) {
  const kernel = createZfKernel();
  loadModuleSourceGraph(kernel, [{ file: "PolynomialNonvanishing.g17", source: text }], ["lib"]);
  return kernel;
}

test("multivariate nonvanishing and the integral-localization obstruction are hereditary ZF proofs", () => {
  const kernel = load(source);
  const names = [...kernel.theorems.keys()].filter(n =>
    /^Grace.Cumulus.Algebra.Polynomial.(Nonvanishing|InfiniteFieldLocalization)\./.test(n)
    || /^Grace.Cumulus.Algebra.Field.PrincipalLocalization.(Is)?RingHom\./.test(n)
    || n.startsWith("PolynomialNonvanishing."));
  assert.ok(names.length >= 15);
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /choice|sorry/i.test(a)), [], name);
  }
});

for (const premise of ["field", "infinite", "polynomial", "nonzero", "agreement"]) {
  test(`polynomial nonvanishing and extensionality require ${premise}`, () => {
    const text = source.replace(/section Localizations[\s\S]*?end Localizations/, "")
      .replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "")
      .replace("polynomialAt.exists_nonzero with", "polynomialAt.exists_nonzero at I, A, add, z, neg, mul, one, p with")
      .replace("polynomialAt.ext with", "polynomialAt.ext at I, A, add, z, neg, mul, one, p, q with");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

for (const premise of ["index", "injective", "embedding", "carrier", "target"]) {
  test(`the localization obstruction requires ${premise}`, () => {
    const text = source.replace(/section Polynomials[\s\S]*?end Polynomials/, "")
      .replace(/theorem nonintegral_element[\s\S]*?(?=end Localizations)/, "")
      .replace(new RegExp(`^(?:hypothesis|  requires) ${premise} :.*\\n`, "gm"), "")
      .replace("polynomialLocalization.not_field with", "polynomialLocalization.not_field at I, A, add, z, neg, mul, one, B, plus, o, minus, times, unit, g, s, j, T with");
    assert.throws(() => load(text), /cannot find evidence/);
  });
}

test("nonvanishing and nonintegrality histories survive cached checks with scoped notation", () => {
  for (let i = 0; i < 2; i++) {
    const result = checkWorkbenchFiles([{ name: "PolynomialNonvanishing.g17", source }], "ZF", ["PolynomialNonvanishing.g17"]);
    for (const name of ["nonvanishing", "localization_not_field", "nonintegral_element"]) {
      const theorem = result.theorems.find(t => t.name === `PolynomialNonvanishing.${name}`)!;
      assert.ok(theorem, name);
      assert.ok(theorem.steps.length, name);
    }
    const theorem = result.theorems.find(t => t.name === "PolynomialNonvanishing.nonintegral_element")!;
    assert.match(theorem.statement, /IntegralOver\(identity\(T\), L, S, y\)/);
  }
});
