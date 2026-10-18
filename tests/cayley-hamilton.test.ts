// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// The bundled matrix ring, Cramer's rule, the adjugate inverse, and the
// Cayley–Hamilton theorem: the statements elaborate in the textbook
// notation, every proof is admission-free ZF, and the hypotheses of the
// rules are needed.

import test from "node:test";
import assert from "node:assert/strict";
import { createZfKernel, loadModuleSourceGraph, auditTheoremAxioms } from "../src/index.ts";
import { checkWorkbenchFiles } from "../src/workbench.ts";

const header = "module CayleyHamiltonChecks\nimport Grace.Cumulus.Algebra.Ring.CayleyHamilton\n";

function load(source: string) {
  const kernel = createZfKernel();
  const modules = loadModuleSourceGraph(kernel, [{ file: "CayleyHamiltonChecks.g17", source }], ["lib"]);
  assert.equal(modules.flatMap(m => m.sorries).length, 0);
  return kernel;
}

function check(source: string) {
  const result = checkWorkbenchFiles([{ name: "CayleyHamiltonChecks.g17", source }]);
  assert.equal(result.ok, true, JSON.stringify(result).slice(0, 800));
  return result;
}

const statement = (result: ReturnType<typeof check>, name: string): string =>
  result.theorems.find(item => item.name.endsWith(name))!.statement;

const section = (body: string) => header + `
section Checks
variable (R : Set) (n : Nat)
hypothesis comm : CommRing(R)
${body}
end Checks
`;

test("the matrix ring, Cramer's rule, and Cayley–Hamilton are admission-free ZF", t => {
  const kernel = load(header);
  const names = [...kernel.theorems.keys()].filter(name =>
    /^Grace\.Cumulus\.Algebra\.Ring\.(MatrixRing|MatrixEntries|MatrixCramer|Bicommutant|MatrixPolynomial|CayleyHamilton)\./.test(name));
  assert.ok(names.length >= 150, `${names.length} entries`);
  for (const key of ["CayleyHamilton.Matrix.cayley_hamilton", "MatrixCramer.Matrix.cramer",
    "MatrixCramer.Matrix.mul_inverse", "MatrixCramer.Matrix.mul_adj", "MatrixRing.matrixRing.ring"]) {
    assert.ok(names.some(name => name.endsWith(key)), key);
  }
  for (const name of names) {
    const audit = auditTheoremAxioms(kernel, name);
    assert.equal(audit.complete, true, name);
    assert.deepEqual(audit.hereditary.filter(a => /sorry|choice/i.test(a)), [], name);
  }
  t.diagnostic(`${names.length} theorem entries audited`);
});

test("the statements read in the bundled matrix notation", () => {
  const result = check(section(`
theorem checks.cayley_hamilton (M : R ^ n × n)
  shows evalAt(M)(charpoly(M)) = matrixRing(R, n)[0]
proof
  exact Matrix.cayley_hamilton with *

theorem checks.cramer (M N : R ^ n × n) (x b i : Set)
  requires vector : x : n → R.carrier
  requires solution : ∀ j ∈ n, rowProduct(R, n, x, M)(j) = b(j)
  requires row : i ∈ n
  requires replaced : ∀ j ∈ n, N[i, j] = b(j)
  requires outside : ∀ k ∈ n, k ≠ i → ∀ j ∈ n, N[k, j] = M[k, j]
  shows det(M) * x(i) = det(N)
proof
  exact Matrix.cramer with *

theorem checks.inverse (M : R ^ n × n) (u : R)
  requires inverse : u * det(M) = R[1]
  shows M * scalarMultiple(R, n, u, adj(M)) = matrixRing(R, n)[1]
proof
  exact Matrix.mul_inverse with *

theorem checks.ring_laws (M N P : R ^ n × n)
  shows M * (N + P) = M * N + M * P ∧ M * N * P = M * (N * P)
proof
  have ring := matrixRing.ring at R, n with *
  have parts := Ring.parts with ring
  have distributive := IsRing.distributive with parts
  have monoid := IsRing.multiplicative with parts
  have assoc := IsMonoid.associative with monoid
  have hM : M ∈ Ring.carrier(matrixRing(R, n)) by assumption
  have hN : N ∈ Ring.carrier(matrixRing(R, n)) by assumption
  have hP : P ∈ Ring.carrier(matrixRing(R, n)) by assumption
  have law := distributive with M, hM, N, hN, P, hP
  have associative := assoc with M, hM, N, hN, P, hP
  exact ⟨law.left, associative⟩
`));
  assert.match(statement(result, "checks.cayley_hamilton"), /evalAt\(M\)\(charpoly\(M\)\) = (matrixRing\(R, n\)\[0\]|Ring\.zero\(matrixRing\(R, n\)\))/);
  assert.match(statement(result, "checks.cramer"), /det\(M\) \* (x\(i\)|xᵢ) = det\(N\)/);
  assert.match(statement(result, "checks.inverse"), /M \* scalarMultiple\(R, n, u, adj\(M\)\) = (matrixRing\(R, n\)\[1\]|Ring\.one\(matrixRing\(R, n\)\))/);
});

for (const [label, pattern] of [
  ["the solution equation", /^  requires solution :.*\n/m],
  ["the replaced row", /^  requires replaced :.*\n/m],
  ["the unchanged rows", /^  requires outside :.*\n/m],
] as const) {
  test(`Cramer's rule needs ${label}`, () => {
    const source = section(`
theorem checks.cramer (M N : R ^ n × n) (x b i : Set)
  requires vector : x : n → R.carrier
  requires solution : ∀ j ∈ n, rowProduct(R, n, x, M)(j) = b(j)
  requires row : i ∈ n
  requires replaced : ∀ j ∈ n, N[i, j] = b(j)
  requires outside : ∀ k ∈ n, k ≠ i → ∀ j ∈ n, N[k, j] = M[k, j]
  shows det(M) * x(i) = det(N)
proof
  exact Matrix.cramer with *
`);
    const changed = source.replace(pattern, "");
    assert.notEqual(changed, source);
    assert.throws(() => checkWorkbenchFiles([{ name: "CayleyHamiltonChecks.g17", source: changed }]));
  });
}

test("the inverse needs the unit equation and the zero matrix is not the identity", () => {
  assert.throws(() => checkWorkbenchFiles([{ name: "CayleyHamiltonChecks.g17", source: section(`
theorem checks.inverse (M : R ^ n × n) (u : R)
  shows M * scalarMultiple(R, n, u, adj(M)) = matrixRing(R, n)[1]
proof
  exact Matrix.mul_inverse with *
`) }]));
  assert.throws(() => checkWorkbenchFiles([{ name: "CayleyHamiltonChecks.g17", source: section(`
theorem checks.cayley_hamilton (M : R ^ n × n)
  shows evalAt(M)(charpoly(M)) = matrixRing(R, n)[1]
proof
  exact Matrix.cayley_hamilton with *
`) }]));
});
