// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import { mkdtempSync, readFileSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import assert from "node:assert/strict";
import { createZfgKernel, loadModuleSourceGraph, exportTheoremForMachine, compileProofModule, verifyProofMachine, encodeProofMachineBinary, exportKernelEnvironment } from "../src/index.ts";

const header = `module RingContext
namespace RingContext
import Grace.Cumulus.Algebra.OrderedAdditive

`;
const statement = ` (A add zero neg mul one x y z : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  requires equality : call2(add, x, y) = z
`;

test("ring reuses local equalities modulo checked commutative-ring normalization", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header +
    `theorem forward${statement}
  shows call2(add, y, x) = call2(add, zero, z)
proof
  ring

theorem backward${statement}
  shows call2(add, zero, z) = call2(add, y, x)
proof
  ring
` + "\nend RingContext\n" }], ["lib"]);
  for (const name of ["RingContext.forward", "RingContext.backward"]) {
    const artifact = exportTheoremForMachine(kernel, name);
    assert.doesNotThrow(() => verifyProofMachine(kernel, compileProofModule([artifact])));
  }
});

test("ring does not treat an unrelated local equality as the desired equality", () => {
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "RingContext.g17", source: header +
    `theorem false_claim${statement}
  shows call2(add, y, y) = z
proof
  ring
` + "\nend RingContext\n" }], ["lib"]), /different normal forms/);
});

test("ring cancels all repeated opposite monomials, including at the end of a sum", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header + `
theorem repeated (A add zero neg mul one x z : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hz : z ∈ A
  shows call2(add, call2(add, x, x), call2(add, neg(x), neg(x))) = zero
proof
  ring

theorem trailing (A add zero neg mul one x z : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hz : z ∈ A
  shows call2(add, z, call2(add, call2(add, x, x), call2(add, neg(x), neg(x)))) = z
proof
  ring
` + "\nend RingContext\n" }], ["lib"]);
  for (const name of ["RingContext.repeated", "RingContext.trailing"]) {
    assert.doesNotThrow(() => verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, name)])));
  }
});

test("linear_combination uses the selected ring, cancels common terms, and replays", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header + `
theorem subtract${statement}
  shows x = call2(add, z, neg(y))
proof
  linear_combination equality

theorem scaled${statement}
  shows call2(mul, x, call2(add, y, x)) = call2(mul, x, z)
proof
  linear_combination x * equality

theorem negative${statement}
  shows call2(add, z, neg(x)) = y
proof
  linear_combination -equality
` + "\nend RingContext\n" }], ["lib"]);
  for (const name of ["subtract", "scaled", "negative"]) {
    assert.doesNotThrow(() => verifyProofMachine(kernel,
      compileProofModule([exportTheoremForMachine(kernel, `RingContext.${name}`)])));
  }
});

test("ring linear_combination rejects a wrong coefficient and missing membership", () => {
  for (const [goal, combination, extra] of [
    ["call2(add, x, x) = z", "equality", ""],
    ["call2(mul, zero, x) = call2(mul, zero, z)", "x * equality", ""],
    ["call2(mul, k, call2(add, x, y)) = call2(mul, k, z)", "k * equality", " k"],
  ]) {
    const params = statement.replace("x y z : Set", `x y z${extra} : Set`);
    assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{
      file: "RingContext.g17", source: header + `theorem rejected${params}
  shows ${goal}
proof
  linear_combination ${combination}
` + "\nend RingContext\n",
    }], ["lib"]));
  }
});


test("the original expanded midsegment calculation keeps a bounded replayable certificate", () => {
  const kernel = createZfgKernel();
  const source = readFileSync("tests/fixtures/polynomial-midsegment.g17", "utf8");
  loadModuleSourceGraph(kernel, [{ file: "PolynomialRegression.g17", source }], ["lib"]);
  const program = compileProofModule([
    exportTheoremForMachine(kernel, "PolynomialRegression.original_midsegment_length"),
  ]);
  // A structural performance gate avoids timing assertions on shared runners.
  // This exercises the original expanded calculation; the factored library proof
  // is covered by the library tests.
  assert.ok(program.code.length < 9000, `${program.code.length} instructions`);
  assert.doesNotThrow(() => verifyProofMachine(kernel, program));
  const directory = mkdtempSync(join(tmpdir(), "g17-polynomial-"));
  try {
    const machine = join(directory, "proof.g17m");
    const environment = join(directory, "proof.g17env");
    writeFileSync(machine, encodeProofMachineBinary(program));
    writeFileSync(environment, JSON.stringify(exportKernelEnvironment(kernel)));
    const checked = spawnSync("python3", ["checkers/python/g17check.py", machine,
      "--environment", environment, "--json"], { encoding: "utf8" });
    assert.equal(checked.status, 0, checked.stderr);
    assert.equal(JSON.parse(checked.stdout).theorems, 1);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
});

test("signed normalization preserves residual terms and fresh law parameters", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header + `
theorem signed (A add zero neg mul one __ring_arg0 y z : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : __ring_arg0 ∈ A
  requires hy : y ∈ A
  requires hz : z ∈ A
  shows neg(call2(add, call2(add, __ring_arg0, y), call2(add, neg(__ring_arg0), z))) =
    call2(add, neg(y), neg(z))
proof
  ring
` + "\nend RingContext\n" }], ["lib"]);
  const program = compileProofModule([exportTheoremForMachine(kernel, "RingContext.signed")]);
  assert.doesNotThrow(() => verifyProofMachine(kernel, program));
});


test("ring_nf normalizes ideal membership without treating the containing set as a scalar", () => {
  const kernel = createZfgKernel();
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header + `
theorem membership (A add zero neg mul one I x y : Set)
  requires structure : IsCommRing(A, add, zero, neg, mul, one)
  requires hx : x ∈ A
  requires hy : y ∈ A
  requires member : call2(add, x, y) ∈ I
  shows call2(add, y, x) ∈ I
proof
  ring_nf at member
  ring_nf
  exact member
end RingContext
` }], ["lib"]);
  verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, "RingContext.membership")]));
});

test("polynomial carrier selection prefers outer operations over operations inside opaque map arguments", () => {
  const kernel = createZfgKernel();
  const context = ` (f A add zero neg mul one B plus z minus times unit x : Set)
  requires source : IsCommRing(A, add, zero, neg, mul, one)
  requires target : IsCommRing(B, plus, z, minus, times, unit)
  requires hx : x ∈ A
  requires fx : f(x) ∈ B
  requires fn : f(neg(x)) ∈ B
`;
  loadModuleSourceGraph(kernel, [{ file: "RingContext.g17", source: header + `
theorem map_neg${context}
  requires equation : z = call2(plus, f(neg(x)), f(x))
  shows f(neg(x)) = minus(f(x))
proof
  linear_combination -equation

theorem opaque_atom${context}
  shows f(neg(x)) = call2(plus, z, f(neg(x)))
proof
  ring

theorem opaque_membership${context}
  requires member : f(neg(x)) ∈ B
  shows call2(plus, z, f(neg(x))) ∈ B
proof
  ring_nf
  exact member
end RingContext
` }], ["lib"]);
  for (const name of ["map_neg", "opaque_atom", "opaque_membership"]) {
    verifyProofMachine(kernel, compileProofModule([exportTheoremForMachine(kernel, `RingContext.${name}`)]));
  }
});

test("outer-ring selection still requires membership of opaque polynomial atoms", () => {
  assert.throws(() => loadModuleSourceGraph(createZfgKernel(), [{ file: "RingContext.g17", source: header + `
theorem missing_atom (f A add zero neg mul one B plus z minus times unit x : Set)
  requires source : IsCommRing(A, add, zero, neg, mul, one)
  requires target : IsCommRing(B, plus, z, minus, times, unit)
  requires hx : x ∈ A
  shows f(neg(x)) = call2(plus, z, f(neg(x)))
proof
  ring
end RingContext
` }], ["lib"]), /could not establish.*∈ B/);
});
