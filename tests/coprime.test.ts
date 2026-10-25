// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { checkWorkbenchFiles, prepareWorkbenchFiles } from "../src/workbench.ts";

const header = "module CoprimeRegression\nimport Grace.Cumulus.NumberTheory\n";
const check = (source: string) => checkWorkbenchFiles([{ name: "CoprimeRegression.g17", source }]);
const integer = (n: number) => `${n < 0 ? "integerNegativeOfNat" : "integerOfNat"}(${Math.abs(n)})`;

test("the public coprime example proves cancellation, inverse existence, uniqueness, and a concrete inverse", () => {
  assert.equal(checkWorkbenchFiles([{ name: "CoprimeStarter.g17", source: readFileSync("examples/CoprimeStarter.g17", "utf8") }]).ok, true);
});

test("coprimality and inverse existence cover signs and zero or unit moduli", () => {
  let source = header;
  for (const [i, [a, m]] of [[3, 11], [-3, 11], [3, -11], [-3, -11], [0, 1], [1, 0], [-1, 0], [37, 1]].entries()) {
    const x = integer(a), modulus = integer(m);
    source += `theorem coprime_${i}
  shows IntegerCoprime(${x}, ${modulus})
proof
  unfold IntegerCoprime
  simp [integerGCD, integerNatAbs.ofNat, integerNatAbs.ofNegativeNat]

theorem inverse_${i}
  shows ∃ u, Integer(u) ∧ IntegerCongruent(${modulus}, ${x} * u, integerOne)
proof
  have coprime := coprime_${i}
  exact IntegerCoprime.modular_inverse at ${x}, ${modulus} with *
`;
  }
  assert.equal(check(source).ok, true);
});

test("noncoprime inputs cannot acquire an inverse through the converse", () => {
  let source = header;
  for (const [i, [a, m, g]] of [[6, 9, 3], [-6, 9, 3], [0, 0, 0], [0, 2, 2]].entries()) {
    const x = integer(a), modulus = integer(m);
    source += `theorem no_inverse_${i} (u : Integer)
  shows ¬ IntegerCongruent(${modulus}, ${x} * u, integerOne)
proof
  have actual : integerGCD(${x}, ${modulus}) = ${g}
  . simp [integerGCD, integerNatAbs.ofNat, integerNatAbs.ofNegativeNat]
  have impossible : ${g} ≠ 1
  . intro equal
    have less : ${g === 0 ? "0 < 1" : `1 < ${g}`}
    . arith
    rw equal at less
    have irreflexive := Less.irreflexive at 1 with *
    exact irreflexive with less
  intro inverse
  have coprime := IntegerCoprime.of_modular_inverse at ${x}, ${modulus}, u with *
  unfold IntegerCoprime at coprime
  rw actual at coprime
  exact impossible with coprime
`;
  }
  assert.equal(check(source).ok, true);
});

test("coprime cancellation requires its coprimality and carrier premises", () => {
  for (const type of ["Integer", "Set"]) assert.throws(() => check(header + `
theorem invalid (a b c : ${type})
  requires product : IntegerDivides(a, b * c)
  shows IntegerDivides(a, c)
proof
  exact IntegerCoprime.cancel at a, b, c with *
`));
});

test("incorrect inverse arithmetic and equality instead of congruence are rejected", () => {
  const example = readFileSync("examples/CoprimeStarter.g17", "utf8");
  assert.throws(() => checkWorkbenchFiles([{ name: "CoprimeStarter.g17", source: example.replace("have difference : 12 = 1 + 11 * 1", "have difference : 12 = 1 + 11 * 2") }]));
  assert.throws(() => check(header + `
theorem too_strong (m a u v : Integer)
  requires first : IntegerCongruent(m, a * u, integerOne)
  requires second : IntegerCongruent(m, a * v, integerOne)
  shows u = v
proof
  exact IntegerCongruent.inverse_unique at m, a, u, v with *
`));
});

test("coprime proofs retain intermediate goals on cold and edited checks", () => {
  const file = { name: "NumberTheory/Coprime.g17", source: readFileSync("lib/Grace/Cumulus/NumberTheory/Coprime.g17", "utf8") };
  prepareWorkbenchFiles([file], "ZFG", file.name);
  for (const suffix of ["", "\n-- edit\n"]) {
    file.source += suffix;
    const result = checkWorkbenchFiles([file], "ZFG", [file.name], { includeKernelDetails: false });
    assert.equal(result.ok, true);
    const proof = result.theorems.find(t => t.name.endsWith("IntegerCoprime.cancel"));
    assert.ok(proof?.steps.some(s => s.after.goals.length > 0));
    assert.equal(proof?.steps.at(-1)?.after.goals.length, 0);
  }
});
