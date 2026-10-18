// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import { spawnSync } from "node:child_process";
import {
  and, andElimLeft, andElimRight, andIntro, app, assume, axiom, bottom,
  compileProofMachine, compileProofModule, createZfgKernel, dne, encodeProofMachineBinary, eq, eqElim,
  exists, existsElim, existsIntro, exportKernelEnvironment, exportTheorem,
  falseElim, forall, forallIntro, iffElimLeft, iffIntro, imp, impElim, impIntro, induction,
  or, orElim, orIntroLeft, orIntroRight, pred, refl, v, verifyProofMachine, wellFoundedInduction,
} from "../src/index.ts";

const project = fileURLToPath(new URL("..", import.meta.url));
const checker = join(project, "checkers/python/g17check.py");

function runPython(machine: string, environment: string) {
  return spawnSync("python3", [checker, machine, "--environment", environment, "--json"], {
    cwd: project, encoding: "utf8",
  });
}

test("independent Python checker verifies surface arithmetic and sets", () => {
  for (const source of ["examples/Arithmetic.g17", "examples/Sets.g17", "lib/Grace/Core/Data.g17"]) {
    const directory = mkdtempSync(join(tmpdir(), "g17-python-"));
    const machine = join(directory, "module.g17m");
    const environment = join(directory, "module.g17env");
    const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile", source,
      "--out", machine, "--environment", environment, "--module-root", "lib"],
    { cwd: project, encoding: "utf8" });
    assert.equal(compile.status, 0, compile.stderr);
    const checked = runPython(machine, environment);
    assert.equal(checked.status, 0, checked.stderr);
    assert.equal(JSON.parse(checked.stdout).ok, true);
  }
});

test("independent Python checker covers specialized logical and induction rules", () => {
  const kernel = createZfgKernel();
  const empty = app("empty");
  const truth = eq(empty, empty);
  const conjunction = and(truth, truth);
  kernel.addTheorem("foreign.and_left", truth, andElimLeft(andIntro(refl(empty), refl(empty))));
  kernel.addTheorem("foreign.and_right", truth, andElimRight(andIntro(refl(empty), refl(empty))));
  const choice = or(truth, truth);
  kernel.addTheorem("foreign.or_elim", truth, orElim(
    orIntroLeft(refl(empty), truth), assume(truth), assume(truth),
  ));
  kernel.addTheorem("foreign.or_right", choice, orIntroRight(truth, refl(empty)));
  const identity = impIntro(truth, assume(truth));
  kernel.addTheorem("foreign.iff_left", imp(truth, truth), iffElimLeft(iffIntro(identity, identity)));
  kernel.addTheorem("foreign.eq_elim", truth,
    eqElim(refl(empty), "z", eq(v("z"), empty), refl(empty)));
  const existential = existsIntro("z", eq(v("z"), v("z")), empty, refl(empty));
  kernel.addTheorem("foreign.exists_elim", truth, existsElim(existential, "w", refl(empty)));
  kernel.addAxiom("foreign.absurd", bottom);
  kernel.addTheorem("foreign.false_elim", truth, falseElim(truth, axiom("foreign.absurd")));
  const notTruth = imp(truth, bottom);
  kernel.addTheorem("foreign.dne", truth,
    dne(truth, impIntro(notTruth, impElim(assume(notTruth), refl(empty)))));

  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  const motive = eq(v("x"), v("x"));
  kernel.addAxiom("foreign.wf", pred("wellFoundedOn", relation, domain));
  const ih = forall("y", imp(and(pred("in", v("y"), domain), pred("relates", relation, v("y"), v("x"))), eq(v("y"), v("y"))));
  const step = forall("x", imp(pred("in", v("x"), domain), imp(ih, motive)));
  kernel.addAxiom("foreign.wf_step", step);
  kernel.addTheorem("foreign.wf_induction", forall("x", imp(pred("in", v("x"), domain), motive)),
    wellFoundedInduction(relation, domain, "x", "y", motive, axiom("foreign.wf"), axiom("foreign.wf_step")));

  const names = [...kernel.theorems.keys()].filter(name => name.startsWith("foreign."));
  const machineProgram = compileProofModule(names.map(name => exportTheorem(kernel, name)));
  const opcodes = new Set(machineProgram.code.map(instruction => instruction[0]));
  for (const opcode of [13, 15, 16, 19, 20, 21, 24, 25, 26, 27]) assert.equal(opcodes.has(opcode), true, `missing opcode ${opcode}`);
  const directory = mkdtempSync(join(tmpdir(), "g17-python-rules-"));
  const machine = join(directory, "rules.g17m");
  const environment = join(directory, "rules.g17env");
  writeFileSync(machine, encodeProofMachineBinary(machineProgram));
  writeFileSync(environment, `${JSON.stringify(exportKernelEnvironment(kernel), null, 2)}\n`);
  const checked = runPython(machine, environment);
  assert.equal(checked.status, 0, checked.stderr);
  assert.equal(JSON.parse(checked.stdout).theorems, names.length);
});

test("TypeScript and Python checkers reject non-fresh induction fields", () => {
  const kernel = createZfgKernel();
  kernel.declareDatatype({
    name: "ForeignBoxFamily",
    predicate: "ForeignBox",
    parameters: ["Carrier"],
    constructors: [{ name: "foreignBox", arity: 1, recursiveFields: [] }],
  });
  const motive = eq(v("A"), v("A"));
  const proof = forallIntro("A", forallIntro("Carrier", induction(
    "ForeignBoxFamily",
    "item",
    motive,
    [{ constructor: "foreignBox", fields: ["field"], proof: refl(v("A")) }],
    [v("Carrier")],
  )));
  const statement = kernel.checkProof(proof);
  kernel.addTheorem("foreign.induction_freshness", statement, proof);
  const valid = compileProofMachine(exportTheorem(kernel, "foreign.induction_freshness"));
  assert.doesNotThrow(() => verifyProofMachine(kernel, valid));

  const directory = mkdtempSync(join(tmpdir(), "g17-python-induction-freshness-"));
  const environment = join(directory, "module.g17env");
  writeFileSync(environment, `${JSON.stringify(exportKernelEnvironment(kernel), null, 2)}\n`);
  for (const collision of ["A", "Carrier"]) {
    const forged = structuredClone(valid);
    const instruction = forged.code.find(item => item[0] === 12)!;
    const dataStart = 4 + instruction[3]!;
    const parameterCount = instruction[dataStart + 3]!;
    const firstField = dataStart + 7 + parameterCount;
    instruction[firstField] = forged.symbols.indexOf(collision);
    assert.notEqual(instruction[firstField], -1);
    assert.throws(() => verifyProofMachine(kernel, forged), /induction field is not fresh/i);

    const machine = join(directory, `collision-${collision}.g17m`);
    writeFileSync(machine, encodeProofMachineBinary(forged));
    const checked = runPython(machine, environment);
    assert.notEqual(checked.status, 0);
    assert.match(`${checked.stdout}\n${checked.stderr}`, /induction field is not fresh/i);
  }
});

test("TypeScript and Python checkers reject hidden free variables in universal introduction", () => {
  const kernel = createZfgKernel();
  const hypothesis = and(
    pred("in", v("x"), app("omega")),
    forall("x", eq(v("x"), v("x"))),
  );
  const proof = forallIntro("x", impIntro(hypothesis, forallIntro("z", refl(app("empty")))));
  const statement = kernel.checkProof(proof);
  kernel.addTheorem("foreign.forall_freshness", statement, proof);
  const valid = compileProofMachine(exportTheorem(kernel, "foreign.forall_freshness"));
  assert.doesNotThrow(() => verifyProofMachine(kernel, valid));

  const forged = structuredClone(valid);
  const instruction = forged.code.find(item => item[0] === 10 &&
    forged.symbols[item[4 + item[3]!]!] === "z")!;
  instruction[4 + instruction[3]!] = forged.symbols.indexOf("x");
  assert.throws(() => verifyProofMachine(kernel, forged), /Generalized variable is free/i);

  const directory = mkdtempSync(join(tmpdir(), "g17-python-forall-freshness-"));
  const machine = join(directory, "forged.g17m");
  const environment = join(directory, "module.g17env");
  writeFileSync(machine, encodeProofMachineBinary(forged));
  writeFileSync(environment, `${JSON.stringify(exportKernelEnvironment(kernel), null, 2)}\n`);
  const checked = runPython(machine, environment);
  assert.notEqual(checked.status, 0);
  assert.match(`${checked.stdout}\n${checked.stderr}`, /generalized variable is free/i);
});

test("independent checker rejects corrupted bytes and environment manifests", () => {
  const directory = mkdtempSync(join(tmpdir(), "g17-python-bad-"));
  const machine = join(directory, "module.g17m");
  const environment = join(directory, "module.g17env");
  const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile", "examples/Sets.g17",
    "--out", machine, "--environment", environment], { cwd: project, encoding: "utf8" });
  assert.equal(compile.status, 0, compile.stderr);

  const badMachine = join(directory, "bad.g17m");
  const bytes = readFileSync(machine);
  bytes[Math.floor(bytes.length / 2)]! ^= 1;
  writeFileSync(badMachine, bytes);
  assert.notEqual(runPython(badMachine, environment).status, 0);

  const badEnvironment = join(directory, "bad.g17env");
  const document = JSON.parse(readFileSync(environment, "utf8"));
  document.kernel.functions[0][1] += 1;
  writeFileSync(badEnvironment, JSON.stringify(document));
  assert.notEqual(runPython(machine, badEnvironment).status, 0);
});
