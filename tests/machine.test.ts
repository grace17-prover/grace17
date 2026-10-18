// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import { fileURLToPath } from "node:url";
import { mkdtempSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { spawnSync } from "node:child_process";
import {
  KernelError, and, app, assume, axiom, bottom, compileProofMachine, compileProofModule,
  createZfgKernel, decodeProofMachineBinary, dne, elaborateModule, encodeProofMachineBinary,
  eq, eqElim, exists, existsElim, existsIntro, exportTheorem, falseElim, forall, formulaEquals,
  imp, impElim, impIntro, pred, refl, v, verifyProofMachine, verifyProofMachineBinary,
  verifyProofModule, wellFoundedInduction,
  type ProofMachineProgram,
} from "../src/index.ts";
import { buildProofSuite } from "../examples/proof-suite.ts";

test("compiles arithmetic and set-computation proofs to numeric machine programs", () => {
  const suite = buildProofSuite();
  for (const example of suite.examples) {
    const program = compileProofMachine(exportTheorem(suite.kernel, example.name));
    const checked = verifyProofMachine(suite.kernel, program);
    assert.equal(program.version, 4);
    assert.ok(program.code.every(instruction => instruction.every(Number.isSafeInteger)));
    assert.equal(checked.stats.instructions, program.code.length);
    assert.equal(formulaEquals(checked.formula, example.statement), true);
  }
});

test("ground computation is one proof node and one machine instruction", () => {
  const kernel = createZfgKernel();
  const source = readFileSync(fileURLToPath(new URL("../examples/Arithmetic.g17", import.meta.url)), "utf8");
  elaborateModule(kernel, source);
  const exported = exportTheorem(kernel, "times.ground_700");
  assert.equal(exported.proof.nodes.length, 1);
  assert.equal(exported.proof.nodes[0]!.payload.rule, "compute");
  assert.deepEqual(exported.dependencies.definitions, ["plus.equation", "times.equation"]);
  const program = compileProofMachine(exported);
  assert.equal(program.code.length, 1);
  assert.equal(program.code[0]![0], 28);
  assert.equal(formulaEquals(verifyProofMachine(kernel, program).formula, exported.statement), true);

  const corrupted = structuredClone(program);
  corrupted.code[0]!.pop();
  assert.throws(() => verifyProofMachine(kernel, corrupted), /computation dependencies/);

  const malformedNatural = structuredClone(program);
  const natural = malformedNatural.terms.find(node => node[0] === 3)!;
  malformedNatural.symbols[natural[1]!] = "01";
  assert.throws(() => encodeProofMachineBinary(malformedNatural), /natural/);
});

test("links theorem boundaries and round-trips a canonical authenticated G17M module", () => {
  const suite = buildProofSuite();
  const exports = suite.examples.map(example => exportTheorem(suite.kernel, example.name));
  const module = compileProofModule(exports);
  assert.deepEqual(verifyProofModule(suite.kernel, module), { theorems: 3, instructions: 94 });
  const bytes = encodeProofMachineBinary(module);
  assert.equal(new TextDecoder().decode(bytes.subarray(0, 4)), "G17M");
  assert.ok(bytes.length < JSON.stringify(module).length);
  const decoded = decodeProofMachineBinary(bytes);
  assert.ok("theorems" in decoded);
  assert.deepEqual(verifyProofMachineBinary(suite.kernel, bytes), { theorems: 3, instructions: 94 });

  const corrupted = bytes.slice();
  corrupted[Math.floor(corrupted.length / 2)]! ^= 1;
  assert.throws(() => decodeProofMachineBinary(corrupted), /digest/);
  const invalid = structuredClone(module);
  invalid.code[invalid.root]![4] = invalid.root;
  assert.throws(() => encodeProofMachineBinary(invalid), KernelError);
});

test("numeric machine covers equality, existential, classical, false, and well-founded rules", () => {
  const kernel = createZfgKernel();
  const empty = app("empty");
  const truth = eq(empty, empty);

  kernel.addTheorem("machine.eq_elim", truth,
    eqElim(refl(empty), "z", eq(v("z"), empty), refl(empty)));
  const existential = existsIntro("z", eq(v("z"), v("z")), empty, refl(empty));
  kernel.addTheorem("machine.exists_elim", truth, existsElim(existential, "w", refl(empty)));
  kernel.addAxiom("machine.absurd", bottom);
  kernel.addTheorem("machine.false_elim", truth, falseElim(truth, axiom("machine.absurd")));
  const notTruth = imp(truth, bottom);
  kernel.addTheorem("machine.dne", truth,
    dne(truth, impIntro(notTruth, impElim(assume(notTruth), refl(empty)))));

  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  const motive = eq(v("x"), v("x"));
  kernel.addAxiom("machine.wf", pred("wellFoundedOn", relation, domain));
  const predecessorMotive = eq(v("y"), v("y"));
  const inductionHypothesis = forall("y", imp(
    and(pred("in", v("y"), domain), pred("relates", relation, v("y"), v("x"))),
    predecessorMotive,
  ));
  const step = forall("x", imp(pred("in", v("x"), domain), imp(inductionHypothesis, motive)));
  kernel.addAxiom("machine.wf_step", step);
  const result = forall("x", imp(pred("in", v("x"), domain), motive));
  kernel.addTheorem("machine.wf_induction", result,
    wellFoundedInduction(relation, domain, "x", "y", motive, axiom("machine.wf"), axiom("machine.wf_step")));

  for (const theorem of ["machine.eq_elim", "machine.exists_elim", "machine.false_elim", "machine.dne", "machine.wf_induction"]) {
    const checked = verifyProofMachine(kernel, compileProofMachine(exportTheorem(kernel, theorem)));
    assert.equal(formulaEquals(checked.formula, kernel.theorems.get(theorem)!), true, theorem);
  }
  assert.equal(kernel.checkProof(existential).tag, "exists");
  assert.equal(formulaEquals(kernel.checkProof(existential), exists("z", eq(v("z"), v("z")))), true);
});

test("numeric machine covers every theorem in the set-theory surface suite", () => {
  const kernel = createZfgKernel();
  const source = readFileSync(fileURLToPath(new URL("../examples/Sets.g17", import.meta.url)), "utf8");
  const module = elaborateModule(kernel, source);
  for (const theorem of module.theorems) {
    const checked = verifyProofMachine(kernel, compileProofMachine(exportTheorem(kernel, theorem)));
    assert.equal(formulaEquals(checked.formula, kernel.theorems.get(theorem)!), true, theorem);
  }
});

test("qualified module theorems compile into a shared authenticated tape", () => {
  const kernel = createZfgKernel();
  const core = readFileSync(fileURLToPath(new URL("../examples/CoreNat.g17", import.meta.url)), "utf8");
  const client = readFileSync(fileURLToPath(new URL("../examples/ModuleCompute.g17", import.meta.url)), "utf8");
  const theoremNames = [...elaborateModule(kernel, core).theorems, ...elaborateModule(kernel, client).theorems];
  const program = compileProofModule(theoremNames.map(name => exportTheorem(kernel, name)));
  // Refined-result definitions also contribute their checked .type laws.
  assert.deepEqual(theoremNames, [
    "Grace.Core.Nat.Rec.add.type", "Grace.Core.Nat.Rec.add.left_unit",
    "Grace.Examples.Compute.Demo.double.type", "Grace.Examples.Compute.Demo.double.three",
    "Grace.Examples.Compute.Demo.imported_add",
  ]);
  assert.deepEqual(verifyProofModule(kernel, program), { theorems: 5, instructions: 39 });
  assert.deepEqual(verifyProofMachineBinary(kernel, encodeProofMachineBinary(program)), { theorems: 5, instructions: 39 });
});

test("numeric machine rejects corrupted conclusions, contexts, and forward references", () => {
  const suite = buildProofSuite();
  const original = compileProofMachine(exportTheorem(suite.kernel, "plus.right_unit"));
  const mutate = (change: (copy: any) => void): ProofMachineProgram => {
    const copy = structuredClone(original);
    change(copy);
    return copy;
  };
  assert.throws(() => verifyProofMachine(suite.kernel, mutate(copy => {
    const root = copy.root;
    copy.code[root][1] = (copy.code[root][1] + 1) % copy.formulas.length;
  })), /wrong formula|received the wrong|Bad/);
  assert.throws(() => verifyProofMachine(suite.kernel, mutate(copy => {
    copy.code[copy.root][2] = 999_999;
  })), /context/);
  assert.throws(() => verifyProofMachine(suite.kernel, mutate(copy => {
    copy.code[copy.root][4] = copy.root;
  })), /forward or invalid premise/);
});

test("linked theorem boundaries cannot cite themselves or later theorems", () => {
  const suite = buildProofSuite();
  const program = compileProofModule([exportTheorem(suite.kernel, "plus.right_unit")]);
  const forged = structuredClone(program);
  const [name, root] = forged.theorems[0]!;
  forged.code[root] = [2, forged.code[root]![1]!, forged.code[root]![2]!, 0, name];
  assert.throws(() => verifyProofModule(suite.kernel, forged), /not yet proved/);
});

test("CLI compiles and verifies a portable G17M module", () => {
  const project = fileURLToPath(new URL("..", import.meta.url));
  const directory = mkdtempSync(join(tmpdir(), "g17m-"));
  const output = join(directory, "sets.g17m");
  const compile = spawnSync(process.execPath, ["bin/g17.ts", "compile", "examples/Sets.g17", "--out", output, "--json"], {
    cwd: project, encoding: "utf8",
  });
  assert.equal(compile.status, 0, compile.stderr);
  const compiled = JSON.parse(compile.stdout);
  assert.equal(compiled.theorems, 7);
  assert.ok(compiled.bytes > 32);
  const verify = spawnSync(process.execPath, ["bin/g17.ts", "verify-machine", "examples/Sets.g17", "--machine", output, "--json"], {
    cwd: project, encoding: "utf8",
  });
  assert.equal(verify.status, 0, verify.stderr);
  assert.equal(JSON.parse(verify.stdout).theorems, 7);
});
