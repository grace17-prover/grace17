// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { createHash } from "node:crypto";
import { mkdirSync, rmSync, writeFileSync } from "node:fs";
import { dirname, join } from "node:path";
import {
  compileProofMachine, encodeProofMachineBinary, exportKernelEnvironment,
  exportTheorem, type ProofMachineProgram,
} from "../src/index.ts";
import { buildConformanceFixture } from "../conformance/cases.ts";

type MutableProgram = {
  version: 4;
  environment: string;
  symbols: string[];
  terms: number[][];
  formulas: number[][];
  contexts: number[][];
  code: number[][];
  root: number;
};

interface VectorRecord {
  id: string;
  expected: "accept" | "reject";
  rule: string;
  opcode: number;
  invariant: string;
  certificate: string;
  sha256: string;
}

const root = join(import.meta.dirname, "..");
const conformance = join(root, "conformance");
const vectors = join(conformance, "vectors");
const fixture = buildConformanceFixture();
const records: VectorRecord[] = [];

function clone(program: ProofMachineProgram): MutableProgram {
  return structuredClone(program) as MutableProgram;
}

function sha256(bytes: Uint8Array | string): string {
  return createHash("sha256").update(bytes).digest("hex");
}

function slug(value: string): string {
  return value.replaceAll(/[^a-z0-9]+/g, "-").replaceAll(/^-|-$/g, "");
}

function save(id: string, expected: "accept" | "reject", rule: string, opcode: number,
  invariant: string, program: MutableProgram | ProofMachineProgram): void {
  const bytes = encodeProofMachineBinary(program);
  const relative = `vectors/${expected}/${id}.g17m`;
  const target = join(conformance, relative);
  mkdirSync(dirname(target), { recursive: true });
  writeFileSync(target, bytes);
  records.push({ id, expected, rule, opcode, invariant, certificate: relative, sha256: sha256(bytes) });
}

function instruction(program: MutableProgram, opcode: number): number[] {
  const found = program.code.findLast(item => item[0] === opcode);
  if (!found) throw new Error(`Fixture contains no opcode ${opcode}`);
  return found;
}

function wrongClaim(program: MutableProgram, opcode: number): void {
  const target = instruction(program, opcode);
  const current = target[1]!;
  let replacement = program.formulas.findIndex((_, index) => index !== current);
  if (replacement < 0) {
    replacement = program.formulas.length;
    program.formulas.push([0]);
  }
  target[1] = replacement;
}

rmSync(vectors, { recursive: true, force: true });

for (const item of fixture.cases) {
  const program = compileProofMachine(exportTheorem(fixture.kernel, item.theorem));
  const stem = `op${String(item.opcode).padStart(2, "0")}-${slug(item.rule)}`;
  save(`${stem}-accept`, "accept", item.rule, item.opcode,
    "A canonical proof using this primitive rule must be accepted.", program);
  const rejected = clone(program);
  wrongClaim(rejected, item.opcode);
  save(`${stem}-wrong-claim`, "reject", item.rule, item.opcode,
    "The checker must derive the result itself and reject a false claimed conclusion.", rejected);
}

const forallProgram = clone(compileProofMachine(exportTheorem(
  fixture.kernel, fixture.securitySeeds.forallFreshness,
)));
const zSymbol = forallProgram.symbols.indexOf("z");
const forallInstruction = forallProgram.code.find(item =>
  item[0] === 10 && item[4 + item[3]!] === zSymbol,
);
if (!forallInstruction) throw new Error("Cannot find inner universal-introduction fixture");
const forallData = 4 + forallInstruction[3]!;
forallInstruction[forallData] = forallProgram.symbols.indexOf("x");
save("op10-universal-introduction-hidden-context-variable", "reject", "universal-introduction", 10,
  "The eigenvariable must not occur free anywhere in the context, including beneath a sibling binder.", forallProgram);

for (const collision of ["A", "Carrier"] as const) {
  const inductionProgram = clone(compileProofMachine(exportTheorem(
    fixture.kernel, fixture.securitySeeds.inductionFreshness,
  )));
  const inductionInstruction = instruction(inductionProgram, 12);
  const data = 4 + inductionInstruction[3]!;
  const parameterCount = inductionInstruction[data + 3]!;
  const firstField = data + 7 + parameterCount;
  inductionInstruction[firstField] = inductionProgram.symbols.indexOf(collision);
  const source = collision === "A" ? "open motive" : "datatype parameter term";
  save(`op12-datatype-induction-field-collides-${slug(source)}`, "reject", "datatype-induction", 12,
    `Constructor field symbols must be fresh for the ${source}.`, inductionProgram);
}

const computeCase = fixture.cases.find(item => item.opcode === 28)!;
const computeProgram = clone(compileProofMachine(exportTheorem(fixture.kernel, computeCase.theorem)));
const computeInstruction = instruction(computeProgram, 28);
const computeData = 4 + computeInstruction[3]!;
if (computeInstruction[computeData]! < 1) throw new Error("Computation fixture has no dependencies");
computeInstruction[computeData] = computeInstruction[computeData]! - 1;
computeInstruction.pop();
save("op28-ground-computation-inexact-dependencies", "reject", "ground-computation", 28,
  "The allow-list must equal the exact sorted set of definitions actually unfolded.", computeProgram);

// Validly authenticated tapes with invalid logical export boundaries.
const openRoot: MutableProgram = {
  version: 4, environment: fixture.kernel.digest(), symbols: ["audit.false"],
  terms: [], formulas: [[0]], contexts: [[0], []], code: [[0, 0, 0, 0, 0]], root: 0,
};
save("open-assumption-root", "reject", "export-boundary", 0,
  "A standalone proof root must have an empty context.", openRoot);
save("open-theorem-boundary", "reject", "export-boundary", 2,
  "A closed citation cannot discharge an open linked theorem's assumptions.", {
    ...openRoot, code: [[0, 0, 0, 0, 0], [2, 0, 1, 0, 0]], root: 1,
    theorems: [[0, 0]],
  } as ProofMachineProgram);

const environment = JSON.stringify(exportKernelEnvironment(fixture.kernel), null, 2) + "\n";
writeFileSync(join(conformance, "environment.g17env"), environment);
const manifest = {
  format: "grace17.conformance",
  version: 1,
  g17m_version: 4,
  logical_environment_digest: fixture.kernel.digest(),
  environment: { file: "environment.g17env", sha256: sha256(environment) },
  coverage: {
    opcodes: fixture.cases.map(item => item.opcode),
    accept: records.filter(item => item.expected === "accept").length,
    reject: records.filter(item => item.expected === "reject").length,
  },
  vectors: records,
};
writeFileSync(join(conformance, "manifest.json"), JSON.stringify(manifest, null, 2) + "\n");
console.log(`generated ${records.length} conformance vectors (${manifest.coverage.accept} accept, ${manifest.coverage.reject} reject)`);
