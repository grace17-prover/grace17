// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { createHash } from "node:crypto";
import { readFileSync } from "node:fs";
import { join } from "node:path";
import { decodeProofMachineBinary, verifyProofMachine } from "../src/index.ts";
import { buildConformanceFixture } from "../conformance/cases.ts";

interface Manifest {
  format: string;
  version: number;
  g17m_version: number;
  logical_environment_digest: string;
  environment: { file: string; sha256: string };
  vectors: Array<{
    id: string; expected: "accept" | "reject"; certificate: string; sha256: string;
  }>;
}

const root = join(import.meta.dirname, "..");
const directory = join(root, "conformance");
const manifest = JSON.parse(readFileSync(join(directory, "manifest.json"), "utf8")) as Manifest;
if (manifest.format !== "grace17.conformance" || manifest.version !== 1 || manifest.g17m_version !== 4) {
  throw new Error("Unsupported conformance manifest");
}
const fixture = buildConformanceFixture();
if (fixture.kernel.digest() !== manifest.logical_environment_digest) {
  throw new Error("Conformance environment does not match the normative fixture");
}
const digest = (bytes: Uint8Array): string => createHash("sha256").update(bytes).digest("hex");
const environmentBytes = readFileSync(join(directory, manifest.environment.file));
if (digest(environmentBytes) !== manifest.environment.sha256) throw new Error("Conformance environment checksum mismatch");

let failures = 0;
for (const vector of manifest.vectors) {
  const bytes = readFileSync(join(directory, vector.certificate));
  if (digest(bytes) !== vector.sha256) throw new Error(`Checksum mismatch: ${vector.id}`);
  let accepted = false;
  try {
    const program = decodeProofMachineBinary(bytes);
    if ("theorems" in program) throw new Error("Conformance vectors must be unlinked tapes");
    verifyProofMachine(fixture.kernel, program);
    accepted = true;
  } catch {
    accepted = false;
  }
  if (accepted !== (vector.expected === "accept")) {
    failures += 1;
    console.error(`${vector.id}: expected ${vector.expected}, checker ${accepted ? "accepted" : "rejected"}`);
  }
}
if (failures) throw new Error(`${failures} conformance expectation(s) failed`);
console.log(`TypeScript checker passed ${manifest.vectors.length} conformance vectors`);
