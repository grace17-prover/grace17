// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { sha256Bytes, timingSafeBytesEqual } from "./hash.ts";
import { KernelError, type Kernel } from "./kernel.ts";
import {
  verifyProofMachine, verifyProofModule,
  type ProofMachineModuleProgram, type ProofMachineProgram,
} from "./machine.ts";

const MAGIC = Uint8Array.of(0x47, 0x31, 0x37, 0x4d); // G17M
const VERSION = 4;
const DIGEST_BYTES = 32;
const MAX_COUNT = 10_000_000;
const MAX_VECTOR = 1_000_000;

/** Canonical binary encoding: unsigned LEB128 vectors followed by SHA-256. */
export function encodeProofMachineBinary(program: ProofMachineProgram): Uint8Array {
  validateProgram(program);
  const writer = new Writer();
  writer.bytes(MAGIC);
  writer.byte(VERSION);
  const module = "theorems" in program;
  writer.byte(module ? 1 : 0);
  writer.bytes(Uint8Array.from(Buffer.from(program.environment, "hex")));
  writer.varUint(program.symbols.length);
  for (const symbol of program.symbols) writer.string(symbol);
  writeVectors(writer, program.terms);
  writeVectors(writer, program.formulas);
  writeVectors(writer, program.contexts);
  writeVectors(writer, program.code);
  writer.varUint(program.root);
  const boundaries = module ? (program as ProofMachineModuleProgram).theorems : [];
  writer.varUint(boundaries.length);
  for (const [name, root] of boundaries) { writer.varUint(name); writer.varUint(root); }
  const body = writer.finish();
  const digest = sha256Bytes(body);
  const result = new Uint8Array(body.length + digest.length);
  result.set(body); result.set(digest, body.length);
  return result;
}

export function decodeProofMachineBinary(bytes: Uint8Array): ProofMachineProgram | ProofMachineModuleProgram {
  if (bytes.length < MAGIC.length + 2 + DIGEST_BYTES) throw new KernelError("Truncated G17M certificate");
  const body = bytes.subarray(0, bytes.length - DIGEST_BYTES);
  const supplied = bytes.subarray(bytes.length - DIGEST_BYTES);
  const actual = sha256Bytes(body);
  if (!timingSafeBytesEqual(actual, supplied)) throw new KernelError("Corrupted G17M certificate digest");
  const reader = new Reader(body);
  for (const expected of MAGIC) if (reader.byte() !== expected) throw new KernelError("Bad G17M magic");
  if (reader.byte() !== VERSION) throw new KernelError("Unsupported G17M version");
  const flags = reader.byte();
  if (flags !== 0 && flags !== 1) throw new KernelError("Unsupported G17M flags");
  const environment = Buffer.from(reader.bytes(DIGEST_BYTES)).toString("hex");
  const symbolCount = reader.count("symbols");
  const symbols = Array.from({ length: symbolCount }, () => reader.string());
  const terms = readVectors(reader, "terms");
  const formulas = readVectors(reader, "formulas");
  const contexts = readVectors(reader, "contexts");
  const code = readVectors(reader, "instructions");
  const root = reader.varUint();
  const theoremCount = reader.count("theorems");
  const theorems = Array.from({ length: theoremCount }, () => [reader.varUint(), reader.varUint()] as [number, number]);
  if (!reader.done()) throw new KernelError("Trailing data in G17M certificate");
  if ((flags === 0) !== (theorems.length === 0)) throw new KernelError("G17M theorem-boundary flag mismatch");
  const base = { version: 4 as const, environment, symbols, terms, formulas, contexts, code, root };
  const program = flags === 1 ? { ...base, theorems } : base;
  validateProgram(program);
  deepFreeze(program);
  return program;
}

export function verifyProofMachineBinary(kernel: Kernel, bytes: Uint8Array): {
  readonly instructions: number;
  readonly theorems: number;
} {
  const program = decodeProofMachineBinary(bytes);
  if ("theorems" in program) return verifyProofModule(kernel, program);
  return { instructions: verifyProofMachine(kernel, program).stats.instructions, theorems: 1 };
}

function writeVectors(writer: Writer, vectors: readonly (readonly number[])[]): void {
  writer.varUint(vectors.length);
  for (const vector of vectors) {
    writer.varUint(vector.length);
    for (const value of vector) writer.varUint(value);
  }
}

function readVectors(reader: Reader, name: string): number[][] {
  const count = reader.count(name);
  return Array.from({ length: count }, (_, index) => {
    const length = reader.vectorLength(`${name}[${index}]`);
    return Array.from({ length }, () => reader.varUint());
  });
}

function validateProgram(program: ProofMachineProgram): void {
  if (program.version !== 4 || !/^[0-9a-f]{64}$/.test(program.environment)) throw new KernelError("Bad proof-machine version or environment digest");
  if (program.symbols.length > MAX_COUNT || program.terms.length > MAX_COUNT || program.formulas.length > MAX_COUNT ||
      program.contexts.length > MAX_COUNT || program.code.length > MAX_COUNT) throw new KernelError("G17M arena is too large");
  const symbols = new Set<string>();
  program.symbols.forEach((symbol, index) => {
    if (!symbol || symbols.has(symbol)) throw new KernelError(`Bad or duplicate G17M symbol ${index}`);
    symbols.add(symbol);
  });
  const termNodes = new Set<string>();
  program.terms.forEach((node, index) => {
    if (node.length < 2 || node.some(value => !isUint(value))) throw new KernelError(`Malformed G17M term ${index}`);
    if (node[0] === 0 && (node.length !== 2 || node[1]! >= program.symbols.length)) throw new KernelError(`Malformed G17M free variable ${index}`);
    else if (node[0] === 1 && node.length !== 2) throw new KernelError(`Malformed G17M bound variable ${index}`);
    else if (node[0] === 2 && (node[1]! >= program.symbols.length || node.slice(2).some(child => child >= index))) throw new KernelError(`Malformed G17M application ${index}`);
    else if (node[0] === 3 && (node.length !== 2 || node[1]! >= program.symbols.length || !/^(?:0|[1-9]\d*)$/.test(program.symbols[node[1]!]!))) throw new KernelError(`Malformed G17M natural ${index}`);
    else if (node[0]! > 3) throw new KernelError(`Unknown G17M term opcode at ${index}`);
    const key = node.join(","); if (termNodes.has(key)) throw new KernelError(`Duplicate G17M term ${index}`); termNodes.add(key);
  });
  const formulaNodes = new Set<string>();
  program.formulas.forEach((node, index) => {
    if (node.length === 0 || node.some(value => !isUint(value))) throw new KernelError(`Malformed G17M formula ${index}`);
    const op = node[0]!;
    if (op === 0 && node.length !== 1) throw new KernelError(`Malformed G17M bottom ${index}`);
    else if (op === 1 && (node.length !== 3 || node[1]! >= program.terms.length || node[2]! >= program.terms.length)) throw new KernelError(`Malformed G17M equality ${index}`);
    else if (op === 2 && (node.length < 2 || node[1]! >= program.symbols.length || node.slice(2).some(term => term >= program.terms.length))) throw new KernelError(`Malformed G17M predicate ${index}`);
    else if ((op === 3 || (op >= 5 && op <= 7)) && (node.length !== 3 || node[1]! >= index || node[2]! >= index)) throw new KernelError(`Malformed G17M binary formula ${index}`);
    else if ((op === 4 || op === 8) && (node.length !== 2 || node[1]! >= index)) throw new KernelError(`Malformed G17M quantifier ${index}`);
    else if (op > 8) throw new KernelError(`Unknown G17M formula opcode at ${index}`);
    const key = node.join(","); if (formulaNodes.has(key)) throw new KernelError(`Duplicate G17M formula ${index}`); formulaNodes.add(key);
  });
  const contextNodes = new Set<string>();
  program.contexts.forEach((context, index) => {
    if (context.length > MAX_VECTOR || context.some(formula => !isUint(formula) || formula >= program.formulas.length)) throw new KernelError(`Malformed G17M context ${index}`);
    const key = context.join(","); if (contextNodes.has(key)) throw new KernelError(`Duplicate G17M context ${index}`); contextNodes.add(key);
  });
  program.code.forEach((instruction, pc) => {
    if (instruction.length < 4 || instruction.length > MAX_VECTOR || instruction.some(value => !isUint(value))) throw new KernelError(`Malformed G17M instruction ${pc}`);
    const [op, conclusion, context, premises] = instruction;
    if (op! > 29 || conclusion! >= program.formulas.length || context! >= program.contexts.length ||
        premises! > instruction.length - 4 || instruction.slice(4, 4 + premises!).some(premise => premise >= pc)) {
      throw new KernelError(`Invalid G17M instruction ${pc}`);
    }
  });
  if (!isUint(program.root) || program.root >= program.code.length) throw new KernelError("Invalid G17M root");
  if ("theorems" in program) {
    const names = new Set<number>();
    for (const [name, root] of program.theorems) {
      if (!isUint(name) || name >= program.symbols.length || names.has(name) || !isUint(root) || root >= program.code.length) {
        throw new KernelError("Malformed G17M theorem boundary");
      }
      names.add(name);
    }
  }
}

function isUint(value: number): boolean { return Number.isSafeInteger(value) && value >= 0 && value <= 0xffff_ffff; }

class Writer {
  private readonly data: number[] = [];
  byte(value: number): void { this.data.push(value); }
  bytes(values: Uint8Array): void { for (const value of values) this.data.push(value); }
  varUint(value: number): void {
    if (!isUint(value)) throw new KernelError(`Cannot encode G17M integer ${value}`);
    do { const chunk = value % 128; value = Math.floor(value / 128); this.byte(chunk | (value > 0 ? 0x80 : 0)); } while (value > 0);
  }
  string(value: string): void { const bytes = new TextEncoder().encode(value); this.varUint(bytes.length); this.bytes(bytes); }
  finish(): Uint8Array { return Uint8Array.from(this.data); }
}

class Reader {
  private offset = 0;
  private readonly data: Uint8Array;
  constructor(data: Uint8Array) { this.data = data; }
  byte(): number { if (this.offset >= this.data.length) throw new KernelError("Truncated G17M data"); return this.data[this.offset++]!; }
  bytes(length: number): Uint8Array {
    if (this.offset + length > this.data.length) throw new KernelError("Truncated G17M data");
    const result = this.data.subarray(this.offset, this.offset + length); this.offset += length; return result;
  }
  varUint(): number {
    let value = 0; let factor = 1; let count = 0; let chunk: number;
    do {
      chunk = this.byte(); count += 1;
      if (count > 5) throw new KernelError("Oversized G17M integer");
      value += (chunk & 0x7f) * factor; factor *= 128;
    } while ((chunk & 0x80) !== 0);
    if ((count > 1 && (chunk & 0x7f) === 0) || !isUint(value)) throw new KernelError("Noncanonical G17M integer");
    return value;
  }
  count(name: string): number { const value = this.varUint(); if (value > MAX_COUNT) throw new KernelError(`Too many G17M ${name}`); return value; }
  vectorLength(name: string): number { const value = this.varUint(); if (value > MAX_VECTOR) throw new KernelError(`Oversized G17M vector ${name}`); return value; }
  string(): string {
    const length = this.vectorLength("string");
    if (this.offset + length > this.data.length) throw new KernelError("Truncated G17M string");
    const bytes = this.data.subarray(this.offset, this.offset + length); this.offset += length;
    const value = new TextDecoder("utf-8", { fatal: true }).decode(bytes);
    if (new TextEncoder().encode(value).length !== length) throw new KernelError("Noncanonical G17M UTF-8");
    return value;
  }
  done(): boolean { return this.offset === this.data.length; }
}

function deepFreeze(value: unknown, seen = new WeakSet<object>()): void {
  if (value === null || typeof value !== "object" || seen.has(value)) return;
  seen.add(value); for (const child of Object.values(value)) deepFreeze(child, seen); Object.freeze(value);
}
