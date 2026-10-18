// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { canonical } from "./ast.ts";
import { decodeProofDag, encodeProofDag, type ProofDag } from "./dag.ts";
import { deepFreeze as freezeCertificate } from "./freeze.ts";
import { sha256Hex } from "./hash.ts";
import { exportProofForMachine } from "./export.ts";
import {
  Kernel, KernelError, type KernelAdmissionCheckpoint, type KernelAdmissionEvent,
  type KernelAdmissionOperation, type SetTheoryProfile,
} from "./kernel.ts";
import { compileProofModule, type ProofMachineModuleProgram } from "./machine.ts";
import type { Proof } from "./proof.ts";

export interface CompiledModuleDependency {
  readonly module: string;
  readonly digest: string;
}

export interface CompiledAdmissionEvent {
  readonly operation: CompiledAdmissionOperation;
  readonly payload: unknown;
}

export type CompiledAdmissionOperation = Exclude<KernelAdmissionOperation, "addAxiom">;

/**
 * G17C is a certificate for reconstructing a kernel extension.  It
 * contains no serialized Kernel, maps, DefinitionRecord, or trusted snapshot.
 */
export interface CompiledKernelModule {
  readonly format: "grace17.compiled-module";
  readonly version: 1;
  readonly module: string;
  readonly source: string;
  readonly baseEnvironment: string;
  readonly dependencies: readonly CompiledModuleDependency[];
  readonly events: readonly CompiledAdmissionEvent[];
  readonly resultEnvironment: string;
  readonly digest: string;
}

export type DenseCompiledEvent =
  | { readonly kind: "admission"; readonly event: CompiledAdmissionEvent }
  | {
      readonly kind: "theoremBatch";
      readonly statements: readonly { readonly name: string; readonly statement: import("./ast.ts").Formula }[];
      readonly machine: ProofMachineModuleProgram;
    };

/** Version 2 shares one numeric proof arena within each consecutive theorem batch. */
export interface DenseCompiledKernelModule {
  readonly format: "grace17.compiled-module";
  readonly version: 2;
  readonly module: string;
  readonly source: string;
  readonly baseEnvironment: string;
  readonly dependencies: readonly CompiledModuleDependency[];
  readonly events: readonly DenseCompiledEvent[];
  readonly resultEnvironment: string;
  readonly digest: string;
}

/**
 * Version 3 is a separately cacheable module. Dependencies are the complete,
 * ordered checked prefix used to compile it. Strict checkers reconstruct that
 * prefix exactly; editor loaders may reuse the module in a larger monotone
 * environment after matching every content receipt.
 */
export interface SeparateCompiledKernelModule {
  readonly format: "grace17.compiled-module";
  readonly version: 3;
  readonly module: string;
  readonly source: string;
  readonly foundation: {
    readonly profile: SetTheoryProfile;
    readonly environment: string;
  };
  readonly dependencies: readonly CompiledModuleDependency[];
  readonly baseEnvironment: string;
  readonly events: readonly DenseCompiledEvent[];
  readonly resultEnvironment: string;
  readonly digest: string;
}

interface EncodedProof {
  readonly $grace17ProofDag: ProofDag;
}

const validatedModules = new WeakSet<object>();

const proofRules = new Set([
  "assumption", "axiom", "theorem", "definition", "refl", "compute", "rationalClassCompute", "symm", "trans", "congr",
  "impIntro", "impElim", "forallIntro", "forallElim", "eqElim", "andIntro", "andElimLeft",
  "andElimRight", "orIntroLeft", "orIntroRight", "orElim", "iffIntro", "iffElimLeft",
  "iffElimRight", "existsIntro", "existsElim", "falseElim", "dne", "induction", "wellFoundedInduction",
]);

/** Compile admissions performed after `checkpoint` into a deterministic certificate. */
export function compileKernelModule(
  kernel: Kernel,
  checkpoint: KernelAdmissionCheckpoint,
  options: {
    readonly module: string;
    readonly sourceDigest?: string;
    readonly dependencies?: readonly CompiledModuleDependency[];
  },
): CompiledKernelModule {
  if (!options.module) throw new KernelError("Compiled module name must not be empty");
  if (options.sourceDigest !== undefined && !isDigest(options.sourceDigest)) {
    throw new KernelError("Malformed compiled module source digest");
  }
  const dependencies = [...(options.dependencies ?? [])].sort((left, right) => left.module.localeCompare(right.module));
  if (new Set(dependencies.map(item => item.module)).size !== dependencies.length ||
      dependencies.some(item => !item.module || !isDigest(item.digest))) {
    throw new KernelError("Malformed compiled module dependency list");
  }
  const events = kernel.admissionEventsSince(checkpoint).map(encodeAdmission);
  const body = {
    format: "grace17.compiled-module" as const,
    version: 1 as const,
    module: options.module,
    source: options.sourceDigest ?? "",
    baseEnvironment: checkpoint.environment,
    dependencies,
    events,
    resultEnvironment: kernel.digest(),
  };
  const result = deepFreeze({ ...body, digest: sha256Hex(canonical(body)) });
  validatedModules.add(result);
  return result;
}

/** Canonical UTF-8 G17C encoding, suitable for content-addressed storage. */
export function encodeCompiledKernelModule(module: CompiledKernelModule): Uint8Array {
  validateEnvelope(module);
  return new TextEncoder().encode(canonical(module));
}

/** Parse only. Logical validity is established exclusively by replay. */
export function decodeCompiledKernelModule(bytes: Uint8Array): CompiledKernelModule {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed compiled module encoding"); }
  validateEnvelope(value);
  return value;
}

/**
 * Replay into a fresh fork.  The caller's base is unchanged even if an event
 * is corrupt or the claimed result digest is false.
 */
export function replayCompiledKernelModule(base: Kernel, compiled: CompiledKernelModule): Kernel {
  validateEnvelope(compiled);
  if (base.digest() !== compiled.baseEnvironment) {
    throw new KernelError("Compiled module belongs to a different base environment");
  }
  const result = base.fork();
  for (const event of compiled.events) replayAdmission(result, event);
  if (result.digest() !== compiled.resultEnvironment) {
    throw new KernelError("Compiled module replay produced the wrong environment");
  }
  return result;
}

/**
 * Compile the same admission transcript with dense G17M theorem batches.
 * `base` is required so each batch is compiled and checked at its true event
 * boundary rather than against the completed environment.
 */
export function compileDenseKernelModule(
  base: Kernel,
  completed: Kernel,
  checkpoint: KernelAdmissionCheckpoint,
  options: {
    readonly module: string;
    readonly sourceDigest?: string;
    readonly dependencies?: readonly CompiledModuleDependency[];
  },
): DenseCompiledKernelModule {
  if (base.digest() !== checkpoint.environment) throw new KernelError("Dense compilation base does not match its checkpoint");
  if (!options.module) throw new KernelError("Compiled module name must not be empty");
  if (options.sourceDigest !== undefined && !isDigest(options.sourceDigest)) {
    throw new KernelError("Malformed compiled module source digest");
  }
  const dependencies = [...(options.dependencies ?? [])].sort((left, right) => left.module.localeCompare(right.module));
  if (new Set(dependencies.map(item => item.module)).size !== dependencies.length ||
      dependencies.some(item => !item.module || !isDigest(item.digest))) {
    throw new KernelError("Malformed compiled module dependency list");
  }

  const admissions = completed.admissionEventsSince(checkpoint);
  const simulation = base.fork();
  const events: DenseCompiledEvent[] = [];
  for (let index = 0; index < admissions.length;) {
    const admission = admissions[index]!;
    if (admission.operation !== "addTheorem") {
      const event = encodeAdmission(admission);
      replayAdmission(simulation, event);
      events.push({ kind: "admission", event });
      index += 1;
      continue;
    }

    const batch: KernelAdmissionEvent[] = [];
    while (index < admissions.length && admissions[index]!.operation === "addTheorem") {
      batch.push(admissions[index]!);
      index += 1;
    }
    const environment = simulation.digest();
    const statements = batch.map(item => {
      const payload = item.payload;
      if (typeof payload.name !== "string" || !isRecord(payload.statement) || !isProof(payload.proof)) {
        throw new KernelError("Malformed retained theorem admission");
      }
      return { name: payload.name, statement: payload.statement as import("./ast.ts").Formula, proof: payload.proof };
    });
    const machine = compileProofModule(statements.map(item =>
      exportProofForMachine(completed, item.name, item.proof, environment)));
    const publicStatements = statements.map(({ name, statement }) => ({ name, statement }));
    simulation.addTheoremMachineBatch(publicStatements, machine);
    events.push({ kind: "theoremBatch", statements: publicStatements, machine });
  }
  if (simulation.digest() !== completed.digest()) throw new KernelError("Dense compiler did not reconstruct the completed environment");
  const body = {
    format: "grace17.compiled-module" as const,
    version: 2 as const,
    module: options.module,
    source: options.sourceDigest ?? "",
    baseEnvironment: checkpoint.environment,
    dependencies,
    events,
    resultEnvironment: completed.digest(),
  };
  return deepFreeze({ ...body, digest: sha256Hex(canonical(body)) });
}

export function encodeDenseKernelModule(module: DenseCompiledKernelModule): Uint8Array {
  validateDenseEnvelope(module);
  return new TextEncoder().encode(canonical(module));
}

export function decodeDenseKernelModule(bytes: Uint8Array): DenseCompiledKernelModule {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed dense compiled module encoding"); }
  validateDenseEnvelope(value);
  return value;
}

export function replayDenseKernelModule(base: Kernel, compiled: DenseCompiledKernelModule): Kernel {
  validateDenseEnvelope(compiled);
  if (base.digest() !== compiled.baseEnvironment) {
    throw new KernelError("Dense compiled module belongs to a different base environment");
  }
  const result = base.fork();
  for (const item of compiled.events) {
    if (item.kind === "admission") replayAdmission(result, item.event);
    else result.addTheoremMachineBatch(item.statements, item.machine);
  }
  if (result.digest() !== compiled.resultEnvironment) {
    throw new KernelError("Dense compiled module replay produced the wrong environment");
  }
  return result;
}

/** Compile a dense module against an exact, receipt-bearing dependency prefix. */
export function compileSeparateKernelModule(
  foundation: Kernel,
  base: Kernel,
  completed: Kernel,
  checkpoint: KernelAdmissionCheckpoint,
  options: {
    readonly module: string;
    readonly sourceDigest?: string;
    /** Complete dependency closure in replay order, not merely direct imports. */
    readonly dependencies?: readonly CompiledModuleDependency[];
  },
): SeparateCompiledKernelModule {
  const foundationEnvironment = foundation.foundationDigest();
  if (foundationEnvironment === undefined || foundation.digest() !== foundationEnvironment) {
    throw new KernelError("Separate compilation requires an exact completed foundation kernel");
  }
  if (base.foundationDigest() !== foundationEnvironment || completed.foundationDigest() !== foundationEnvironment) {
    throw new KernelError("Separate compilation kernels use a different foundation");
  }
  const dependencies = [...(options.dependencies ?? [])];
  validateDependencies(dependencies, "separate compiled module");
  for (const dependency of dependencies) {
    if (base.checkedModuleReceipt(dependency.module) !== dependency.digest) {
      throw new KernelError(`Separate compilation is missing exact dependency ${dependency.module}`);
    }
  }
  const expectedBase = dependencies.length === 0
    ? foundationEnvironment
    : base.checkedModuleResultEnvironment(dependencies[dependencies.length - 1]!.module);
  if (expectedBase === undefined || base.digest() !== expectedBase) {
    throw new KernelError("Separate compilation base is not the exact ordered dependency closure");
  }
  const dense = compileDenseKernelModule(base, completed, checkpoint, {
    module: options.module, sourceDigest: options.sourceDigest,
  });
  const body = {
    format: "grace17.compiled-module" as const,
    version: 3 as const,
    module: options.module,
    source: options.sourceDigest ?? "",
    foundation: {
      profile: foundation.capabilities.setTheory ?? "none",
      environment: foundationEnvironment,
    },
    dependencies,
    baseEnvironment: dense.baseEnvironment,
    events: dense.events,
    resultEnvironment: dense.resultEnvironment,
  };
  return deepFreeze({ ...body, digest: sha256Hex(canonical(body)) });
}

/** The proof-checked bootstrap prelude over the bare axioms, as replayable events. */
export interface FoundationImage {
  readonly format: "grace17.foundation-image";
  readonly version: 1;
  readonly profile: SetTheoryProfile;
  /** Digest of the bare axiomatic kernel the events extend. */
  readonly baseEnvironment: string;
  readonly events: readonly DenseCompiledEvent[];
  /** Digest of the completed foundation, the identity every compiled module names. */
  readonly resultEnvironment: string;
}

/**
 * Compile the bootstrap prelude: `bare` is the axiomatic kernel before the
 * prelude and `bootstrapped` the same kernel after it, at the checkpoint
 * taken in between. The prelude is the foundation itself, so unlike a
 * module it has no foundation to be checked against; replay verifies that
 * the result digest is the foundation digest the prelude's elaboration had.
 */
export function compileFoundationImage(bare: Kernel, bootstrapped: Kernel, checkpoint: KernelAdmissionCheckpoint): FoundationImage {
  const dense = compileDenseKernelModule(bare, bootstrapped, checkpoint, { module: "Grace.Foundation" });
  const foundation = bootstrapped.foundationDigest();
  if (foundation === undefined || foundation !== dense.resultEnvironment) throw new KernelError("Foundation image must end at the foundation boundary");
  return deepFreeze({
    format: "grace17.foundation-image", version: 1,
    profile: bare.capabilities.setTheory ?? "none",
    baseEnvironment: dense.baseEnvironment, events: dense.events, resultEnvironment: dense.resultEnvironment,
  });
}

/**
 * Replay a foundation image onto a bare axiomatic kernel whose boundary is
 * not yet fixed, checking every proof as admission does, and confirm the
 * kernel reaches exactly the recorded foundation digest.
 */
export function replayFoundationImage(kernel: Kernel, image: FoundationImage): void {
  if (!isRecord(image) || image.format !== "grace17.foundation-image" || image.version !== 1 ||
      !isDigest(image.baseEnvironment) || !isDigest(image.resultEnvironment) || !Array.isArray(image.events)) {
    throw new KernelError("Malformed foundation image");
  }
  validateDenseEvents(image.events);
  if ((kernel.capabilities.setTheory ?? "none") !== image.profile || kernel.digest() !== image.baseEnvironment) {
    throw new KernelError("Foundation image belongs to a different axiomatic kernel");
  }
  for (const item of image.events) {
    if (item.kind === "admission") replayAdmission(kernel, item.event);
    else kernel.addTheoremMachineBatch(item.statements, item.machine);
  }
  if (kernel.digest() !== image.resultEnvironment) throw new KernelError("Foundation image replay produced the wrong environment");
}

/**
 * Compile a module whose base is the foundation plus exactly its dependency
 * closure, in any topological order. Environment digests are order-free, so
 * `baseEnvironment` identifies the closure as a set, and a strict checker
 * reconstructs it by replaying the listed artifacts with receipt checks before
 * replaying this module exactly. The base may carry no receipt outside the
 * closure and no admission outside those replays; the module store builds it
 * that way, and an exact replay of the artifact confirms the claim.
 */
export function compileSeparateKernelModuleOverClosure(
  foundation: Kernel,
  base: Kernel,
  completed: Kernel,
  checkpoint: KernelAdmissionCheckpoint,
  options: {
    readonly module: string;
    readonly sourceDigest?: string;
    /** Complete dependency closure in a topological order. */
    readonly dependencies: readonly CompiledModuleDependency[];
  },
): SeparateCompiledKernelModule {
  const foundationEnvironment = foundation.foundationDigest();
  if (foundationEnvironment === undefined || foundation.digest() !== foundationEnvironment) {
    throw new KernelError("Separate compilation requires an exact completed foundation kernel");
  }
  if (base.foundationDigest() !== foundationEnvironment || completed.foundationDigest() !== foundationEnvironment) {
    throw new KernelError("Separate compilation kernels use a different foundation");
  }
  const dependencies = [...options.dependencies];
  validateDependencies(dependencies, "separate compiled module");
  const receipts = base.checkedModuleReceipts();
  if (receipts.length !== dependencies.length ||
      dependencies.some(dependency => base.checkedModuleReceipt(dependency.module) !== dependency.digest)) {
    throw new KernelError("Separate compilation base does not carry exactly the dependency closure receipts");
  }
  if (dependencies.length === 0 && base.digest() !== foundationEnvironment) {
    throw new KernelError("Separate compilation base is not the exact foundation");
  }
  const dense = compileDenseKernelModule(base, completed, checkpoint, {
    module: options.module, sourceDigest: options.sourceDigest,
  });
  const body = {
    format: "grace17.compiled-module" as const,
    version: 3 as const,
    module: options.module,
    source: options.sourceDigest ?? "",
    foundation: {
      profile: foundation.capabilities.setTheory ?? "none",
      environment: foundationEnvironment,
    },
    dependencies,
    baseEnvironment: dense.baseEnvironment,
    events: dense.events,
    resultEnvironment: dense.resultEnvironment,
  };
  return deepFreeze({ ...body, digest: sha256Hex(canonical(body)) });
}

export function encodeSeparateKernelModule(module: SeparateCompiledKernelModule): Uint8Array {
  validateSeparateEnvelope(module);
  return new TextEncoder().encode(canonical(module));
}

export function decodeSeparateKernelModule(bytes: Uint8Array): SeparateCompiledKernelModule {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed separate compiled module encoding"); }
  validateSeparateEnvelope(value);
  return value;
}

/**
 * Reference-checker path: the supplied kernel must be precisely foundation +
 * the declared dependency closure. This is the preferred independent-checker
 * algorithm because it needs no receipt database beyond the current prefix.
 */
export function replaySeparateKernelModuleExact(
  base: Kernel, compiled: SeparateCompiledKernelModule,
): Kernel {
  return replaySeparate(base, compiled, true);
}

/**
 * Editor/cache path: unrelated checked declarations may already be present,
 * but all dependency receipts and the foundation identity must match. Every
 * event is still replayed through checked kernel operations.
 */
export function replaySeparateKernelModule(
  base: Kernel, compiled: SeparateCompiledKernelModule,
  options: { readonly machineProofLoader?: (name: string) => ProofMachineModuleProgram } = {},
): Kernel {
  return replaySeparate(base, compiled, false, options.machineProofLoader);
}

/** Replay onto `kernel` itself rather than a fork; a failure leaves it partly extended. */
export function replaySeparateKernelModuleInPlace(
  kernel: Kernel, compiled: SeparateCompiledKernelModule,
  options: { readonly machineProofLoader?: (name: string) => ProofMachineModuleProgram } = {},
): void {
  replaySeparate(kernel, compiled, false, options.machineProofLoader, true);
}

function replaySeparate(
  base: Kernel, compiled: SeparateCompiledKernelModule, exact: boolean,
  machineProofLoader?: (name: string) => ProofMachineModuleProgram, inPlace = false,
): Kernel {
  validateSeparateEnvelope(compiled);
  if ((base.capabilities.setTheory ?? "none") !== compiled.foundation.profile ||
      base.foundationDigest() !== compiled.foundation.environment) {
    throw new KernelError("Separate compiled module belongs to a different foundation");
  }
  for (const dependency of compiled.dependencies) {
    if (base.checkedModuleReceipt(dependency.module) !== dependency.digest) {
      throw new KernelError(`Missing or stale compiled dependency ${dependency.module}`);
    }
  }
  if (exact && base.digest() !== compiled.baseEnvironment) {
    throw new KernelError("Separate compiled module belongs to a different exact dependency prefix");
  }
  const existing = base.checkedModuleReceipt(compiled.module);
  if (existing !== undefined) {
    if (existing !== compiled.digest) throw new KernelError(`Conflicting checked module receipt: ${compiled.module}`);
    return inPlace ? base : base.fork();
  }
  const result = inPlace ? base : base.fork();
  for (const item of compiled.events) {
    if (item.kind === "admission") replayAdmission(result, item.event);
    else result.addTheoremMachineBatch(item.statements, item.machine, machineProofLoader);
  }
  if (exact && result.digest() !== compiled.resultEnvironment) {
    throw new KernelError("Separate compiled module replay produced the wrong environment");
  }
  result.recordCheckedModule(compiled.module, compiled.digest, compiled.resultEnvironment);
  return result;
}

function encodeAdmission(event: KernelAdmissionEvent): CompiledAdmissionEvent {
  if (event.operation === "addAxiom") throw new KernelError("Compiled library modules may not introduce axioms");
  return Object.freeze({ operation: event.operation, payload: encodeValue(event.payload) });
}

function encodeValue(value: unknown): unknown {
  if (isProof(value)) return Object.freeze({ $grace17ProofDag: encodeProofDag(value) } satisfies EncodedProof);
  if (Array.isArray(value)) return Object.freeze(value.map(encodeValue));
  if (isRecord(value)) return Object.freeze(Object.fromEntries(
    Object.entries(value).map(([key, child]) => [key, encodeValue(child)]),
  ));
  if (value === null || typeof value === "string" || typeof value === "number" || typeof value === "boolean") return value;
  throw new KernelError("Kernel admission event is not canonically serializable");
}

function decodeValue(value: unknown): unknown {
  if (isEncodedProof(value)) {
    const proofs = decodeProofDag(value.$grace17ProofDag);
    return proofs[value.$grace17ProofDag.root]!;
  }
  if (Array.isArray(value)) return value.map(decodeValue);
  if (isRecord(value)) return Object.fromEntries(Object.entries(value).map(([key, child]) => [key, decodeValue(child)]));
  return value;
}

function replayAdmission(kernel: Kernel, encoded: CompiledAdmissionEvent): void {
  if (!isRecord(encoded) || !admissionOperations.has(encoded.operation as CompiledAdmissionOperation) || !isRecord(encoded.payload)) {
    throw new KernelError("Malformed compiled admission event");
  }
  const payload = decodeValue(encoded.payload) as Record<string, unknown>;
  switch (encoded.operation) {
    case "declareFunction": kernel.declareFunction(stringField(payload, "name"), integerField(payload, "arity")); return;
    case "declarePredicate": kernel.declarePredicate(stringField(payload, "name"), integerField(payload, "arity")); return;
    case "addTheorem": kernel.addTheorem(
      stringField(payload, "name"), payload.statement as Parameters<Kernel["addTheorem"]>[1], payload.proof as Proof,
    ); return;
    case "defineFunction": kernel.defineFunction(
      stringField(payload, "name"), stringArrayField(payload, "parameters"), payload.body as Parameters<Kernel["defineFunction"]>[2],
    ); return;
    case "definePredicate": kernel.definePredicate(
      stringField(payload, "name"), stringArrayField(payload, "parameters"), payload.body as Parameters<Kernel["definePredicate"]>[2],
    ); return;
    case "declareDatatype": kernel.declareDatatype(recordField(payload, "spec") as unknown as Parameters<Kernel["declareDatatype"]>[0]); return;
    case "registerNaturalDatatype": kernel.registerNaturalDatatype(); return;
    case "defineStructuralFunction": kernel.defineStructuralFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineStructuralFunction"]>[0]); return;
    case "defineWellFoundedFunction": kernel.defineWellFoundedFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineWellFoundedFunction"]>[0]); return;
    case "defineSubset": kernel.defineSubset(
      stringField(payload, "name"), stringArrayField(payload, "parameters"), stringField(payload, "element"),
      payload.bound as Parameters<Kernel["defineSubset"]>[3], payload.condition as Parameters<Kernel["defineSubset"]>[4],
    ); return;
    case "reifyUnaryOperation": kernel.reifyUnaryOperation(recordField(payload, "options") as unknown as Parameters<Kernel["reifyUnaryOperation"]>[0]); return;
    case "defineReplacement": kernel.defineReplacement(recordField(payload, "options") as unknown as Parameters<Kernel["defineReplacement"]>[0]); return;
    case "defineUniqueFunction": kernel.defineUniqueFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineUniqueFunction"]>[0]); return;
    case "defineWellFoundedSetFunction": kernel.defineWellFoundedSetFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineWellFoundedSetFunction"]>[0]); return;
    case "defineMembershipRecursiveFunction": kernel.defineMembershipRecursiveFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineMembershipRecursiveFunction"]>[0]); return;
    case "defineTransfiniteFunction": kernel.defineTransfiniteFunction(recordField(payload, "options") as unknown as Parameters<Kernel["defineTransfiniteFunction"]>[0]); return;
  }
}

const admissionOperations = new Set<CompiledAdmissionOperation>([
  "declareFunction", "declarePredicate", "addTheorem", "defineFunction", "definePredicate",
  "declareDatatype", "registerNaturalDatatype", "defineStructuralFunction", "defineWellFoundedFunction", "defineSubset", "reifyUnaryOperation",
  "defineReplacement", "defineUniqueFunction", "defineWellFoundedSetFunction", "defineMembershipRecursiveFunction",
  "defineTransfiniteFunction",
]);

function validateEnvelope(value: unknown): asserts value is CompiledKernelModule {
  if (isRecord(value) && validatedModules.has(value)) return;
  if (!isRecord(value) || value.format !== "grace17.compiled-module" || value.version !== 1 ||
      typeof value.module !== "string" || !value.module || typeof value.source !== "string" ||
      (value.source !== "" && !isDigest(value.source)) ||
      !isDigest(value.baseEnvironment) || !isDigest(value.resultEnvironment) || !isDigest(value.digest) ||
      !Array.isArray(value.dependencies) || !Array.isArray(value.events)) {
    throw new KernelError("Malformed compiled module envelope");
  }
  if (value.dependencies.some(item => !isRecord(item) || typeof item.module !== "string" || !item.module || !isDigest(item.digest)) ||
      new Set(value.dependencies.map(item => (item as Record<string, unknown>).module)).size !== value.dependencies.length) {
    throw new KernelError("Malformed compiled module dependencies");
  }
  if (value.events.some(event => !isRecord(event) || !admissionOperations.has(event.operation as CompiledAdmissionOperation) || !isRecord(event.payload))) {
    throw new KernelError("Malformed compiled module events");
  }
  const { digest, ...body } = value;
  if (sha256Hex(canonical(body)) !== digest) throw new KernelError("Malformed or corrupted compiled module");
  deepFreeze(value);
  validatedModules.add(value);
}

function validateDenseEnvelope(value: unknown): asserts value is DenseCompiledKernelModule {
  if (isRecord(value) && validatedModules.has(value)) return;
  if (!isRecord(value) || value.format !== "grace17.compiled-module" || value.version !== 2 ||
      typeof value.module !== "string" || !value.module || typeof value.source !== "string" ||
      (value.source !== "" && !isDigest(value.source)) || !isDigest(value.baseEnvironment) ||
      !isDigest(value.resultEnvironment) || !isDigest(value.digest) ||
      !Array.isArray(value.dependencies) || !Array.isArray(value.events)) {
    throw new KernelError("Malformed dense compiled module envelope");
  }
  if (value.dependencies.some(item => !isRecord(item) || typeof item.module !== "string" || !item.module || !isDigest(item.digest)) ||
      new Set(value.dependencies.map(item => (item as Record<string, unknown>).module)).size !== value.dependencies.length) {
    throw new KernelError("Malformed dense compiled module dependencies");
  }
  for (const item of value.events) {
    if (!isRecord(item)) throw new KernelError("Malformed dense compiled module event");
    if (item.kind === "admission") {
      if (!isRecord(item.event) || !admissionOperations.has(item.event.operation as CompiledAdmissionOperation) ||
          !isRecord(item.event.payload)) throw new KernelError("Malformed dense admission event");
    } else if (item.kind === "theoremBatch") {
      if (!Array.isArray(item.statements) || item.statements.length === 0 || !isRecord(item.machine) ||
          item.statements.some(statement => !isRecord(statement) || typeof statement.name !== "string" ||
            !statement.name || !isRecord(statement.statement))) {
        throw new KernelError("Malformed dense theorem batch");
      }
    } else throw new KernelError("Unknown dense compiled module event");
  }
  const { digest, ...body } = value;
  if (sha256Hex(canonical(body)) !== digest) throw new KernelError("Malformed or corrupted dense compiled module");
  deepFreeze(value);
  validatedModules.add(value);
}

/**
 * Accept a separate compiled module whose bytes a loader has already
 * verified against the digest its dependents recorded, so the envelope is
 * not re-serialized to check its own digest field. Every proof in it is
 * still replayed by the kernel on admission.
 */
export function acceptVerifiedSeparateModule(value: unknown): asserts value is SeparateCompiledKernelModule {
  validateSeparateShape(value);
  // The loader owns the parsed object; what the kernel retains from it, it
  // freezes itself on admission, and the programs are not retained at all.
  validatedModules.add(value);
}

function validateSeparateEnvelope(value: unknown): asserts value is SeparateCompiledKernelModule {
  if (isRecord(value) && validatedModules.has(value)) return;
  validateSeparateShape(value);
  const { digest, ...body } = value;
  if (sha256Hex(canonical(body)) !== digest) throw new KernelError("Malformed or corrupted separate compiled module");
  deepFreeze(value);
  validatedModules.add(value);
}

function validateSeparateShape(value: unknown): asserts value is SeparateCompiledKernelModule {
  if (!isRecord(value) || value.format !== "grace17.compiled-module" || value.version !== 3 ||
      typeof value.module !== "string" || !value.module || typeof value.source !== "string" ||
      (value.source !== "" && !isDigest(value.source)) || !isRecord(value.foundation) ||
      !setTheoryProfiles.has(value.foundation.profile as SetTheoryProfile) ||
      !isDigest(value.foundation.environment) || !isDigest(value.baseEnvironment) ||
      !isDigest(value.resultEnvironment) || !isDigest(value.digest) ||
      !Array.isArray(value.dependencies) || !Array.isArray(value.events)) {
    throw new KernelError("Malformed separate compiled module envelope");
  }
  validateDependencies(value.dependencies as unknown as readonly CompiledModuleDependency[], "separate compiled module");
  validateDenseEvents(value.events);
}

function validateDenseEvents(events: readonly unknown[]): void {
  for (const item of events) {
    if (!isRecord(item)) throw new KernelError("Malformed dense compiled module event");
    if (item.kind === "admission") {
      if (!isRecord(item.event) || !admissionOperations.has(item.event.operation as CompiledAdmissionOperation) ||
          !isRecord(item.event.payload)) throw new KernelError("Malformed dense admission event");
    } else if (item.kind === "theoremBatch") {
      if (!Array.isArray(item.statements) || item.statements.length === 0 || !isRecord(item.machine) ||
          item.statements.some(statement => !isRecord(statement) || typeof statement.name !== "string" ||
            !statement.name || !isRecord(statement.statement))) {
        throw new KernelError("Malformed dense theorem batch");
      }
    } else throw new KernelError("Unknown dense compiled module event");
  }
}

function validateDependencies(dependencies: readonly CompiledModuleDependency[], context: string): void {
  if (dependencies.some(item => !isRecord(item) || typeof item.module !== "string" || !item.module || !isDigest(item.digest)) ||
      new Set(dependencies.map(item => item.module)).size !== dependencies.length) {
    throw new KernelError(`Malformed ${context} dependencies`);
  }
}

const setTheoryProfiles = new Set<SetTheoryProfile>(["none", "ZF", "ZFC", "ZFG"]);

function isProof(value: unknown): value is Proof {
  return isRecord(value) && typeof value.rule === "string" && proofRules.has(value.rule);
}

function isEncodedProof(value: unknown): value is EncodedProof {
  return isRecord(value) && Object.keys(value).length === 1 && isRecord(value.$grace17ProofDag);
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function isDigest(value: unknown): value is string {
  return typeof value === "string" && /^[0-9a-f]{64}$/.test(value);
}

function stringField(record: Record<string, unknown>, name: string): string {
  const value = record[name];
  if (typeof value !== "string") throw new KernelError(`Malformed compiled event field ${name}`);
  return value;
}

function integerField(record: Record<string, unknown>, name: string): number {
  const value = record[name];
  if (!Number.isSafeInteger(value)) throw new KernelError(`Malformed compiled event field ${name}`);
  return value as number;
}

function stringArrayField(record: Record<string, unknown>, name: string): readonly string[] {
  const value = record[name];
  if (!Array.isArray(value) || value.some(item => typeof item !== "string")) {
    throw new KernelError(`Malformed compiled event field ${name}`);
  }
  return value;
}

function recordField(record: Record<string, unknown>, name: string): Record<string, unknown> {
  const value = record[name];
  if (!isRecord(value)) throw new KernelError(`Malformed compiled event field ${name}`);
  return value;
}

function deepFreeze<T>(value: T): T {
  freezeCertificate(value);
  return value;
}
