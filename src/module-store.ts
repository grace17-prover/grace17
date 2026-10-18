// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { existsSync, mkdirSync, readFileSync, renameSync, writeFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { canonical } from "./ast.ts";
import {
  compileSeparateKernelModuleOverClosure, acceptVerifiedSeparateModule, compileFoundationImage, replayFoundationImage, replaySeparateKernelModule, replaySeparateKernelModuleInPlace, type FoundationImage, replaySeparateKernelModuleExact,
  type SeparateCompiledKernelModule,
} from "./compiled-module.ts";
import { sha256Hex } from "./hash.ts";
import { Kernel, KernelError, type SetTheoryProfile } from "./kernel.ts";
import type { ProofMachineModuleProgram } from "./machine.ts";
import { scanModule, setLibraryModuleLoader, type LoadedModule } from "./module-source-loader.ts";
import { moduleNameFromPath, resolveImportName } from "./module-names.ts";
import {
  captureSurfaceBaseline, elaborateModule, exportSurfaceEnvironmentDelta, forkSurfaceEnvironment, moduleReport, moveSurfaceEnvironment,
  mergeSurfaceEnvironmentDelta, setSurfaceTraceCapture, SurfaceError,
  type SurfaceEnvironmentDelta, type SurfaceSorry, type SurfaceTheoremLocation,
} from "./surface.ts";
import { bootstrapSourceDigest, createSetTheoryBareKernel, createSetTheoryKernel, createSetTheoryKernelFromImage, installSetTheoryBootstrap } from "./zfg.ts";

/**
 * One checked module, compiled against its import closure. The kernel events
 * replay through checked kernel operations on any kernel that carries the
 * closure's receipts; the surface delta and the loaded record are editor and
 * report data with no logical authority.
 */
export interface ModuleArtifact {
  readonly format: "grace17.module-artifact";
  readonly version: 1;
  readonly module: string;
  /** Source path relative to its module root, for reports. */
  readonly file: string;
  readonly sourceDigest: string;
  readonly profile: SetTheoryProfile;
  readonly imports: readonly string[];
  /** Transitive imports in replay order, each with the artifact it was built against. */
  readonly closure: readonly { readonly module: string; readonly digest: string }[];
  readonly compiled: SeparateCompiledKernelModule;
  readonly surface: SurfaceEnvironmentDelta;
  readonly loaded: {
    readonly definitions: readonly string[];
    readonly theorems: readonly string[];
    readonly theoremLocations: readonly SurfaceTheoremLocation[];
    readonly sorries: readonly SurfaceSorry[];
  };
  readonly digest: string;
}

export interface ModuleStoreOptions {
  /** Directories holding `.g17` sources, searched in order. */
  readonly roots: readonly string[];
  /** Directory holding one `<Module.Name>.g17a` file per module. */
  readonly store: string;
  readonly profile?: SetTheoryProfile;
  /** Replay each new artifact exactly on its base before writing it. */
  readonly verify?: boolean;
  readonly log?: (line: string) => void;
}

export interface ModuleStoreBuildReport {
  /** Modules compiled in this run, in build order. */
  readonly built: readonly string[];
  /** Modules whose artifacts were already current. */
  readonly reused: readonly string[];
  readonly artifacts: ReadonlyMap<string, ModuleArtifact>;
}

interface ScannedSource {
  readonly module: string;
  readonly file: string;
  readonly relative: string;
  readonly source: string;
  readonly digest: string;
  readonly imports: readonly string[];
}

/** Bring the artifacts of `modules` and their closures up to date. */
export function buildModuleStore(modules: readonly string[], options: ModuleStoreOptions): ModuleStoreBuildReport {
  const profile = options.profile ?? "ZFG";
  const log = options.log ?? (() => {});
  // The foundation image lets later loads skip elaborating the prelude.
  let foundationArtifact: FoundationArtifact | undefined;
  try { foundationArtifact = readFoundationArtifact(foundationArtifactPath(options.store, profile)); }
  catch (error) { if (!(error instanceof KernelError)) throw error; }
  if (!foundationArtifact || foundationArtifact.sourceDigest !== bootstrapSourceDigest()) writeFoundationArtifact(options.store, profile);
  const sources = scanSources(modules, options.roots);
  const order = topologicalOrder(sources);
  const closures = new Map<string, readonly string[]>();
  const closureOf = (name: string): readonly string[] => {
    const known = closures.get(name);
    if (known) return known;
    const result: string[] = [];
    for (const imported of sources.get(name)!.imports) {
      for (const item of [...closureOf(imported), imported]) if (!result.includes(item)) result.push(item);
    }
    closures.set(name, result);
    return result;
  };

  mkdirSync(options.store, { recursive: true });
  const artifacts = new Map<string, ModuleArtifact>();
  const built: string[] = [];
  const reused: string[] = [];
  // Created only when a module needs building, from the foundation image.
  let foundationKernel: Kernel | undefined;
  const foundation = (): Kernel => {
    if (!foundationKernel) { foundationKernel = createStoreKernel(options.store, profile); setSurfaceTraceCapture(foundationKernel, false); }
    return foundationKernel;
  };
  // Completed kernels of recently built modules, each carrying exactly its
  // closure's receipts plus its own. A dependent forks the one covering the
  // most of its closure and replays only the rest.
  const bases: { readonly receipts: ReadonlySet<string>; readonly kernel: Kernel }[] = [];
  const maximumBases = 32;

  for (const name of order) {
    const source = sources.get(name)!;
    const closure = closureOf(name);
    const closureEntries = closure.map(module => ({ module, digest: artifacts.get(module)!.digest }));
    const current = readArtifact(artifactPath(options.store, name));
    if (current && current.profile === profile && current.sourceDigest === source.digest &&
        current.closure.length === closureEntries.length &&
        current.closure.every((item, index) => item.module === closureEntries[index]!.module && item.digest === closureEntries[index]!.digest)) {
      artifacts.set(name, current);
      reused.push(name);
      continue;
    }
    const started = globalThis.performance?.now() ?? 0;
    const closureSet = new Set(closure);
    const seed = bases.filter(item => [...item.receipts].every(module => closureSet.has(module)))
      .sort((left, right) => right.receipts.size - left.receipts.size)[0];
    let base = seed ? seed.kernel.fork() : foundation().fork();
    forkSurfaceEnvironment(seed ? seed.kernel : foundation(), base);
    for (const module of closure) {
      if (base.checkedModuleReceipt(module) !== undefined) continue;
      base = replayArtifact(base, artifacts.get(module)!);
    }
    const completed = base.fork();
    forkSurfaceEnvironment(base, completed);
    setSurfaceTraceCapture(completed, false);
    const checkpoint = base.admissionCheckpoint();
    const baseline = captureSurfaceBaseline(completed);
    let elaborated: ReturnType<typeof elaborateModule>;
    try { elaborated = elaborateModule(completed, source.source, { moduleName: source.module }); }
    catch (error) {
      if (error instanceof SurfaceError) error.file ??= source.file;
      throw error;
    }
    const compiled = compileSeparateKernelModuleOverClosure(foundation(), base, completed, checkpoint, {
      module: name,
      sourceDigest: source.digest,
      dependencies: closure.map(module => ({ module, digest: artifacts.get(module)!.compiled.digest })),
    });
    if (options.verify) {
      const replayed = replaySeparateKernelModuleExact(base, compiled);
      if (replayed.digest() !== completed.digest()) throw new KernelError(`Artifact for ${name} does not replay to its source environment`);
    }
    completed.recordCheckedModule(name, compiled.digest, compiled.resultEnvironment);
    const surface = exportSurfaceEnvironmentDelta(completed, baseline, name, compiled.digest);
    const body = {
      format: "grace17.module-artifact" as const,
      version: 1 as const,
      module: name,
      file: source.relative,
      sourceDigest: source.digest,
      profile,
      imports: source.imports,
      closure: closureEntries,
      compiled,
      surface,
      loaded: {
        definitions: elaborated.definitions,
        theorems: elaborated.theorems,
        theoremLocations: elaborated.theoremLocations,
        sorries: elaborated.sorries,
      },
    };
    const text = canonical(body);
    const artifact: ModuleArtifact = { ...body, digest: sha256Hex(text) };
    // The digest comes first and covers the canonical text that follows, so a
    // reader hashes the bytes it was given instead of re-serializing them.
    writeAtomically(artifactPath(options.store, name), `{"digest":"${artifact.digest}",${text.slice(1)}\n`);
    artifacts.set(name, artifact);
    built.push(name);
    bases.push({ receipts: new Set([...closure, name]), kernel: completed });
    while (bases.length > maximumBases) bases.shift();
    const elapsed = globalThis.performance ? ((globalThis.performance.now() - started) / 1000).toFixed(1) : "?";
    log(`built ${name} (${elaborated.definitions.length} definitions, ${elaborated.theorems.length} theorems, ${elapsed}s)`);
  }
  return { built, reused, artifacts };
}

/**
 * Replay the artifacts of `modules` and their closures onto `kernel`, which
 * must be a fresh kernel of the artifacts' foundation or one that already
 * carries compatible receipts. Returns the extended kernel; the argument is
 * unchanged.
 */
export function loadModuleStore(
  kernel: Kernel, modules: readonly string[], store: string,
): { readonly kernel: Kernel; readonly loaded: readonly LoadedModule[] } {
  const artifacts = new Map<string, ModuleArtifact>();
  const read = (name: string, digest?: string): ModuleArtifact => {
    const known = artifacts.get(name);
    if (known) {
      if (digest !== undefined && known.digest !== digest) throw new KernelError(`Artifact store holds a different ${name} than its dependents expect`);
      return known;
    }
    const artifact = readArtifact(artifactPath(store, name));
    if (!artifact) throw new KernelError(`Artifact store has no artifact for ${name}`);
    if (digest !== undefined && artifact.digest !== digest) throw new KernelError(`Artifact store holds a different ${name} than its dependents expect`);
    artifacts.set(name, artifact);
    return artifact;
  };
  const order: string[] = [];
  const visit = (name: string, digest?: string): void => {
    if (order.includes(name)) return;
    const artifact = read(name, digest);
    for (const item of artifact.closure) visit(item.module, item.digest);
    order.push(name);
  };
  modules.forEach(name => visit(name));

  let current = kernel;
  const loaded: LoadedModule[] = [];
  for (const name of order) {
    const artifact = artifacts.get(name)!;
    if (current.checkedModuleReceipt(name) === undefined) {
      current = replayArtifact(current, artifact, artifactPath(store, name), current !== kernel);
    }
    loaded.push({
      file: artifact.file,
      module: name,
      definitions: artifact.loaded.definitions,
      theorems: artifact.loaded.theorems,
      theoremLocations: artifact.loaded.theoremLocations,
      evaluations: [],
      sorries: artifact.loaded.sorries,
    });
  }
  return { kernel: current, loaded };
}

/** The bootstrap prelude compiled over the bare axioms, with its surface delta. */
export interface FoundationArtifact {
  readonly format: "grace17.foundation-artifact";
  readonly version: 1;
  readonly profile: SetTheoryProfile;
  /** Digest of the bootstrap sources the image was compiled from. */
  readonly sourceDigest: string;
  readonly image: FoundationImage;
  readonly surface: SurfaceEnvironmentDelta;
  readonly digest: string;
}

export function foundationArtifactPath(store: string, profile: SetTheoryProfile): string {
  return join(store, `foundation.${profile}.g17f`);
}

/**
 * Compile the foundation of `profile` into the store: the bootstrap prelude
 * elaborated once, over the bare axiomatic kernel, as replayable events.
 */
export function writeFoundationArtifact(store: string, profile: SetTheoryProfile): FoundationArtifact {
  const bare = createSetTheoryBareKernel({ profile });
  const checkpoint = bare.admissionCheckpoint();
  const baseline = captureSurfaceBaseline(bare);
  const bootstrapped = bare.fork();
  forkSurfaceEnvironment(bare, bootstrapped);
  installSetTheoryBootstrap(bootstrapped);
  bootstrapped.recordFoundationBoundary();
  const image = compileFoundationImage(bare, bootstrapped, checkpoint);
  const surface = exportSurfaceEnvironmentDelta(bootstrapped, baseline, "Grace.Foundation", image.resultEnvironment);
  const body = { format: "grace17.foundation-artifact" as const, version: 1 as const, profile, sourceDigest: bootstrapSourceDigest(), image, surface };
  const text = canonical(body);
  const artifact: FoundationArtifact = { ...body, digest: sha256Hex(text) };
  mkdirSync(store, { recursive: true });
  writeAtomically(foundationArtifactPath(store, profile), `{"digest":"${artifact.digest}",${text.slice(1)}\n`);
  return artifact;
}

function readFoundationArtifact(path: string): FoundationArtifact | undefined {
  if (!existsSync(path)) return undefined;
  const text = readFileSync(path, "utf8");
  let value: unknown;
  try { value = JSON.parse(text); }
  catch { return undefined; }
  const prefix = /^\{"digest":"([0-9a-f]{64})",/.exec(text);
  if (!prefix || sha256Hex(`{${text.slice(prefix[0].length, text.endsWith("\n") ? -1 : undefined)}`) !== prefix[1]) {
    throw new KernelError(`Corrupted foundation artifact ${path}`);
  }
  if (!isRecord(value) || value.format !== "grace17.foundation-artifact" || value.version !== 1 || typeof value.profile !== "string" ||
      !isDigest(value.sourceDigest) || !isRecord(value.image) || !isRecord(value.surface) || value.digest !== prefix[1]) {
    throw new KernelError(`Malformed foundation artifact ${path}`);
  }
  return value as unknown as FoundationArtifact;
}

/**
 * The foundation kernel for a store: replayed from the store's foundation
 * artifact when it exists and was compiled from the current bootstrap
 * sources, and elaborated from those sources otherwise. Either way the
 * kernel reaches the same foundation digest, which the replay verifies.
 */
export function createStoreKernel(store: string, profile: SetTheoryProfile): Kernel {
  const artifact = readFoundationArtifact(foundationArtifactPath(store, profile));
  if (!artifact || artifact.profile !== profile || artifact.sourceDigest !== bootstrapSourceDigest()) return createSetTheoryKernel({ profile });
  const kernel = createSetTheoryKernelFromImage({ profile }, bare => replayFoundationImage(bare, artifact.image));
  mergeSurfaceEnvironmentDelta(kernel, artifact.surface, "foundation");
  return kernel;
}

/** Write through a temporary file so concurrent builders never read a partial artifact. */
function writeAtomically(path: string, text: string): void {
  const temporary = `${path}.${process.pid}.tmp`;
  writeFileSync(temporary, text);
  renameSync(temporary, path);
}

function replayArtifactInPlace(kernel: Kernel, artifact: ModuleArtifact, path: string): void {
  const { digest, module } = artifact;
  let reloaded: ModuleArtifact | undefined;
  replaySeparateKernelModuleInPlace(kernel, artifact.compiled, { machineProofLoader: name => {
    reloaded ??= readArtifact(path);
    if (!reloaded || reloaded.digest !== digest) throw new KernelError(`Artifact store no longer holds the loaded ${module}`);
    const batch = reloaded.compiled.events.find(item => item.kind === "theoremBatch" && item.statements.some(statement => statement.name === name));
    if (!batch || batch.kind !== "theoremBatch") throw new KernelError(`Artifact ${module} has no machine proof of ${name}`);
    return batch.machine;
  } });
  mergeSurfaceEnvironmentDelta(kernel, artifact.surface);
}

/**
 * Serve library imports from a store for every source load in this process:
 * an imported module under one of `roots` is built into `store/<profile>`
 * when missing or stale and replayed, with its closure, onto the loading
 * kernel in place of elaborating its source. Tests use this so a file that
 * imports a large closure loads it in well under a second.
 */
export function installLibraryStore(store: string, roots: readonly string[]): void {
  setLibraryModuleLoader((kernel, name, entries) => {
    const profile = kernel.capabilities.setTheory;
    if (!profile || profile === "none" || kernel.foundationDigest() === undefined) return false;
    const relative = `${name.split(".").join("/")}.g17`;
    if (!roots.some(root => existsSync(resolve(root, relative)))) return false;
    const directory = join(store, profile);
    buildModuleStore([name], { roots, store: directory, profile });
    const order: string[] = [];
    // A module elaborated from source earlier is loaded but carries no
    // receipt, so artifacts depending on it cannot replay: such a closure is
    // left to source loading too.
    const present = new Set(moduleReport(kernel).map(record => record.name));
    let sourceLoaded = false;
    const visit = (module: string): void => {
      if (order.includes(module) || kernel.checkedModuleReceipt(module) !== undefined) return;
      if (present.has(module)) { sourceLoaded = true; return; }
      const artifact = readArtifact(artifactPath(directory, module));
      if (!artifact) throw new KernelError(`Artifact store has no artifact for ${module}`);
      for (const item of artifact.closure) visit(item.module);
      order.push(module);
    };
    visit(name);
    // A module the caller elaborates from source must not also arrive
    // through the store, so such a closure is left to source loading.
    if (sourceLoaded || order.some(module => entries.has(module))) return false;
    for (const module of order) {
      const path = artifactPath(directory, module);
      replayArtifactInPlace(kernel, readArtifact(path)!, path);
    }
    return true;
  });
}

/** The module a `.g17` file declares, when it declares one. */
export function declaredModule(file: string, roots: readonly string[] = ["lib"]): string | undefined {
  return scanModule(readFileSync(file, "utf8"), file, path => moduleNameFromPath(resolve(path), roots.map(root => resolve(root))) ?? moduleNameFromPath(path, roots)).name;
}

export function artifactPath(store: string, module: string): string {
  return join(store, `${module}.g17a`);
}

function replayArtifact(base: Kernel, artifact: ModuleArtifact, path: string, owned: boolean): Kernel {
  // The verified programs are reloaded from the same artifact if an audit
  // asks for them; the reload must produce the digest that was loaded. The
  // loader holds only the digest and name, so the parsed artifact is freed.
  const { digest, module } = artifact;
  let reloaded: ModuleArtifact | undefined;
  const machineProofLoader = (name: string): ProofMachineModuleProgram => {
    reloaded ??= readArtifact(path);
    if (!reloaded || reloaded.digest !== digest) throw new KernelError(`Artifact store no longer holds the loaded ${module}`);
    const batch = reloaded.compiled.events.find(item => item.kind === "theoremBatch" && item.statements.some(statement => statement.name === name));
    if (!batch || batch.kind !== "theoremBatch") throw new KernelError(`Artifact ${module} has no machine proof of ${name}`);
    return batch.machine;
  };
  const next = replaySeparateKernelModule(base, artifact.compiled, { machineProofLoader });
  if (owned) moveSurfaceEnvironment(base, next); else forkSurfaceEnvironment(base, next);
  mergeSurfaceEnvironmentDelta(next, artifact.surface);
  return next;
}

function readArtifact(path: string): ModuleArtifact | undefined {
  if (!existsSync(path)) return undefined;
  const text = readFileSync(path, "utf8");
  let value: unknown;
  try { value = JSON.parse(text); }
  catch { return undefined; }
  const prefix = /^\{"digest":"([0-9a-f]{64})",/.exec(text);
  if (!prefix || sha256Hex(`{${text.slice(prefix[0].length, text.endsWith("\n") ? -1 : undefined)}`) !== prefix[1]) {
    throw new KernelError(`Corrupted module artifact ${path}`);
  }
  if (!isRecord(value) || value.format !== "grace17.module-artifact" || value.version !== 1 ||
      typeof value.module !== "string" || typeof value.file !== "string" || !isDigest(value.sourceDigest) ||
      typeof value.profile !== "string" || !Array.isArray(value.imports) || !Array.isArray(value.closure) ||
      value.closure.some(item => !isRecord(item) || typeof item.module !== "string" || !isDigest(item.digest)) ||
      !isRecord(value.compiled) || !isRecord(value.surface) || !isRecord(value.loaded) || !isDigest(value.digest)) {
    throw new KernelError(`Malformed module artifact ${path}`);
  }
  if (value.digest !== prefix[1]) throw new KernelError(`Corrupted module artifact ${path}`);
  acceptVerifiedSeparateModule(value.compiled);
  return value as unknown as ModuleArtifact;
}

/**
 * The compiled module carries its own content digest, which replay verifies,
 * so the artifact digest covers that digest rather than the events again.
 */
function scanSources(entries: readonly string[], roots: readonly string[]): Map<string, ScannedSource> {
  const resolvedRoots = roots.map(root => resolve(root));
  const sources = new Map<string, ScannedSource>();
  const locate = (name: string): ScannedSource => {
    const known = sources.get(name);
    if (known) return known;
    const relative = `${name.split(".").join("/")}.g17`;
    const file = resolvedRoots.map(root => resolve(root, relative)).find(candidate => existsSync(candidate));
    if (!file) throw new SurfaceError(1, `cannot locate module ${name} as ${relative}`);
    const source = readFileSync(file, "utf8");
    const metadata = scanModule(source, file, path => moduleNameFromPath(path, resolvedRoots));
    if (metadata.name !== name) throw new SurfaceError(1, `${file} declares module ${metadata.name ?? "<none>"}, expected ${name}`);
    const exists = (candidate: string): boolean => sources.has(candidate) ||
      resolvedRoots.some(root => existsSync(resolve(root, `${candidate.split(".").join("/")}.g17`)));
    const imports = metadata.imports.map(raw => resolveImportName(name, raw, exists) ?? raw);
    const item: ScannedSource = { module: name, file, relative, source, digest: sha256Hex(source), imports };
    sources.set(name, item);
    item.imports.forEach(locate);
    return item;
  };
  entries.forEach(locate);
  return sources;
}

function topologicalOrder(sources: ReadonlyMap<string, ScannedSource>): readonly string[] {
  const order: string[] = [];
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const visit = (name: string): void => {
    if (visited.has(name)) return;
    if (visiting.has(name)) throw new SurfaceError(1, `cyclic module import involving ${name}`);
    visiting.add(name);
    sources.get(name)!.imports.forEach(visit);
    visiting.delete(name);
    visited.add(name);
    order.push(name);
  };
  [...sources.keys()].sort().forEach(visit);
  return order;
}

function isRecord(value: unknown): value is Record<string, unknown> {
  return value !== null && typeof value === "object" && !Array.isArray(value);
}

function isDigest(value: unknown): value is string {
  return typeof value === "string" && /^[0-9a-f]{64}$/.test(value);
}
