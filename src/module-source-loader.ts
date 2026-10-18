// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { elaborateModule, moduleReport, SurfaceError, type ElaboratedModule } from "./surface.ts";
import { moduleNameFromPath, resolveImportName } from "./module-names.ts";
import type { Kernel } from "./kernel.ts";

export interface LoadedModule extends ElaboratedModule {
  readonly file: string;
  readonly module?: string;
}

interface ModuleSource {
  readonly file: string;
  readonly source: string;
  readonly name?: string;
  readonly imports: readonly string[];
}

export interface ModuleSourceFile {
  readonly file: string;
  readonly source: string;
}

export type ModuleSourceResolver = (name: string) => ModuleSourceFile | undefined;
/** The qualified name a file under a module root denotes, for bare `module Name` declarations. */
export type ModuleNameDeriver = (file: string) => string | undefined;

/**
 * An installed library loader may bring an imported library module and its
 * closure into the kernel by other means than elaborating their sources,
 * such as replaying a module store; it returns whether it did. The source
 * loader then skips those modules, as it skips any module already loaded.
 */
export type LibraryModuleLoader = (kernel: Kernel, name: string, entries: ReadonlySet<string>) => boolean;
let libraryModuleLoader: LibraryModuleLoader | undefined;
export function setLibraryModuleLoader(loader?: LibraryModuleLoader): void {
  libraryModuleLoader = loader;
}

/**
 * Resolve and elaborate an in-memory module graph. The optional resolver is
 * the only platform hook: Node supplies filesystem reads, while the browser
 * supplies versioned standard-library source strings.
 */
export function loadModuleSourceGraphResolved(
  kernel: Kernel,
  entries: readonly ModuleSourceFile[],
  entryFiles?: readonly string[],
  resolveSource?: ModuleSourceResolver,
  entryModules: readonly string[] = [],
  deriveName: ModuleNameDeriver = file => moduleNameFromPath(file, ["lib"]),
): readonly LoadedModule[] {
  const sources = new Map<string, ModuleSource>();

  const add = (file: string, source: string): ModuleSource => {
    const metadata = scanModule(source, file, deriveName);
    if (metadata.declared && !metadata.declared.includes(".") && metadata.derived &&
        metadata.derived.split(".").at(-1) !== metadata.declared) {
      throw new SurfaceError(1, `${file}: module ${metadata.declared} does not match its file, which denotes ${metadata.derived}`);
    }
    const item = { file, source, name: metadata.name, imports: metadata.imports };
    if (item.name) {
      const previous = sources.get(item.name);
      if (previous && previous.file !== item.file) throw new SurfaceError(1, `duplicate module ${item.name}`);
      sources.set(item.name, item);
    }
    return item;
  };
  const entrySources = entries.map(item => add(item.file, item.source));
  const selectedFiles = entryFiles ? new Set(entryFiles) : undefined;
  const selectedEntries = selectedFiles ? entrySources.filter(item => selectedFiles.has(item.file)) : entrySources;
  if (selectedFiles && selectedEntries.length !== selectedFiles.size) {
    const missing = [...selectedFiles].filter(file => !entrySources.some(item => item.file === file));
    throw new SurfaceError(1, `unknown workspace entry ${missing.join(", ")}`);
  }
  const alreadyLoaded = new Set(moduleReport(kernel).map(item => item.name));
  // An import is read relative to the importing module, innermost first.
  const exists = (name: string): boolean => sources.has(name) || alreadyLoaded.has(name) || resolveSource?.(name) !== undefined;
  const resolveImport = (current: string | undefined, raw: string): string => resolveImportName(current, raw, exists) ?? raw;
  const locate = (name: string): ModuleSource => {
    const known = sources.get(name);
    if (known) return known;
    const resolved = resolveSource?.(name);
    if (!resolved) throw new SurfaceError(1, `cannot locate imported module ${name} as ${name.split(".").join("/")}.g17`);
    const loaded = add(resolved.file, resolved.source);
    if (loaded.name !== name) {
      throw new SurfaceError(1, `${resolved.file} declares module ${loaded.name ?? "<none>"}, expected ${name}`);
    }
    return loaded;
  };

  const ordered: ModuleSource[] = [];
  const visiting = new Set<string>();
  const visited = new Set<string>();
  const importModule = (name: string): void => {
    if (alreadyLoaded.has(name) || sources.has(name)) { if (!alreadyLoaded.has(name)) visit(locate(name)); return; }
    if (libraryModuleLoader?.(kernel, name, new Set(sources.keys()))) {
      for (const record of moduleReport(kernel)) alreadyLoaded.add(record.name);
      if (alreadyLoaded.has(name)) return;
    }
    visit(locate(name));
  };
  const visit = (item: ModuleSource): void => {
    if (!item.name || visited.has(item.name) || alreadyLoaded.has(item.name)) return;
    if (visiting.has(item.name)) throw new SurfaceError(1, `cyclic module import involving ${item.name}`);
    visiting.add(item.name);
    item.imports.forEach(raw => importModule(resolveImport(item.name, raw)));
    visiting.delete(item.name);
    visited.add(item.name);
    ordered.push(item);
  };
  selectedEntries.forEach(visit);
  entryModules.forEach(importModule);

  const results: LoadedModule[] = [];
  const elaborate = (item: ModuleSource): ElaboratedModule => {
    try { return elaborateModule(kernel, item.source, item.name ? { moduleName: item.name } : {}); }
    catch (error) {
      if (error instanceof SurfaceError) error.file ??= item.file;
      throw error;
    }
  };
  for (const item of selectedEntries.filter(item => !item.name)) results.push({ file: item.file, ...elaborate(item) });
  for (const item of ordered) results.push({ file: item.file, module: item.name, ...elaborate(item) });
  return results;
}

/**
 * The module a source declares and the imports it writes. A bare `module Name`
 * is qualified by the file's path under a module root when a path is given;
 * the imports are returned as written and are resolved relative to the module.
 */
export function scanModule(source: string, file?: string, deriveName: ModuleNameDeriver = path => moduleNameFromPath(path, ["lib"])): {
  readonly name?: string; readonly imports: readonly string[]; readonly declared?: string; readonly derived?: string;
} {
  const lines = source.split(/\r?\n/).map(raw => raw.replace(/--.*$/, "").trim()).filter(Boolean);
  const declaration = lines.map(line => /^module\s+(\S+)$/.exec(line)).find(Boolean);
  const imports = lines.map(line => /^import\s+(\S+)$/.exec(line)).filter((match): match is RegExpExecArray => Boolean(match))
    .map(match => match[1]!);
  const declared = declaration?.[1];
  let name = declared;
  let derived: string | undefined;
  if (name && !name.includes(".") && file) {
    derived = deriveName(file);
    if (derived && derived.split(".").at(-1) === name) name = derived;
  }
  return { name, imports, declared, derived };
}
