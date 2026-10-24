// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { existsSync, readdirSync, readFileSync, statSync } from "node:fs";
import { join, resolve } from "node:path";
import {
  loadModuleSourceGraphResolved, type LoadedModule, type ModuleNameDeriver, type ModuleSourceFile,
} from "./module-source-loader.ts";
import type { Kernel } from "./kernel.ts";
import { moduleNameFromPath } from "./module-names.ts";
import { setLibraryDeclarationLocator } from "./surface.ts";

export type { LoadedModule, ModuleSourceFile } from "./module-source-loader.ts";

/** Resolve imports from module roots and elaborate dependencies first. */
export function loadModuleGraph(
  kernel: Kernel,
  entries: readonly string[],
  roots: readonly string[] = ["."],
): readonly LoadedModule[] {
  return loadModuleSourceGraph(kernel, entries.map(file => {
    const absolute = resolve(file);
    return { file: absolute, source: readFileSync(absolute, "utf8") };
  }), roots);
}

/**
 * Load an import graph whose entry modules may live in memory. Workspace
 * sources take precedence over files found in module roots, so an editor can
 * check several mutually importing buffers and can open a bundled core module
 * without admitting an older copy first.
 */
export function loadModuleSourceGraph(
  kernel: Kernel,
  entries: readonly ModuleSourceFile[],
  roots: readonly string[] = ["."],
  entryFiles?: readonly string[],
  entryModules: readonly string[] = [],
  deriveName: ModuleNameDeriver = file => moduleNameFromRoots(file, roots),
): readonly LoadedModule[] {
  const resolvedRoots = roots.map(root => resolve(root));
  setLibraryDeclarationLocator(libraryDeclarationLocator(resolvedRoots));
  return loadModuleSourceGraphResolved(kernel, entries, entryFiles, name => {
    const relative = `${name.split(".").join("/")}.g17`;
    const file = resolvedRoots.map(root => resolve(root, relative)).find(candidate => {
      noteDependencyRead(candidate);
      return existsSync(candidate);
    });
    return file ? { file, source: readFileSync(file, "utf8") } : undefined;
  }, entryModules, deriveName);
}

// The dependency files a check read from disk, each with the size and
// modification time seen: a caller that keeps an answer computed over them
// can tell when a later request must not reuse it, because a dependency was
// rewritten, created, or removed meanwhile. A file that was looked for and
// not found is recorded too, so that its creation is also a change.
export interface DependencyStamp {
  readonly file: string;
  readonly size: number;
  readonly mtimeMs: number;
}
const MISSING_STAMP = -1;
// Recordings nest: a load started while another records is noted by both.
const dependencyReads: Map<string, DependencyStamp>[] = [];

/** Record the dependency files read from now until the matching `endDependencyReads`. */
export function beginDependencyReads(): void {
  dependencyReads.push(new Map());
}

/** The dependency files read since the matching `beginDependencyReads`, and stop that recording. */
export function endDependencyReads(): readonly DependencyStamp[] {
  return [...(dependencyReads.pop()?.values() ?? [])];
}

function stampOf(file: string): DependencyStamp {
  try {
    const stat = statSync(file);
    return { file, size: stat.size, mtimeMs: stat.mtimeMs };
  } catch {
    return { file, size: MISSING_STAMP, mtimeMs: MISSING_STAMP };
  }
}

/** Note that a loader read, or looked for, a dependency file on disk. */
export function noteDependencyRead(file: string): void {
  if (dependencyReads.length === 0) return;
  const stamp = stampOf(file);
  for (const recording of dependencyReads) if (!recording.has(file)) recording.set(file, stamp);
}

/** Whether every recorded dependency file is as it was when it was read: same size and modification time, or still missing. */
export function dependencyStampsCurrent(stamps: readonly DependencyStamp[]): boolean {
  return stamps.every(stamp => {
    const now = stampOf(stamp.file);
    return now.size === stamp.size && now.mtimeMs === stamp.mtimeMs;
  });
}

/** The declarations of the modules under the roots, read from their sources
 * without elaboration and indexed by short name, so that a proof naming a
 * declaration outside its import closure is told which module declares it.
 * Built on first use per root list and kept for the process. */
const declarationIndexes = new Map<string, Map<string, { readonly module: string; readonly name: string }[]>>();
const DECLARATION_HEAD = /^(?:theorem|lemma|instance|def|predicate|class|defgraph|defunique|defchoose|structure|datatype|axiom)\s+([^\s(:]+)/u;
export function libraryDeclarationLocator(
  roots: readonly string[],
): (short: string) => readonly { readonly module: string; readonly name: string }[] {
  const key = roots.join("\n");
  return short => {
    let index = declarationIndexes.get(key);
    if (!index) {
      index = new Map();
      const files: string[] = [];
      const walk = (directory: string): void => {
        let names: string[];
        try { names = readdirSync(directory); } catch { return; }
        for (const name of names) {
          const path = join(directory, name);
          let directoryEntry = false;
          try { directoryEntry = statSync(path).isDirectory(); } catch { continue; }
          if (directoryEntry) walk(path);
          else if (name.endsWith(".g17")) files.push(path);
        }
      };
      roots.forEach(walk);
      for (const file of files) {
        let source: string;
        try { source = readFileSync(file, "utf8"); } catch { continue; }
        const module = /^module\s+(\S+)/mu.exec(source)?.[1];
        if (!module) continue;
        for (const line of source.split("\n")) {
          const declared = DECLARATION_HEAD.exec(line)?.[1];
          if (!declared) continue;
          const record = { module, name: declared };
          for (const entry of new Set([declared, declared.split(".").at(-1)!])) {
            const bucket = index.get(entry) ?? [];
            if (!bucket.some(item => item.module === module && item.name === declared)) bucket.push(record);
            index.set(entry, bucket);
          }
        }
      }
      declarationIndexes.set(key, index);
    }
    return index.get(short) ?? [];
  };
}

/** The module a file under one of the roots denotes, by absolute or written path. */
export function moduleNameFromRoots(file: string, roots: readonly string[]): string | undefined {
  const resolvedRoots = roots.map(root => resolve(root));
  return moduleNameFromPath(resolve(file), resolvedRoots) ?? moduleNameFromPath(file, roots);
}
