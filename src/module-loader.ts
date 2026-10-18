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
    const file = resolvedRoots.map(root => resolve(root, relative)).find(candidate => existsSync(candidate));
    return file ? { file, source: readFileSync(file, "utf8") } : undefined;
  }, entryModules, deriveName);
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
