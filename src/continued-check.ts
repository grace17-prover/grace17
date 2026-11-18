// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// A check that goes on past a failing module: `g17 check --continue` and
// the machine interface's `check` with `continue: true` both run it, so a
// served check reports every failure of a workspace as the command line
// does.

import { existsSync, readFileSync } from "node:fs";
import { resolve } from "node:path";
import type { Kernel } from "./kernel.ts";
import { KernelError } from "./kernel.ts";
import { loadModuleSourceGraph, moduleNameFromRoots } from "./module-loader.ts";
import { resolveImportName } from "./module-names.ts";
import { scanModule, type LoadedModule } from "./module-source-loader.ts";
import {
  forkSurfaceEnvironment, moduleReport, SurfaceError,
} from "./surface.ts";
import { rememberFailureDisplay } from "./workbench.ts";

export interface ContinuedCheckFailure {
  readonly module: string;
  readonly file: string;
  readonly source: string;
  readonly error: unknown;
}

export interface ContinuedCheck {
  readonly kernel: Kernel;
  readonly loaded: readonly LoadedModule[];
  /**
   * Every failure, a module's failed theorems each once; a module with
   * several appears several times.
   */
  readonly failures: readonly ContinuedCheckFailure[];
  readonly skipped: readonly {
    readonly module: string; readonly file: string; readonly because: string;
  }[];
  /** The theorems a module could not reach after a failure outside a proof. */
  readonly skippedAfterFailure: readonly {
    readonly module: string; readonly file: string; readonly line: number;
    readonly theorems: readonly string[];
  }[];
}

/**
 * An entry of a continued check: a file on disk, or a file with the source
 * to check in place of what is on disk.
 */
export interface ContinuedCheckEntry {
  readonly file: string;
  readonly source?: string;
}

/** The theorems, lemmas, and instances declared after a line of a source. */
function theoremsAfterLine(source: string, line: number): string[] {
  return source.split(/\r?\n/).flatMap((text, index) => {
    const header = index + 1 > line
      ? /^(?:theorem|lemma|instance)\s+(\S+)/.exec(text) : null;
    return header ? [header[1]!] : [];
  });
}

/** The kind and message of a failure, as the command line prints it. */
export function failureText(error: unknown): string {
  const kind = error instanceof SurfaceError ? "surface"
    : error instanceof KernelError ? "kernel" : "io";
  const message = error instanceof Error ? error.message : String(error);
  return `${kind} error: ${message}`;
}

interface Source {
  readonly module: string;
  readonly file: string;
  readonly source: string;
  readonly imports: readonly string[];
}

/**
 * Check every module of the entries' import graph, going on past a failure:
 * each module is elaborated in a fork of the kernel, so a failed module
 * leaves nothing behind, and the modules that import a failed or skipped
 * module are skipped and reported with the import that blocked them.
 * Within a module, a failed theorem is reported and the next declaration
 * is checked, so one run reports every failing proof of the module; a
 * failure outside a proof, in a definition or a notation, stops the module
 * there, and the theorems after it are reported as skipped after it. A
 * module the initial kernel already holds is not elaborated again, so a
 * kernel seeded with the checked dependencies starts at the entries.
 */
export function checkContinuing(
  initial: Kernel, entries: readonly ContinuedCheckEntry[],
  roots: readonly string[], log?: (line: string) => void,
): ContinuedCheck {
  const resolvedRoots = roots.map(root => resolve(root));
  const derive = (file: string): string | undefined =>
    moduleNameFromRoots(file, resolvedRoots);
  const sources = new Map<string, Source>();
  const libraryFile = (name: string): string | undefined => {
    const relative = `${name.split(".").join("/")}.g17`;
    return resolvedRoots.map(root => resolve(root, relative))
      .find(candidate => existsSync(candidate));
  };
  const alreadyLoaded = new Set(moduleReport(initial).map(item => item.name));
  const exists = (name: string): boolean => sources.has(name)
    || alreadyLoaded.has(name) || libraryFile(name) !== undefined;
  const add = (file: string, given?: string): Source => {
    const source = given ?? readFileSync(file, "utf8");
    const metadata = scanModule(source, file, derive);
    const module = metadata.name ?? file;
    const known = sources.get(module);
    if (known) return known;
    const imports = metadata.imports.map(raw =>
      resolveImportName(metadata.name, raw, exists) ?? raw);
    const item = { module, file, source, imports };
    sources.set(module, item);
    return item;
  };
  // Dependencies before dependents, each module once.
  const ordered: Source[] = [];
  const visited = new Set<string>();
  const visiting = new Set<string>();
  const visit = (item: Source): void => {
    if (visited.has(item.module)) return;
    if (visiting.has(item.module)) {
      throw new SurfaceError(1,
        `cyclic module import involving ${item.module}`);
    }
    visiting.add(item.module);
    for (const name of item.imports) {
      if (alreadyLoaded.has(name)) continue;
      const file = sources.get(name)?.file ?? libraryFile(name);
      if (!file) {
        const path = `${name.split(".").join("/")}.g17`;
        throw new SurfaceError(1,
          `${item.file}: cannot locate imported module ${name} as ${path}`);
      }
      visit(add(file));
    }
    visiting.delete(item.module);
    visited.add(item.module);
    ordered.push(item);
  };
  // The entries are known by name before any import is resolved, so an
  // entry's given source stands in for the file of the same module on disk.
  entries.map(entry => add(entry.file, entry.source)).forEach(visit);

  let kernel = initial;
  const loaded: LoadedModule[] = [];
  const failures: ContinuedCheckFailure[] = [];
  const skipped: { module: string; file: string; because: string }[] = [];
  const skippedAfterFailure: {
    module: string; file: string; line: number; theorems: string[];
  }[] = [];
  const blocked = new Set<string>();
  for (const item of ordered) {
    const blocking = item.imports.find(name => blocked.has(name));
    if (blocking) {
      blocked.add(item.module);
      skipped.push({ module: item.module, file: item.file, because: blocking });
      log?.(`skipped ${item.file}: imports ${blocking}`);
      continue;
    }
    const attempt = kernel.fork();
    forkSurfaceEnvironment(kernel, attempt);
    const fail = (error: SurfaceError | KernelError): void => {
      rememberFailureDisplay(error, attempt);
      blocked.add(item.module);
      const { module, file, source } = item;
      failures.push({ module, file, source, error });
      log?.(`failed ${item.file}: ${failureText(error)}`);
    };
    try {
      const entry = { file: item.file, source: item.source };
      const modules = loadModuleSourceGraph(attempt, [entry], roots, undefined,
        [], derive, { onTheoremFailure: failure => fail(failure.error) });
      // A module with a failed theorem is a failed module: its checked
      // theorems are reported, nothing of it is kept, and its dependents
      // are skipped.
      if (blocked.has(item.module)) {
        loaded.push(...modules.filter(module => module.module !== item.module));
      } else {
        loaded.push(...modules);
        kernel = attempt;
      }
    } catch (error) {
      if (!(error instanceof SurfaceError) && !(error instanceof KernelError)) {
        throw error;
      }
      fail(error);
      const line = error instanceof SurfaceError ? error.line : undefined;
      const theorems = line === undefined ? []
        : theoremsAfterLine(item.source, line);
      if (theorems.length) {
        const { module, file } = item;
        skippedAfterFailure.push({ module, file, line: line!, theorems });
        const noun = theorems.length === 1 ? "theorem" : "theorems";
        const count = `${theorems.length} ${noun}`;
        log?.(`skipped after failure ${file}: ${count} after line ${line}`);
      }
    }
  }
  return { kernel, loaded, failures, skipped, skippedAfterFailure };
}
