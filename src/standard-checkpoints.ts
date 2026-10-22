// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import type { SeparateCompiledKernelModule } from "./compiled-module.ts";
import type { SurfaceEnvironmentIndex } from "./surface.ts";

export interface StandardDependencyCheckpoint {
  readonly rootModule: string;
  /** The foundation profile the checkpoint was built under; `ZFG` when absent. */
  readonly profile?: "ZF" | "ZFC" | "ZFG";
  readonly sources: readonly (readonly [module: string, digest: string])[];
  /** Where a browser build keeps the payload below, relative to its generated directory, until it is installed. */
  readonly file?: string;
  /** A kept checkpoint compiled over a bundled one: that root replays first, then this payload on top. */
  readonly prefix?: string;
  readonly compiled?: SeparateCompiledKernelModule;
  readonly surface?: SurfaceEnvironmentIndex;
  readonly loaded?: readonly {
    readonly module: string;
    readonly definitions: readonly string[];
    readonly theorems: readonly string[];
  }[];
}

/**
 * Native development elaborates source; browser builds replace this with an
 * index of authenticated caches whose payloads are fetched when a workspace
 * first needs them.
 */
export const standardDependencyCheckpoints: Map<string, StandardDependencyCheckpoint> = new Map();

/** Install or complete a checkpoint: a fetched bundled payload, or one a browser built and kept. */
export function installStandardCheckpoint(entry: StandardDependencyCheckpoint): void {
  const existing = standardDependencyCheckpoints.get(entry.rootModule);
  standardDependencyCheckpoints.set(entry.rootModule, existing ? { ...existing, ...entry } : entry);
}
