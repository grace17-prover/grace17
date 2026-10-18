// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import type { SeparateCompiledKernelModule } from "./compiled-module.ts";
import type { SurfaceEnvironmentIndex } from "./surface.ts";

export interface StandardDependencyCheckpoint {
  readonly rootModule: string;
  readonly sources: readonly (readonly [module: string, digest: string])[];
  readonly compiled: SeparateCompiledKernelModule;
  readonly surface: SurfaceEnvironmentIndex;
  readonly loaded: readonly {
    readonly module: string;
    readonly definitions: readonly string[];
    readonly theorems: readonly string[];
  }[];
}

/** Native development elaborates source; browser builds replace this with authenticated caches. */
export const standardDependencyCheckpoints: ReadonlyMap<string, StandardDependencyCheckpoint> = new Map();
