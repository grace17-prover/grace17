// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { canonical } from "./ast.ts";
import type { Kernel } from "./kernel.ts";

export interface PortableKernelEnvironment {
  readonly format: "grace17.environment";
  readonly version: 1;
  readonly digest: string;
  readonly kernel: object;
}

/** Export the exact data and digest against which a G17M checker replays. */
export function exportKernelEnvironment(kernel: Kernel): PortableKernelEnvironment {
  const snapshot = kernel.environmentSnapshot();
  const result: PortableKernelEnvironment = {
    format: "grace17.environment",
    version: 1,
    digest: kernel.digest(),
    kernel: snapshot,
  };
  // Force traversal now so an unserializable future field fails at export time.
  canonical(result);
  return Object.freeze(result);
}
