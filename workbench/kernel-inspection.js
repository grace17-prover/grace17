// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// An inspection answers for one theorem, its kernel rows sent as the machine
// interface sends them: each context formula once, in kernelAssumptions, and a
// row's context as indices into it (src/kernel-contexts.ts). The page restores
// the rows, sharing those strings, with the indices as the context's key.

import { compactKernelContexts, expandKernelContexts } from "./generated/src/kernel-contexts.js";

/** The worker's answer to an inspection of `theorem`: that theorem alone, its contexts as indices. */
export function compactInspection(result, theorem) {
  if (!result.ok) return result;
  return { ...result, theorems: result.theorems.filter(item => item.name === theorem).map(item => {
    const compact = compactKernelContexts(item.kernel);
    return { ...item, kernel: compact.rows, kernelAssumptions: compact.assumptions };
  }) };
}

/** The kernel rows of an inspected theorem, each context as its formulas and with `contextKey`. */
export function expandInspectedKernel(details) {
  return details.kernelAssumptions ? expandKernelContexts(details.kernel, details.kernelAssumptions) : details.kernel;
}
