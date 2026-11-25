// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// An inspection answers for one theorem. Its kernel rows each carry their
// whole context, which repeats along a derivation, so the worker sends each
// context formula once, in kernelAssumptions, and a row's context as indices
// into it; the page restores the rows, sharing those strings, with the
// indices as the context's key.

/** The worker's answer to an inspection of `theorem`: that theorem alone, its contexts as indices. */
export function compactInspection(result, theorem) {
  if (!result.ok) return result;
  return { ...result, theorems: result.theorems.filter(item => item.name === theorem).map(item => {
    const table = [];
    const indices = new Map();
    const index = text => {
      let known = indices.get(text);
      if (known === undefined) { known = table.length; table.push(text); indices.set(text, known); }
      return known;
    };
    return { ...item, kernel: item.kernel.map(node => ({ ...node, assumptions: node.assumptions.map(index) })), kernelAssumptions: table };
  }) };
}

/** The kernel rows of an inspected theorem, each context as its formulas and with `contextKey`. */
export function expandInspectedKernel(details) {
  const table = details.kernelAssumptions;
  if (!table) return details.kernel;
  return details.kernel.map(node => ({
    ...node, assumptions: node.assumptions.map(item => table[item]), contextKey: node.assumptions.join(","),
  }));
}
