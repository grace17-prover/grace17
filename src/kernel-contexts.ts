// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Each row of a kernel derivation carries its whole context, and a context
// repeats along a derivation: written out, a large proof's rows run to
// hundreds of megabytes. Sent as a table of context formulas, each written
// once, and each row's context as indices into it, they are a fraction of
// that. Both the machine interface and the Workbench worker send rows so.

/** Rows whose contexts are indices into `assumptions`, each formula there once. */
export interface CompactKernelRows<Row> {
  readonly rows: (Omit<Row, "assumptions"> & { readonly assumptions: readonly number[] })[];
  readonly assumptions: readonly string[];
}

export function compactKernelContexts<Row extends { readonly assumptions: readonly string[] }>(rows: readonly Row[]): CompactKernelRows<Row> {
  const assumptions: string[] = [];
  const indices = new Map<string, number>();
  const index = (text: string): number => {
    let known = indices.get(text);
    if (known === undefined) { known = assumptions.length; assumptions.push(text); indices.set(text, known); }
    return known;
  };
  return { rows: rows.map(row => ({ ...row, assumptions: row.assumptions.map(index) })), assumptions };
}

/**
 * The rows with their contexts as formulas again, sharing the table's
 * strings, and `contextKey`, equal for two rows exactly when their contexts are.
 */
export function expandKernelContexts<Row extends { readonly assumptions: readonly number[] }>(rows: readonly Row[], assumptions: readonly string[]) {
  return rows.map(row => ({ ...row, assumptions: row.assumptions.map(item => assumptions[item]!), contextKey: row.assumptions.join(",") }));
}
