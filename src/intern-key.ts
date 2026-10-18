// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Internal interning keys, never a proof or a serialized AST representation.
export type InternKey = string | number;

/** Injective encoding of two nonnegative integer IDs, with exact arithmetic. */
export function pairInternKey(left: number, right: number): InternKey {
  const sum = left + right;
  // At this bound sum*(sum+1) < 2^52. The product, division by two,
  // and final addition are exact integers in JavaScript's number format.
  // Above it, preserve the original delimiter-separated encoding.
  return sum <= 67_108_863 ? sum * (sum + 1) / 2 + right : `${left},${right}`;
}
