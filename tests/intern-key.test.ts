// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { pairInternKey } from "../src/intern-key.ts";

test("binary interning keys distinguish ordered pairs including exact-integer boundaries", () => {
  const bound = 67_108_863;
  const ids = [0, 1, 2, 127, 32768, 1_000_000, bound - 2, bound - 1, bound,
    bound + 1, Number.MAX_SAFE_INTEGER - 1, Number.MAX_SAFE_INTEGER];
  const seen = new Set<string | number>();
  for (const left of ids) for (const right of ids) {
    const key = pairInternKey(left, right);
    assert.ok(!seen.has(key), `collision for ${left},${right}`);
    seen.add(key);
    if (left + right <= bound) {
      assert.equal(typeof key, "number");
      assert.ok(Number.isSafeInteger(key));
      const total = BigInt(left) + BigInt(right);
      assert.equal(BigInt(key), total * (total + 1n) / 2n + BigInt(right));
    } else assert.equal(key, `${left},${right}`);
  }
});

test("binary interning keys remain injective across the numeric/string transition", () => {
  const bound = 67_108_863;
  const keys = new Set<string | number>();
  for (let delta = -2; delta <= 2; delta++) for (let left = 0; left < 1000; left++) {
    const key = pairInternKey(left, bound + delta - left);
    assert.ok(!keys.has(key));
    keys.add(key);
  }
  assert.equal(keys.size, 5000);
});
