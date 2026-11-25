// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import { canonical, CanonicalText, canonicalDigest, canonicalEquals } from "../src/ast.ts";
import { Sha256, sha256Hex } from "../src/hash.ts";

const samples: unknown[] = [
  null, 0, -1.5, true, "", "plain", "quote \" and \\ and \n",
  "π ∀x ∃y 😀", "lone \ud800 surrogate", [], {}, [1, [2, [3]]],
  { b: 1, a: [null, "x"], c: { z: undefined, y: 2 } },
  [undefined, 1, undefined],
  { list: [1, undefined], nested: [[undefined]] },
  // Pieces that straddle the 64 KiB flush, with multi-byte characters at the edge.
  { text: "é".repeat(70_000), more: ["😀".repeat(40_000), "a".repeat(65_535)] },
  Array.from({ length: 5_000 }, (_, index) => ({ index, name: `n${index}`, value: index % 3 ? index : null })),
];

test("canonicalDigest is the digest of the canonical text", () => {
  for (const sample of samples) {
    const expected = sha256Hex(canonical(sample));
    assert.equal(canonicalDigest(sample), expected);
    assert.equal(canonicalDigest(sample, { portable: true }), expected);
  }
  assert.equal(canonicalDigest(undefined), sha256Hex(""));
});

test("the incremental SHA-256 agrees with the one-shot digest however the message is split", () => {
  const message = new TextEncoder().encode("Grace17 ".repeat(1_000) + "∀ε>0 ∃δ>0");
  for (const portable of [false, true]) {
    for (const size of [1, 3, 63, 64, 65, 127, 1_000, message.length]) {
      const hasher = new Sha256({ portable });
      for (let offset = 0; offset < message.length; offset += size) hasher.update(message.subarray(offset, offset + size));
      assert.equal(hasher.digestHex(), sha256Hex(message), `portable ${portable}, pieces of ${size}`);
    }
    for (const length of [0, 55, 56, 63, 64, 119, 120]) {
      const bytes = message.subarray(0, length);
      assert.equal(new Sha256({ portable }).update(bytes).digestHex(), sha256Hex(bytes), `portable ${portable}, ${length} bytes`);
    }
  }
});

test("a value whose canonical text is longer than a string can be still has a digest", () => {
  const piece = "x".repeat(1 << 20);
  const value = { pieces: Array.from({ length: 600 }, () => piece) };
  assert.throws(() => canonical(value), RangeError);
  const expected = new Sha256();
  const encoder = new TextEncoder();
  expected.update(encoder.encode(`{"pieces":[`));
  const quoted = encoder.encode(JSON.stringify(piece));
  for (let index = 0; index < 600; index += 1) {
    if (index > 0) expected.update(encoder.encode(","));
    expected.update(quoted);
  }
  expected.update(encoder.encode("]}"));
  assert.equal(canonicalDigest(value), expected.digestHex());
});

test("canonical text read in chunks is the canonical text, and compares as it does", () => {
  const sparse = [1, , 3];
  const extra = [sparse, [undefined, undefined], { f: () => 1, g: undefined }, () => 1, undefined];
  for (const sample of [...samples, ...extra]) {
    const text = new CanonicalText(sample);
    let joined = "";
    for (let chunk = text.next(100); chunk !== undefined; chunk = text.next(100)) joined += chunk;
    assert.equal(joined, canonical(sample) ?? "");
    assert.equal(canonicalDigest(sample), sha256Hex(canonical(sample) ?? ""));
  }
  const all = [...samples, ...extra];
  for (const left of all) for (const right of all) assert.equal(canonicalEquals(left, right), canonical(left) === canonical(right));
  assert.equal(canonicalEquals({ a: [1, 2] }, { a: [1, 2], b: undefined }), true);
  assert.equal(canonicalEquals({ a: "x".repeat(200_000) }, { a: `${"x".repeat(199_999)}y` }), false);
  const piece = "x".repeat(1 << 20);
  const huge = () => ({ pieces: Array.from({ length: 600 }, () => piece) });
  assert.equal(canonicalEquals(huge(), huge()), true);
  assert.equal(canonicalEquals(huge(), { pieces: [...huge().pieces.slice(1), `${piece}z`] }), false);
});
