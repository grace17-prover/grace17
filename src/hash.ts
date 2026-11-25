// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

// Small synchronous SHA-256 used by both Node and browser builds.
// Keeping hashing platform-neutral makes authenticated Grace17 artifacts
// byte-for-byte identical in the CLI, Workbench worker, and external tools.

const constants = new Uint32Array([
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
]);

const initial = new Uint32Array([
  0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a,
  0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19,
]);

const rotateRight = (value: number, bits: number): number => (value >>> bits) | (value << (32 - bits));

// Node's native digest is used when present; the portable implementation
// below produces the same bytes everywhere else. Node 22 exposes built-in
// modules through process.getBuiltinModule without a static import, which
// keeps this file loadable in the browser bundle.
interface NativeHasher { update(data: Uint8Array): NativeHasher; digest(): Uint8Array }
const nativeCreateHash: (() => NativeHasher) | undefined = (() => {
  try {
    const crypto = (globalThis as { process?: { getBuiltinModule?: (name: string) => unknown } })
      .process?.getBuiltinModule?.("node:crypto") as { createHash?: (name: string) => NativeHasher } | undefined;
    if (!crypto?.createHash) return undefined;
    const probe = crypto.createHash("sha256").update(new Uint8Array()).digest();
    return probe.length === 32 ? () => crypto.createHash!("sha256") : undefined;
  } catch { return undefined; }
})();

/** Fold one 64-byte block of `data` at `offset` into `hash`. */
function compress(hash: Uint32Array, words: Uint32Array, data: Uint8Array, offset: number): void {
  for (let index = 0; index < 16; index += 1) {
    const at = offset + index * 4;
    words[index] = ((data[at]! << 24) | (data[at + 1]! << 16) |
      (data[at + 2]! << 8) | data[at + 3]!) >>> 0;
  }
  for (let index = 16; index < 64; index += 1) {
    const x = words[index - 15]!;
    const y = words[index - 2]!;
    const s0 = rotateRight(x, 7) ^ rotateRight(x, 18) ^ (x >>> 3);
    const s1 = rotateRight(y, 17) ^ rotateRight(y, 19) ^ (y >>> 10);
    words[index] = (words[index - 16]! + s0 + words[index - 7]! + s1) >>> 0;
  }

  let [a, b, c, d, e, f, g, h] = hash;
  for (let index = 0; index < 64; index += 1) {
    const sum1 = rotateRight(e!, 6) ^ rotateRight(e!, 11) ^ rotateRight(e!, 25);
    const choose = (e! & f!) ^ (~e! & g!);
    const first = (h! + sum1 + choose + constants[index]! + words[index]!) >>> 0;
    const sum0 = rotateRight(a!, 2) ^ rotateRight(a!, 13) ^ rotateRight(a!, 22);
    const majority = (a! & b!) ^ (a! & c!) ^ (b! & c!);
    const second = (sum0 + majority) >>> 0;
    h = g; g = f; f = e; e = (d! + first) >>> 0;
    d = c; c = b; b = a; a = (first + second) >>> 0;
  }
  hash[0] = (hash[0]! + a!) >>> 0;
  hash[1] = (hash[1]! + b!) >>> 0;
  hash[2] = (hash[2]! + c!) >>> 0;
  hash[3] = (hash[3]! + d!) >>> 0;
  hash[4] = (hash[4]! + e!) >>> 0;
  hash[5] = (hash[5]! + f!) >>> 0;
  hash[6] = (hash[6]! + g!) >>> 0;
  hash[7] = (hash[7]! + h!) >>> 0;
}

function hashBytes(hash: Uint32Array): Uint8Array {
  const output = new Uint8Array(32);
  hash.forEach((word, index) => {
    output[index * 4] = word >>> 24;
    output[index * 4 + 1] = word >>> 16;
    output[index * 4 + 2] = word >>> 8;
    output[index * 4 + 3] = word;
  });
  return output;
}

/** The padding that ends a message of `length` bytes, from its last partial block on. */
function finalBlocks(tail: Uint8Array, length: number): Uint8Array {
  const paddedLength = Math.ceil((tail.length + 9) / 64) * 64;
  const padded = new Uint8Array(paddedLength);
  padded.set(tail);
  padded[tail.length] = 0x80;
  const bitLength = BigInt(length) * 8n;
  for (let index = 0; index < 8; index += 1) {
    padded[paddedLength - 1 - index] = Number((bitLength >> BigInt(index * 8)) & 0xffn);
  }
  return padded;
}

export function sha256Bytes(value: string | Uint8Array): Uint8Array {
  const input = typeof value === "string" ? new TextEncoder().encode(value) : value;
  if (nativeCreateHash) return new Uint8Array(nativeCreateHash().update(input).digest());
  const padded = finalBlocks(input, input.length);
  const hash = new Uint32Array(initial);
  const words = new Uint32Array(64);
  for (let offset = 0; offset < padded.length; offset += 64) compress(hash, words, padded, offset);
  return hashBytes(hash);
}

const hex = (bytes: Uint8Array): string => [...bytes].map(byte => byte.toString(16).padStart(2, "0")).join("");

export function sha256Hex(value: string | Uint8Array): string {
  return hex(sha256Bytes(value));
}

/**
 * SHA-256 of a message given in pieces: the digest of the concatenation,
 * for messages too large to hold as one string.
 */
export class Sha256 {
  readonly #native: NativeHasher | undefined;
  readonly #hash = new Uint32Array(initial);
  readonly #words = new Uint32Array(64);
  readonly #block = new Uint8Array(64);
  #buffered = 0;
  #length = 0;

  /** `portable` uses the implementation here even where Node's digest is present, as in a browser. */
  constructor(options: { readonly portable?: boolean } = {}) {
    this.#native = options.portable ? undefined : nativeCreateHash?.();
  }

  update(data: Uint8Array): this {
    if (this.#native) { this.#native.update(data); return this; }
    this.#length += data.length;
    let offset = 0;
    if (this.#buffered > 0) {
      const take = Math.min(64 - this.#buffered, data.length);
      this.#block.set(data.subarray(0, take), this.#buffered);
      this.#buffered += take;
      offset = take;
      if (this.#buffered < 64) return this;
      compress(this.#hash, this.#words, this.#block, 0);
      this.#buffered = 0;
    }
    for (; offset + 64 <= data.length; offset += 64) compress(this.#hash, this.#words, data, offset);
    this.#block.set(data.subarray(offset), 0);
    this.#buffered = data.length - offset;
    return this;
  }

  digestHex(): string {
    if (this.#native) return hex(new Uint8Array(this.#native.digest()));
    const padded = finalBlocks(this.#block.subarray(0, this.#buffered), this.#length);
    for (let offset = 0; offset < padded.length; offset += 64) compress(this.#hash, this.#words, padded, offset);
    return hex(hashBytes(this.#hash));
  }
}

export function timingSafeBytesEqual(left: Uint8Array, right: Uint8Array): boolean {
  if (left.length !== right.length) return false;
  let difference = 0;
  for (let index = 0; index < left.length; index += 1) difference |= left[index]! ^ right[index]!;
  return difference === 0;
}
