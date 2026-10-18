// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { canonical } from "./ast.ts";
import { Kernel, KernelError, type SetTheoryProfile } from "./kernel.ts";
import { createSetTheoryFoundationKernel } from "./zfg.ts";

/**
 * A tiny, non-snapshot description of a checker-constructed foundation.
 *
 * The profile selects the normative bootstrap algorithm implemented by the
 * checker.  The environment digest pins its exact result, so a future change
 * to an axiom, signature, or checked prelude cannot retain the same identity.
 */
export interface FoundationBootstrap {
  readonly format: "grace17.foundation";
  readonly version: 1;
  readonly profile: Exclude<SetTheoryProfile, "none">;
  readonly environment: string;
}

const profiles = new Set<Exclude<SetTheoryProfile, "none">>(["ZF", "ZFC", "ZFG"]);
const digestPattern = /^[0-9a-f]{64}$/;

export function constructFoundation(
  profile: Exclude<SetTheoryProfile, "none"> = "ZFG",
): Kernel {
  if (!profiles.has(profile)) throw new KernelError(`Unsupported foundation profile: ${profile}`);
  return createSetTheoryFoundationKernel({ profile });
}

export function describeFoundation(
  profile: Exclude<SetTheoryProfile, "none"> = "ZFG",
): FoundationBootstrap {
  const kernel = constructFoundation(profile);
  return Object.freeze({
    format: "grace17.foundation",
    version: 1,
    profile,
    environment: kernel.digest(),
  });
}

/** Construct and authenticate a foundation description without loading maps. */
export function replayFoundation(description: FoundationBootstrap): Kernel {
  validateFoundationBootstrap(description);
  const kernel = constructFoundation(description.profile);
  if (kernel.digest() !== description.environment) {
    throw new KernelError("Foundation bootstrap produced the wrong environment");
  }
  return kernel;
}

export function encodeFoundationBootstrap(description: FoundationBootstrap): Uint8Array {
  validateFoundationBootstrap(description);
  return new TextEncoder().encode(canonical(description));
}

export function decodeFoundationBootstrap(bytes: Uint8Array): FoundationBootstrap {
  let value: unknown;
  try { value = JSON.parse(new TextDecoder("utf-8", { fatal: true }).decode(bytes)); }
  catch { throw new KernelError("Malformed foundation bootstrap encoding"); }
  validateFoundationBootstrap(value);
  return value;
}

function validateFoundationBootstrap(value: unknown): asserts value is FoundationBootstrap {
  if (typeof value !== "object" || value === null) throw new KernelError("Malformed foundation bootstrap");
  const item = value as Record<string, unknown>;
  if (item.format !== "grace17.foundation" || item.version !== 1 ||
      typeof item.profile !== "string" || !profiles.has(item.profile as Exclude<SetTheoryProfile, "none">) ||
      typeof item.environment !== "string" || !digestPattern.test(item.environment) ||
      Object.keys(item).length !== 4) {
    throw new KernelError("Malformed foundation bootstrap");
  }
}
