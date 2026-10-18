// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { sha256Hex } from "./hash.ts";

/** A hereditary Cantor-normal-form notation for an ordinal below epsilon_0. */
export interface E0Ordinal {
  readonly terms: readonly CantorTerm[];
  readonly finite: bigint;
}

export interface CantorTerm {
  readonly exponent: E0Ordinal;
  readonly coefficient: bigint;
}

export interface OrdinalComparisonCertificate {
  readonly left: E0Ordinal;
  readonly right: E0Ordinal;
  readonly result: -1;
  readonly trace: readonly string[];
  readonly digest: string;
}

export const ordinalZero = (): E0Ordinal => Object.freeze({ terms: Object.freeze([]), finite: 0n });

export function ordinalNat(value: bigint | number): E0Ordinal {
  const finite = BigInt(value);
  if (finite < 0n) throw new RangeError("An ordinal natural must be nonnegative");
  return Object.freeze({ terms: Object.freeze([]), finite });
}

/** Construct w^exponent * coefficient + rest, checking canonical form. */
export function cantor(
  exponent: E0Ordinal,
  coefficient: bigint | number,
  rest: E0Ordinal = ordinalZero(),
): E0Ordinal {
  assertE0Ordinal(exponent);
  assertE0Ordinal(rest);
  const coeff = BigInt(coefficient);
  if (isZero(exponent)) throw new RangeError("Use the finite tail for exponent zero");
  if (coeff <= 0n) throw new RangeError("A Cantor coefficient must be positive");
  if (rest.terms.length > 0 && compareE0(exponent, rest.terms[0]!.exponent) <= 0) {
    throw new RangeError("Cantor exponents must be strictly decreasing");
  }
  return freezeOrdinal({
    terms: [{ exponent, coefficient: coeff }, ...rest.terms],
    finite: rest.finite,
  });
}

export function omegaPow(exponent: E0Ordinal): E0Ordinal {
  return cantor(exponent, 1n);
}

export const omega = (): E0Ordinal => omegaPow(ordinalNat(1));

export function isZero(value: E0Ordinal): boolean {
  return value.terms.length === 0 && value.finite === 0n;
}

export function assertE0Ordinal(value: E0Ordinal): void {
  validateE0Ordinal(value, new WeakSet<object>(), new WeakSet<object>());
}

function validateE0Ordinal(value: E0Ordinal, visiting: WeakSet<object>, checked: WeakSet<object>): void {
  if (typeof value !== "object" || value === null || !Array.isArray(value.terms) || typeof value.finite !== "bigint") {
    throw new TypeError("Malformed epsilon_0 ordinal notation");
  }
  if (checked.has(value)) return;
  if (visiting.has(value)) throw new TypeError("Cyclic epsilon_0 ordinal notation");
  visiting.add(value);
  if (value.finite < 0n) throw new RangeError("Negative finite ordinal tail");
  let previous: E0Ordinal | undefined;
  for (const term of value.terms) {
    if (typeof term.coefficient !== "bigint" || term.coefficient <= 0n) {
      throw new RangeError("Cantor coefficients must be positive integers");
    }
    validateE0Ordinal(term.exponent, visiting, checked);
    if (isZero(term.exponent)) throw new RangeError("Exponent zero belongs in the finite tail");
    if (previous && compareE0(previous, term.exponent) <= 0) {
      throw new RangeError("Cantor exponents must be strictly decreasing");
    }
    previous = term.exponent;
  }
  visiting.delete(value);
  checked.add(value);
}

export function compareE0(left: E0Ordinal, right: E0Ordinal, trace?: string[]): -1 | 0 | 1 {
  assertE0Ordinal(left);
  assertE0Ordinal(right);
  return compareE0Unchecked(left, right, trace);
}

function compareE0Unchecked(left: E0Ordinal, right: E0Ordinal, trace?: string[]): -1 | 0 | 1 {
  const length = Math.min(left.terms.length, right.terms.length);
  for (let index = 0; index < length; index += 1) {
    const l = left.terms[index]!;
    const r = right.terms[index]!;
    const exponentOrder = compareE0Unchecked(l.exponent, r.exponent, trace);
    if (exponentOrder !== 0) {
      trace?.push(`term ${index}: exponent ${exponentOrder < 0 ? "<" : ">"}`);
      return exponentOrder;
    }
    if (l.coefficient !== r.coefficient) {
      const result = l.coefficient < r.coefficient ? -1 : 1;
      trace?.push(`term ${index}: coefficient ${result < 0 ? "<" : ">"}`);
      return result;
    }
  }
  if (left.terms.length !== right.terms.length) {
    const result = left.terms.length < right.terms.length ? -1 : 1;
    trace?.push(`term ${length}: ${result < 0 ? "left exhausted" : "right exhausted"}`);
    return result;
  }
  const result = left.finite === right.finite ? 0 : left.finite < right.finite ? -1 : 1;
  trace?.push(`finite tail: ${result === 0 ? "=" : result < 0 ? "<" : ">"}`);
  return result;
}

export function certifyE0Less(left: E0Ordinal, right: E0Ordinal): OrdinalComparisonCertificate {
  const trace: string[] = [];
  const result = compareE0(left, right, trace);
  if (result !== -1) throw new RangeError("The left ordinal is not strictly smaller");
  const payload = `${serializeE0(left)}<${serializeE0(right)}|${trace.join("|")}`;
  return Object.freeze({
    left: freezeOrdinal(left),
    right: freezeOrdinal(right),
    result,
    trace: Object.freeze([...trace]),
    digest: sha256Hex(payload),
  });
}

/** Independently replay an executable comparison certificate. */
export function checkE0LessCertificate(certificate: OrdinalComparisonCertificate): boolean {
  try {
    const trace: string[] = [];
    if (compareE0(certificate.left, certificate.right, trace) !== -1 || certificate.result !== -1) return false;
    const payload = `${serializeE0(certificate.left)}<${serializeE0(certificate.right)}|${trace.join("|")}`;
    return trace.length === certificate.trace.length &&
      trace.every((item, index) => item === certificate.trace[index]) &&
      sha256Hex(payload) === certificate.digest;
  } catch {
    return false;
  }
}

export function formatE0(value: E0Ordinal): string {
  assertE0Ordinal(value);
  const pieces = value.terms.map(({ exponent, coefficient }) => {
    const power = compareE0(exponent, ordinalNat(1)) === 0 ? "w" : `w^(${formatE0(exponent)})`;
    return coefficient === 1n ? power : `${power}*${coefficient}`;
  });
  if (value.finite !== 0n || pieces.length === 0) pieces.push(value.finite.toString());
  return pieces.join(" + ");
}

function serializeE0(value: E0Ordinal): string {
  return `[${value.terms.map(term => `(${serializeE0(term.exponent)},${term.coefficient})`).join(",")};${value.finite}]`;
}

function freezeOrdinal(value: E0Ordinal): E0Ordinal {
  return Object.freeze({
    terms: Object.freeze(value.terms.map(term => Object.freeze({
      exponent: freezeOrdinal(term.exponent),
      coefficient: term.coefficient,
    }))),
    finite: value.finite,
  });
}
