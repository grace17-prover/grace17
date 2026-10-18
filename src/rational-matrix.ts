// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

/** Exact, normalized BigInt execution for finite rational augmented matrices.
 * This is an execution API; semantic certification in Cumulus remains separate.
 */
export interface RationalValue {
  readonly numerator: bigint;
  readonly denominator: bigint;
}

export interface RationalFraction {
  readonly positive: bigint;
  readonly negative: bigint;
  readonly denominator: bigint;
}

export type RationalRowStep =
  | { readonly kind: "swap"; readonly first: number; readonly second: number }
  | { readonly kind: "scale"; readonly row: number; readonly factor: RationalValue }
  | { readonly kind: "addMultiple"; readonly target: number; readonly source: number; readonly factor: RationalValue };

export interface RationalReduction {
  readonly rows: readonly (readonly RationalValue[])[];
  readonly pivots: readonly number[];
  readonly steps: readonly RationalRowStep[];
  readonly status: "unique" | "inconsistent" | "underdetermined";
}

const abs = (n: bigint): bigint => n < 0n ? -n : n;
function gcd(a: bigint, b: bigint): bigint {
  a = abs(a); b = abs(b);
  while (b !== 0n) [a, b] = [b, a % b];
  return a;
}

export function rational(numerator: bigint, denominator = 1n): RationalValue {
  if (denominator === 0n) throw new RangeError("Rational denominator is zero");
  if (numerator === 0n) return { numerator: 0n, denominator: 1n };
  if (denominator < 0n) { numerator = -numerator; denominator = -denominator; }
  const common = gcd(numerator, denominator);
  return { numerator: numerator / common, denominator: denominator / common };
}

export function fromRationalCell(cell: RationalFraction): RationalValue {
  if (cell.positive < 0n || cell.negative < 0n || cell.denominator <= 0n)
    throw new RangeError("RationalCell requires naturals and a positive denominator");
  return rational(cell.positive - cell.negative, cell.denominator);
}

export function toRationalCell(value: RationalValue): RationalFraction {
  const normalized = rational(value.numerator, value.denominator);
  return { positive: normalized.numerator > 0n ? normalized.numerator : 0n,
    negative: normalized.numerator < 0n ? -normalized.numerator : 0n,
    denominator: normalized.denominator };
}

const ZERO = rational(0n);
const ONE = rational(1n);
const neg = (a: RationalValue): RationalValue => ({ numerator: -a.numerator, denominator: a.denominator });
const mul = (a: RationalValue, b: RationalValue): RationalValue =>
  rational(a.numerator * b.numerator, a.denominator * b.denominator);
const add = (a: RationalValue, b: RationalValue): RationalValue =>
  rational(a.numerator * b.denominator + b.numerator * a.denominator, a.denominator * b.denominator);
const inv = (a: RationalValue): RationalValue => rational(a.denominator, a.numerator);

export function replayRationalRows(rows: readonly (readonly RationalValue[])[],
  steps: readonly RationalRowStep[]): readonly (readonly RationalValue[])[] {
  const result = rows.map(row => row.map(value => rational(value.numerator, value.denominator)));
  const width = result[0]?.length ?? 0;
  if (result.some(row => row.length !== width)) throw new RangeError("Ragged matrix");
  for (const step of steps) {
    const indices = step.kind === "swap" ? [step.first, step.second] :
      step.kind === "scale" ? [step.row] : [step.target, step.source];
    if (indices.some(index => !Number.isSafeInteger(index) || index < 0 || index >= result.length))
      throw new RangeError("Row index outside matrix");
    if (step.kind === "swap") {
      [result[step.first], result[step.second]] = [result[step.second]!, result[step.first]!];
    } else if (step.kind === "scale") {
      if (step.factor.numerator === 0n) throw new RangeError("Cannot scale by zero");
      result[step.row] = result[step.row]!.map(value => mul(value, step.factor));
    } else {
      result[step.target] = result[step.target]!.map((value, column) =>
        add(value, mul(step.factor, result[step.source]![column]!)));
    }
  }
  return result;
}

export function reduceRationalMatrix(input: readonly (readonly RationalValue[])[], variables: number): RationalReduction {
  if (!Number.isSafeInteger(variables) || variables < 0) throw new RangeError("Invalid variable count");
  if (input.some(row => row.length !== variables + 1)) throw new RangeError("Expected augmented rectangular matrix");
  const rows = input.map(row => row.map(value => rational(value.numerator, value.denominator)));
  const steps: RationalRowStep[] = [];
  const pivots: number[] = [];
  let rank = 0;
  for (let column = 0; column < variables && rank < rows.length; column++) {
    const candidate = rows.findIndex((row, index) => index >= rank && row[column]!.numerator !== 0n);
    if (candidate < 0) continue;
    if (candidate !== rank) {
      [rows[candidate], rows[rank]] = [rows[rank]!, rows[candidate]!];
      steps.push({ kind: "swap", first: rank, second: candidate });
    }
    const factor = inv(rows[rank]![column]!);
    rows[rank] = rows[rank]!.map(value => mul(value, factor));
    steps.push({ kind: "scale", row: rank, factor });
    for (let other = 0; other < rows.length; other++) {
      if (other === rank || rows[other]![column]!.numerator === 0n) continue;
      const multiple = neg(rows[other]![column]!);
      rows[other] = rows[other]!.map((value, index) => add(value, mul(multiple, rows[rank]![index]!)));
      steps.push({ kind: "addMultiple", target: other, source: rank, factor: multiple });
    }
    pivots.push(column);
    rank++;
  }
  const inconsistent = rows.some(row => row.slice(0, variables).every(value => value.numerator === 0n) &&
    row[variables]!.numerator !== 0n);
  return { rows, pivots, steps,
    status: inconsistent ? "inconsistent" : rank === variables ? "unique" : "underdetermined" };
}
