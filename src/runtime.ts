// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import type { Pattern, RecursiveFunctionRecord, Kernel } from "./kernel.ts";
import { app, nat, naturalValue, termEquals, v, type Term } from "./ast.ts";
import { KernelError } from "./errors.ts";

export type NativeValue = bigint | NativeApplication;

export interface NativeApplication {
  readonly tag: "app";
  readonly fn: string;
  readonly args: readonly NativeValue[];
}

export interface NativeEvaluationStats {
  readonly calls: number;
  readonly reductions: number;
  readonly cacheHits: number;
}

interface RuntimeState {
  remaining: number;
  calls: number;
  reductions: number;
  cacheHits: number;
  readonly memo: Map<string, NativeValue>;
  readonly prefixes: Map<string, { readonly index: bigint; readonly value: NativeValue }>;
  readonly valueKeys: WeakMap<NativeApplication, string>;
  readonly naturalSpecializations: Map<string, NaturalSpecialization | false>;
  readonly decisionSpecializations: Map<string, NaturalDecision | false>;
  readonly shortcutSpecializations: Map<string, NaturalShortcut | false>;
  readonly usedDefinitions: Set<string>;
  readonly allowedDefinitions?: ReadonlySet<string>;
}

type NaturalOperator = "add" | "mul" | "factorial";
type NaturalDecision = "equal" | "less" | "minus";
type NaturalShortcut = "predecessor" | "sub" | "mod" | "quotient";
interface NaturalSpecialization {
  readonly operator: NaturalOperator;
  readonly definitions: readonly string[];
}

export interface NativeEvaluationOptions {
  readonly allowedDefinitions?: ReadonlySet<string>;
}

interface RecursiveOverride {
  readonly fn: string;
  readonly args: readonly NativeValue[];
  readonly value: NativeValue;
}

/**
 * Execute closed admitted terms using native bigint naturals.
 *
 * Direct calls return values. When the kernel uses this evaluator to
 * check a `compute` certificate, this module is part of the trusted checker.
 * Every optimization below is therefore gated by an exact admitted-equation
 * recognizer; all other definitions use the general equation interpreter.
 */
export function evaluateNative(
  kernel: Kernel,
  term: Term,
  fuel = 10_000_000,
  options: NativeEvaluationOptions = {},
): { readonly value: NativeValue; readonly stats: NativeEvaluationStats; readonly definitions: readonly string[] } {
  if (!Number.isSafeInteger(fuel) || fuel < 1) throw new KernelError("Native evaluation fuel must be positive");
  const state: RuntimeState = {
    remaining: fuel, calls: 0, reductions: 0, cacheHits: 0,
    memo: new Map(), prefixes: new Map(), valueKeys: new WeakMap(), naturalSpecializations: new Map(), decisionSpecializations: new Map(), shortcutSpecializations: new Map(), usedDefinitions: new Set(),
    allowedDefinitions: options.allowedDefinitions,
  };
  const value = evaluate(kernel, term, new Map(), state);
  return nativeResult(value, state);
}

export function evaluateNativeNat(kernel: Kernel, term: Term, fuel = 10_000_000): bigint {
  const result = evaluateNative(kernel, term, fuel).value;
  if (typeof result !== "bigint") throw new KernelError("Native evaluation did not produce a natural number");
  return result;
}

/** Invoke an admitted function directly on native values (for example bigint naturals). */
export function callNative(
  kernel: Kernel,
  fn: string,
  args: readonly NativeValue[],
  fuel = 10_000_000,
): { readonly value: NativeValue; readonly stats: NativeEvaluationStats; readonly definitions: readonly string[] } {
  if (!Number.isSafeInteger(fuel) || fuel < 1) throw new KernelError("Native evaluation fuel must be positive");
  const arity = kernel.functions.get(fn);
  if (arity === undefined) throw new KernelError(`Unknown native function ${fn}`);
  if (arity !== args.length) throw new KernelError(`Native function ${fn} expects ${arity} arguments, got ${args.length}`);
  const state: RuntimeState = {
    remaining: fuel, calls: 0, reductions: 0, cacheHits: 0,
    memo: new Map(), prefixes: new Map(), valueKeys: new WeakMap(), naturalSpecializations: new Map(), decisionSpecializations: new Map(), shortcutSpecializations: new Map(), usedDefinitions: new Set(),
  };
  return nativeResult(invoke(kernel, fn, args, state), state);
}

export function callNativeNat(kernel: Kernel, fn: string, args: readonly NativeValue[], fuel = 10_000_000): bigint {
  const result = callNative(kernel, fn, args, fuel).value;
  if (typeof result !== "bigint") throw new KernelError(`Native function ${fn} did not produce a natural number`);
  return result;
}

function evaluate(
  kernel: Kernel,
  term: Term,
  environment: ReadonlyMap<string, NativeValue>,
  state: RuntimeState,
  override?: RecursiveOverride,
): NativeValue {
  if (term.tag === "nat") {
    if (state.remaining-- <= 0) throw new KernelError("Native evaluation exhausted its fuel");
    state.calls += 1;
    return BigInt(term.value);
  }
  if (term.tag === "var") {
    if (state.remaining-- <= 0) throw new KernelError("Native evaluation exhausted its fuel");
    state.calls += 1;
    const value = environment.get(term.name);
    if (value === undefined) throw new KernelError(`Cannot natively evaluate free variable ${term.name}`);
    return value;
  }

  const args = term.args.map(argument => evaluate(kernel, argument, environment, state, override));
  return invoke(kernel, term.fn, args, state, override);
}

function invoke(
  kernel: Kernel,
  fn: string,
  args: readonly NativeValue[],
  state: RuntimeState,
  override?: RecursiveOverride,
): NativeValue {
  if (state.remaining-- <= 0) throw new KernelError("Native evaluation exhausted its fuel");
  state.calls += 1;
  if (fn === "zero" && args.length === 0) return 0n;
  if (fn === "succ" && args.length === 1 && typeof args[0] === "bigint") return args[0] + 1n;
  if (override && fn === override.fn && nativeArgsEqual(args, override.args)) return override.value;

  const memoKey = `${fn}(${args.map(value => valueKey(value, state.valueKeys)).join(",")})`;
  const cached = state.memo.get(memoKey);
  if (cached !== undefined) { state.cacheHits += 1; return cached; }

  const permitted = state.allowedDefinitions === undefined || state.allowedDefinitions.has(fn);
  const recursive = permitted ? kernel.recursiveFunctions.get(fn) : undefined;
  if (recursive) {
    const decision = classifyNaturalDecision(kernel, fn, state);
    if (decision && args.length === 2 && typeof args[0] === "bigint" && typeof args[1] === "bigint") {
      const left = args[0], right = args[1];
      state.reductions += 1;
      decisionDefinitions(decision).forEach(name => state.usedDefinitions.add(name));
      const result = decision === "minus" ? (left > right ? left - right : 0n) :
        { tag: "app" as const, fn: `Grace.Core.Data.Bool.${decision === "equal" ? left === right : left < right}`,
          args: [] };
      state.memo.set(memoKey, result);
      return result;
    }
    // Predecessor, truncated subtraction, remainder, and quotient descend by
    // ones; on native naturals each is one arithmetic step with a fixed
    // dependency list, mirrored by every reference checker.
    const shortcut = classifyNaturalShortcut(kernel, fn, state);
    if (shortcut && args.length === shortcutArity(shortcut) && args.every(value => typeof value === "bigint")) {
      const naturals = args as readonly bigint[];
      state.reductions += 1;
      shortcutDefinitions(shortcut).forEach(name => state.usedDefinitions.add(name));
      const value = executeNaturalShortcut(shortcut, naturals);
      state.memo.set(memoKey, value);
      return value;
    }
    const specialization = classifyNaturalOperator(
      kernel, fn, state.naturalSpecializations, state.allowedDefinitions,
    );
    if (specialization && args.every(value => typeof value === "bigint")) {
      const naturals = args as readonly bigint[];
      state.reductions += 1;
      specialization.definitions.forEach(name => state.usedDefinitions.add(name));
      const value = executeNaturalOperator(specialization.operator, naturals, state);
      state.memo.set(memoKey, value);
      return value;
    }
    const primitive = evaluatePrimitiveRecursion(kernel, fn, recursive, args, state);
    if (primitive !== undefined) {
      state.usedDefinitions.add(fn);
      state.memo.set(memoKey, primitive);
      return primitive;
    }
    const scrutinee = args[recursive.decreasingParameter];
    for (const equation of recursive.equations) {
      const root = equation.patterns[recursive.decreasingParameter];
      if (!root || !constructorMatches(root, scrutinee)) continue;
      const bindings = new Map<string, NativeValue>();
      if (!equation.patterns.every((pattern, index) => match(pattern, args[index]!, bindings))) continue;
      state.reductions += 1;
      state.usedDefinitions.add(fn);
      const value = evaluate(kernel, equation.body, bindings, state, override);
      state.memo.set(memoKey, value);
      return value;
    }
  }

  const explicit = permitted ? kernel.functionBodies.get(fn) : undefined;
  if (explicit) {
    state.reductions += 1;
    state.usedDefinitions.add(fn);
    const bindings = new Map(explicit.parameters.map((parameter, index) => [parameter, args[index]!]));
    const value = evaluate(kernel, explicit.body, bindings, state, override);
    state.memo.set(memoKey, value);
    return value;
  }

  const value: NativeApplication = { tag: "app", fn, args };
  state.memo.set(memoKey, value);
  return value;
}

const natMod = "Grace.Cumulus.Nat.Mod.";
const natSub = "Grace.Cumulus.Nat.Subtraction.";
const natDiv = "Grace.Cumulus.Nat.Division.";
const natRec = "Grace.Core.Nat.Rec.";
const boolOps = "Grace.Core.Data.BoolOps.";
const bool = "Grace.Core.Data.Bool.";
const rationalOps = "Grace.Cumulus.Rat.Computable.RationalCellOps.";
const bind = (name: string): Pattern => ({ tag: "bind", name });
const ctor = (name: string, ...args: Pattern[]): Pattern => ({ tag: "ctor", name, args });
const equation = (patterns: Pattern[], body: Term) => ({ patterns, body });
const isZero = (name: string) => app(natMod + "isZero", v(name));
const predecessor = (name: string) => app(natRec + "predecessor", v(name));
const nonzero = (name: string) => app(boolOps + "not", isZero(name));

function exactEquations(kernel: Kernel, name: string, parameters: readonly string[],
  expected: readonly ReturnType<typeof equation>[], decreasingParameter = 0): boolean {
  const samePattern = (left: Pattern, right: Pattern): boolean =>
    left.tag === right.tag && (left.tag === "bind" && right.tag === "bind"
      ? left.name === right.name
      : left.tag === "ctor" && right.tag === "ctor" && left.name === right.name &&
        left.args.length === right.args.length && left.args.every((part, index) => samePattern(part, right.args[index]!)));
  const record = kernel.recursiveFunctions.get(name);
  return record?.admission === "structural" && record.decreasingParameter === decreasingParameter &&
    record.parameters.length === parameters.length &&
    record.parameters.every((parameter, index) => parameter === parameters[index]) &&
    record.equations.length === expected.length && record.equations.every((item, index) =>
      item.patterns.length === expected[index]!.patterns.length &&
      item.patterns.every((part, position) => samePattern(part, expected[index]!.patterns[position]!)) &&
      termEquals(item.body, expected[index]!.body));
}

/** An explicit (non-recursive) admitted definition with exactly this body. */
function exactBody(kernel: Kernel, name: string, parameters: readonly string[], body: Term): boolean {
  const record = kernel.functionBodies.get(name);
  return record !== undefined && record.parameters.length === parameters.length &&
    record.parameters.every((parameter, index) => parameter === parameters[index]) &&
    termEquals(record.body, body);
}

// The remainder's fixed dependency list: its own equations, the helper
// equations, and the equality decision with the helpers that one names.
const modDefinitions = [natMod + "mod", natMod + "nextRemainder", natMod + "chooseNat", natMod + "equalNat",
  natMod + "isZero", natRec + "predecessor", boolOps + "not", boolOps + "and"];

function shortcutDefinitions(shortcut: NaturalShortcut): readonly string[] {
  switch (shortcut) {
    case "predecessor": return [natRec + "predecessor"];
    case "sub": return [natSub + "sub", natRec + "predecessor"];
    case "mod": return modDefinitions;
    case "quotient": return [natDiv + "quotientNat", ...modDefinitions];
  }
}

function shortcutArity(shortcut: NaturalShortcut): number {
  return shortcut === "predecessor" ? 1 : 2;
}

function executeNaturalShortcut(shortcut: NaturalShortcut, args: readonly bigint[]): bigint {
  const first = args[0]!;
  const second = args[1] ?? 0n;
  switch (shortcut) {
    case "predecessor": return first > 0n ? first - 1n : 0n;
    case "sub": return first > second ? first - second : 0n;
    // The remainder by zero never wraps, so n % 0 = n; the quotient by zero is zero.
    case "mod": return second === 0n ? first : first % second;
    case "quotient": return second === 0n ? 0n : first / second;
  }
}

/**
 * Exact admitted-equation recognition of the library's descent-by-ones
 * natural operators: predecessor, truncated subtraction, remainder, and
 * quotient, each with its exact helper equations. The fixed dependency list
 * of a recognized shortcut is recorded whatever the arguments are, so the
 * certificate names the same definitions in every implementation.
 */
function classifyNaturalShortcut(kernel: Kernel, name: string, state: RuntimeState): NaturalShortcut | undefined {
  const cached = state.shortcutSpecializations.get(name);
  if (cached !== undefined) return cached || undefined;
  const shortcut: NaturalShortcut | undefined = name === natRec + "predecessor" ? "predecessor" :
    name === natSub + "sub" ? "sub" : name === natMod + "mod" ? "mod" :
    name === natDiv + "quotientNat" ? "quotient" : undefined;
  if (!shortcut || state.allowedDefinitions && shortcutDefinitions(shortcut).some(item => !state.allowedDefinitions!.has(item))) {
    state.shortcutSpecializations.set(name, false);
    return undefined;
  }
  const zero = ctor("zero");
  const successor = (variable: string) => ctor("succ", bind(variable));
  const predecessorExact = exactEquations(kernel, natRec + "predecessor", ["n"], [
    equation([zero], app("zero")), equation([successor("n")], v("n")),
  ]);
  let recognized = false;
  if (shortcut === "predecessor") recognized = predecessorExact;
  else if (shortcut === "sub") {
    recognized = predecessorExact && exactEquations(kernel, natSub + "sub", ["m", "n"], [
      equation([bind("m"), zero], v("m")),
      equation([bind("m"), successor("n")], app(natRec + "predecessor", app(natSub + "sub", v("m"), v("n")))),
    ], 1);
  } else {
    // The remainder equations, shared by the quotient.
    const remainder = (n: string, d: string) => app(natMod + "mod", v(n), v(d));
    const modExact = classifyNaturalDecision(kernel, natMod + "equalNat", state) === "equal" &&
      exactEquations(kernel, natMod + "chooseNat", ["condition", "yes", "no"], [
        equation([ctor(bool + "false"), bind("yes"), bind("no")], v("no")),
        equation([ctor(bool + "true"), bind("yes"), bind("no")], v("yes")),
      ]) &&
      exactBody(kernel, natMod + "nextRemainder", ["d", "r"],
        app(natMod + "chooseNat", app(natMod + "equalNat", app("succ", v("r")), v("d")), nat(0), app("succ", v("r")))) &&
      exactEquations(kernel, natMod + "mod", ["n", "d"], [
        equation([zero, bind("d")], app("zero")),
        equation([successor("n"), bind("d")], app(natMod + "nextRemainder", v("d"), remainder("n", "d"))),
      ]);
    recognized = shortcut === "mod" ? modExact : modExact && exactEquations(kernel, natDiv + "quotientNat", ["n", "d"], [
      equation([zero, bind("d")], app("zero")),
      equation([successor("n"), bind("d")], app(natMod + "chooseNat",
        app(natMod + "equalNat", app("succ", remainder("n", "d")), v("d")),
        app("succ", app(natDiv + "quotientNat", v("n"), v("d"))), app(natDiv + "quotientNat", v("n"), v("d")))),
    ]);
  }
  state.shortcutSpecializations.set(name, recognized ? shortcut : false);
  return recognized ? shortcut : undefined;
}

function decisionDefinitions(decision: NaturalDecision): readonly string[] {
  const common = [natMod + "isZero", natRec + "predecessor"];
  return decision === "minus"
    ? [...common, natMod + "chooseNat", rationalOps + "minus"]
    : [...common, boolOps + "not", boolOps + "and",
      decision === "equal" ? natMod + "equalNat" : rationalOps + "less"];
}

/** Exact admitted-equation recognition, including the helper equations. */
function classifyNaturalDecision(kernel: Kernel, name: string, state: RuntimeState): NaturalDecision | undefined {
  const cached = state.decisionSpecializations.get(name);
  if (cached !== undefined) return cached || undefined;
  const decision: NaturalDecision | undefined = name === natMod + "equalNat" ? "equal" :
    name === rationalOps + "less" ? "less" : name === rationalOps + "minus" ? "minus" : undefined;
  if (!decision || state.allowedDefinitions && decisionDefinitions(decision).some(item => !state.allowedDefinitions!.has(item))) {
    state.decisionSpecializations.set(name, false);
    return undefined;
  }
  const zero = ctor("zero");
  const successor = (variable: string) => ctor("succ", bind(variable));
  const helpers = exactEquations(kernel, natMod + "isZero", ["n"], [
    equation([zero], app(bool + "true")), equation([successor("n")], app(bool + "false")),
  ]) && exactEquations(kernel, natRec + "predecessor", ["n"], [
    equation([zero], app("zero")), equation([successor("n")], v("n")),
  ]);
  const logical = decision === "minus" ? exactEquations(kernel, natMod + "chooseNat", ["condition", "yes", "no"], [
    equation([ctor(bool + "false"), bind("yes"), bind("no")], v("no")),
    equation([ctor(bool + "true"), bind("yes"), bind("no")], v("yes")),
  ]) : exactEquations(kernel, boolOps + "not", ["b"], [
    equation([ctor(bool + "false")], app(bool + "true")),
    equation([ctor(bool + "true")], app(bool + "false")),
  ]) && exactEquations(kernel, boolOps + "and", ["a", "b"], [
    equation([ctor(bool + "false"), bind("b")], app(bool + "false")),
    equation([ctor(bool + "true"), bind("b")], v("b")),
  ]);
  const second = bind(decision === "equal" ? "n" : "b");
  const first = decision === "equal" ? "m" : "a";
  const other = decision === "equal" ? "n" : "b";
  const base = decision === "minus" ? nat(0) : decision === "equal" ? isZero(other) : nonzero(other);
  const recur = app(name, v(first), predecessor(other));
  const step = decision === "minus"
    ? app(natMod + "chooseNat", isZero(other), app("succ", v(first)), recur)
    : app(boolOps + "and", nonzero(other), recur);
  const recognized = helpers && logical && exactEquations(kernel, name, [first, other], [
    equation([zero, second], base), equation([successor(first), second], step),
  ]);
  state.decisionSpecializations.set(name, recognized ? decision : false);
  return recognized ? decision : undefined;
}

function executeNaturalOperator(operator: NaturalOperator, args: readonly bigint[], state: RuntimeState): bigint {
  if (operator === "add") return args[0]! + args[1]!;
  if (operator === "mul") return args[0]! * args[1]!;
  let result = 1n;
  for (let value = 2n; value <= args[0]!; value += 1n) {
    if (state.remaining-- <= 0) throw new KernelError("Native evaluation exhausted its fuel");
    result *= value;
  }
  return result;
}

/** Recognize exact admitted primitive-recursive arithmetic equations. */
function classifyNaturalOperator(
  kernel: Kernel,
  name: string,
  cache: Map<string, NaturalSpecialization | false>,
  allowedDefinitions?: ReadonlySet<string>,
  visiting = new Set<string>(),
): NaturalSpecialization | undefined {
  const cached = cache.get(name);
  if (cached !== undefined) return cached || undefined;
  if (allowedDefinitions !== undefined && !allowedDefinitions.has(name)) return undefined;
  if (visiting.has(name)) return undefined;
  visiting.add(name);
  const recursive = kernel.recursiveFunctions.get(name);
  if (!recursive) { visiting.delete(name); cache.set(name, false); return undefined; }
  const zeroEquation = recursive.equations.find(equation =>
    equation.patterns[recursive.decreasingParameter]?.tag === "ctor" &&
    equation.patterns[recursive.decreasingParameter]?.name === "zero");
  const successorEquation = recursive.equations.find(equation =>
    equation.patterns[recursive.decreasingParameter]?.tag === "ctor" &&
    equation.patterns[recursive.decreasingParameter]?.name === "succ");
  let result: NaturalSpecialization | undefined;
  if (zeroEquation && successorEquation) {
    const root = successorEquation.patterns[recursive.decreasingParameter];
    const predecessor = root?.tag === "ctor" && root.args[0]?.tag === "bind" ? root.args[0].name : undefined;
    const recursiveCall = predecessor === undefined ? undefined : findRecursiveCall(
      successorEquation.body, name, successorEquation.patterns, recursive.decreasingParameter, predecessor,
    );
    if (recursiveCall && recursive.parameters.length === 2 && isOtherPatternVariableBody(
      zeroEquation.body, zeroEquation.patterns, recursive.decreasingParameter,
    ) && successorEquation.body.tag === "app" && successorEquation.body.fn === "succ" &&
      successorEquation.body.args[0] === recursiveCall) {
      result = { operator: "add", definitions: [name] };
    } else {
      const nested = successorEquation.body.tag === "app"
        ? classifyNaturalOperator(kernel, successorEquation.body.fn, cache, allowedDefinitions, visiting)
        : undefined;
      if (recursiveCall && recursive.parameters.length === 2 && isZeroTerm(zeroEquation.body) &&
      successorEquation.body.tag === "app" && successorEquation.body.args.length === 2 &&
      nested?.operator === "add" &&
      successorEquation.body.args.includes(recursiveCall) &&
      successorEquation.body.args.some(term => isOtherPatternVariable(
        term, successorEquation.patterns, recursive.decreasingParameter,
      ))) {
        result = { operator: "mul", definitions: [...new Set([name, ...nested.definitions])].sort() };
      } else if (recursiveCall && recursive.parameters.length === 1 && isOneTerm(zeroEquation.body) &&
      successorEquation.body.tag === "app" && successorEquation.body.args.length === 2 &&
      nested?.operator === "mul" &&
      successorEquation.body.args.includes(recursiveCall) && predecessor !== undefined &&
      successorEquation.body.args.some(term => isSuccessorOf(term, predecessor))) {
        result = { operator: "factorial", definitions: [...new Set([name, ...nested.definitions])].sort() };
      }
    }
  }
  visiting.delete(name);
  cache.set(name, result ?? false);
  return result;
}

function findRecursiveCall(
  term: Term,
  name: string,
  patterns: readonly Pattern[],
  decreasingParameter: number,
  predecessor: string,
): Term | undefined {
  if (term.tag === "app" && term.fn === name && term.args.length === patterns.length &&
    term.args.every((argument, index) => index === decreasingParameter
      ? argument.tag === "var" && argument.name === predecessor
      : patterns[index]?.tag === "bind" && argument.tag === "var" && argument.name === patterns[index].name)) {
    return term;
  }
  if (term.tag === "app") {
    for (const argument of term.args) {
      const found = findRecursiveCall(argument, name, patterns, decreasingParameter, predecessor);
      if (found) return found;
    }
  }
  return undefined;
}

function isOtherPatternVariableBody(body: Term, patterns: readonly Pattern[], decreasingParameter: number): boolean {
  return body.tag === "var" && patterns.some((pattern, index) =>
    index !== decreasingParameter && pattern.tag === "bind" && pattern.name === body.name);
}

function isOtherPatternVariable(term: Term, patterns: readonly Pattern[], decreasingParameter: number): boolean {
  return term.tag === "var" && patterns.some((pattern, index) =>
    index !== decreasingParameter && pattern.tag === "bind" && pattern.name === term.name);
}

function isZeroTerm(term: Term): boolean {
  return naturalValue(term) === 0n;
}

function isOneTerm(term: Term): boolean {
  return naturalValue(term) === 1n;
}

function isSuccessorOf(term: Term, variable: string): boolean {
  return term.tag === "app" && term.fn === "succ" && term.args.length === 1 &&
    term.args[0]?.tag === "var" && term.args[0].name === variable;
}

function nativeResult(value: NativeValue, state: RuntimeState): {
  readonly value: NativeValue; readonly stats: NativeEvaluationStats; readonly definitions: readonly string[];
} {
  return {
    value,
    stats: { calls: state.calls, reductions: state.reductions, cacheHits: state.cacheHits },
    definitions: [...state.usedDefinitions].sort(),
  };
}

function evaluatePrimitiveRecursion(
  kernel: Kernel,
  name: string,
  recursive: RecursiveFunctionRecord,
  args: readonly NativeValue[],
  state: RuntimeState,
): NativeValue | undefined {
  const count = args[recursive.decreasingParameter];
  if (typeof count !== "bigint" || count < 0n) return undefined;
  const zeroEquation = recursive.equations.find(equation => {
    const root = equation.patterns[recursive.decreasingParameter];
    return root?.tag === "ctor" && root.name === "zero";
  });
  const successorEquation = recursive.equations.find(equation => {
    const root = equation.patterns[recursive.decreasingParameter];
    return root?.tag === "ctor" && root.name === "succ";
  });
  if (!zeroEquation || !successorEquation) return undefined;

  const currentArgs = [...args];
  currentArgs[recursive.decreasingParameter] = 0n;
  const zeroBindings = new Map<string, NativeValue>();
  if (!zeroEquation.patterns.every((pattern, index) => match(pattern, currentArgs[index]!, zeroBindings))) return undefined;
  const prefixKey = `${name}(${currentArgs.map(value => valueKey(value, state.valueKeys)).join(",")})`;
  const cached = state.prefixes.get(prefixKey);
  let start = 0n;
  let value: NativeValue;
  if (cached && cached.index <= count) {
    start = cached.index;
    value = cached.value;
    state.cacheHits += 1;
  } else {
    state.reductions += 1;
    value = evaluate(kernel, zeroEquation.body, zeroBindings, state);
    state.memo.set(prefixKey, value);
  }

  // Retain exact intermediate calls, so changing-argument recursion can extend
  // a previously checked prefix instead of recomputing it from zero.
  for (let index = start; index < count; index += 1n) {
    const nextArgs = [...args];
    nextArgs[recursive.decreasingParameter] = index + 1n;
    const bindings = new Map<string, NativeValue>();
    if (!successorEquation.patterns.every((pattern, position) => match(pattern, nextArgs[position]!, bindings))) return undefined;
    const previousArgs = [...args];
    previousArgs[recursive.decreasingParameter] = index;
    state.reductions += 1;
    value = evaluate(kernel, successorEquation.body, bindings, state, { fn: name, args: previousArgs, value });
    const nextKey = `${name}(${nextArgs.map(arg => valueKey(arg, state.valueKeys)).join(",")})`;
    state.memo.set(nextKey, value);
    state.prefixes.set(prefixKey, { index: index + 1n, value });
  }
  return value;
}

function constructorMatches(pattern: Pattern, value: NativeValue | undefined): boolean {
  if (pattern.tag !== "ctor" || value === undefined) return false;
  if (pattern.name === "zero") return value === 0n;
  if (pattern.name === "succ") return typeof value === "bigint" && value > 0n;
  return typeof value !== "bigint" && value.fn === pattern.name;
}

function match(pattern: Pattern, value: NativeValue, bindings: Map<string, NativeValue>): boolean {
  if (pattern.tag === "bind") {
    const previous = bindings.get(pattern.name);
    if (previous !== undefined) return nativeValueEquals(previous, value);
    bindings.set(pattern.name, value);
    return true;
  }
  if (pattern.name === "zero") return value === 0n && pattern.args.length === 0;
  if (pattern.name === "succ") {
    return pattern.args.length === 1 && typeof value === "bigint" && value > 0n &&
      match(pattern.args[0]!, value - 1n, bindings);
  }
  if (typeof value === "bigint" || value.fn !== pattern.name || value.args.length !== pattern.args.length) return false;
  return pattern.args.every((item, index) => match(item, value.args[index]!, bindings));
}

export function nativeValueEquals(left: NativeValue, right: NativeValue): boolean {
  if (typeof left === "bigint" || typeof right === "bigint") return left === right;
  return left.fn === right.fn && left.args.length === right.args.length &&
    left.args.every((item, index) => nativeValueEquals(item, right.args[index]!));
}

export function nativeValueToTerm(value: NativeValue): Term {
  return typeof value === "bigint" ? nat(value) : app(value.fn, ...value.args.map(nativeValueToTerm));
}

function nativeArgsEqual(left: readonly NativeValue[], right: readonly NativeValue[]): boolean {
  return left.length === right.length && left.every((value, index) => nativeValueEquals(value, right[index]!));
}

function valueKey(value: NativeValue, cache: WeakMap<NativeApplication, string>): string {
  if (typeof value === "bigint") return `n${value}`;
  const cached = cache.get(value);
  if (cached !== undefined) return cached;
  const key = `a${value.fn.length}:${value.fn}(${value.args.map(arg => valueKey(arg, cache)).join(",")})`;
  cache.set(value, key);
  return key;
}
