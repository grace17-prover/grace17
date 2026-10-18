// Linear arithmetic over the reals by Fourier-Motzkin elimination with checked certificates.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { app, formulaEquals, not, pred, termCanonical, termEquals, v, freeTermVariables, type Formula, type Term } from "./ast.ts";
import { andElimLeft, andElimRight, assume, dne, eqElim, impIntro, refl, type Proof } from "./proof.ts";

/**
 * Everything the engine needs from the elaborator. The engine never touches
 * the kernel directly: every lemma instance, every carrier guard, and the one
 * ring identity it uses come back as proofs that the caller has already
 * checked, and the final certificate is a proof object that the
 * kernel replays from scratch.
 */
export interface RealLinearArithmeticContext {
  readonly goal: Formula;
  readonly facts: readonly { readonly formula: Formula; readonly proof: Proof }[];
  /** Fully qualified real function symbols that are in scope. */
  readonly symbols: {
    readonly add?: string; readonly sub?: string; readonly neg?: string;
    readonly zero?: string; readonly one?: string;
    /** The graph-application symbol and the addition graph term, which is how the order laws state sums. */
    readonly call2?: string; readonly addGraph?: Term;
    /** The negation graph term, when prefix minus is a graph application. */
    readonly negGraph?: Term;
    readonly mul?: string; readonly mulGraph?: Term;
  };
  /** The relation graphs for strict and non-strict comparison, as terms. */
  readonly graphs?: { readonly less: Term; readonly le: Term };
  /**
   * How comparisons are written, when not as `relates` on the two graphs. A
   * presentation without a non-strict order may read its non-strict
   * comparisons as equalities, with the rule names below reinterpreted.
   */
  readonly comparison?: {
    readonly build: (strict: boolean, left: Term, right: Term) => Formula;
    readonly parse: (formula: Formula) => { strict: boolean; left: Term; right: Term } | undefined;
  };
  /** Instantiate a named library theorem, discharge its Real guards, and feed the premises. */
  readonly rule: (name: string, terms: readonly Term[], premises: readonly Proof[]) => Proof | undefined;
  /** A closed library theorem, such as realZero.lt_one. */
  readonly theoremFact: (name: string) => Proof | undefined;
  readonly isReal: (term: Term) => boolean;
  /** The value of a numeral term, which linearizes to that many ones. */
  readonly numeral?: (term: Term) => bigint | undefined;
  /** A checked proof of left = right by commutative-ring normalization, if the two sides agree. */
  readonly ringEquality: (left: Term, right: Term) => Proof | undefined;
  /**
   * Division by a numeral, t / k with k ≠ 0. The quotient stays an atom and
   * the identity t = k * (t / k), proved by the caller from the field laws
   * once 0 < k is derived here, enters as a hypothesis, so the elimination
   * reasons about t / k as the k-th part of t.
   */
  readonly quotient?: {
    readonly parse: (term: Term) => { readonly numerator: Term; readonly divisor: Term } | undefined;
    readonly identity: (numerator: Term, divisor: Term, quotient: Term, positive: Proof) => Proof | undefined;
  };
  readonly check: (proof: Proof) => Formula;
  /**
   * Formulas the certificate assumes and later discharges (the negated goal,
   * or the comparison of a negated goal). The caller must treat them as
   * active assumptions while checking intermediate proofs.
   */
  readonly extraAssumptions: Formula[];
  readonly constraintLimit?: number;
}

type LinearForm = Map<string, bigint>;

interface Hypothesis {
  readonly left: Term;
  readonly right: Term;
  readonly strict: boolean;
  /** Proves relates(graph, left, right) for the matching graph. */
  readonly proof: Proof;
}

interface Constraint {
  readonly strict: boolean;
  /** Coefficients of left - right, which the constraint asserts is < 0 or ≤ 0. */
  readonly form: LinearForm;
  /** Nonnegative integer multipliers of the original hypotheses. */
  readonly multipliers: ReadonlyMap<number, bigint>;
}

interface Comparison { readonly left: Term; readonly right: Term; readonly strict: boolean; readonly proof: Proof }

/**
 * Prove a real comparison, equality, negated comparison, or ⊥ from the
 * linear content of the local facts. Returns undefined when the facts do not
 * entail the goal linearly, so the caller may try other methods.
 */
// Diagnostics are opt-in through the environment and must not assume a Node
// global: the same module runs inside the browser Workbench worker.
const debugEnabled = typeof process !== "undefined" && Boolean(process.env?.G17_LINARITH_DEBUG);
const debug = (message: string): void => { if (debugEnabled) console.error(`[linarith] ${message}`); };

export function proveRealLinearArithmetic(context: RealLinearArithmeticContext): Proof | undefined {
  const { goal, graphs } = context;
  debug(`goal ${goal.tag} symbols ${JSON.stringify(context.symbols)}`);
  if (!graphs && !context.comparison) return undefined;
  const relation = (formula: Formula): { strict: boolean; left: Term; right: Term } | undefined => {
    if (context.comparison) return context.comparison.parse(formula);
    if (formula.tag !== "pred" || formula.pred !== "relates" || formula.args.length !== 3) return undefined;
    const graph = formula.args[0]!;
    if (termEquals(graph, graphs!.less)) return { strict: true, left: formula.args[1]!, right: formula.args[2]! };
    if (termEquals(graph, graphs!.le)) return { strict: false, left: formula.args[1]!, right: formula.args[2]! };
    return undefined;
  };
  const relates = (strict: boolean, left: Term, right: Term): Formula =>
    context.comparison
      ? context.comparison.build(strict, left, right)
      : pred("relates", strict ? graphs!.less : graphs!.le, left, right);

  if (goal.tag === "eq") {
    if (!context.isReal(goal.left) || !context.isReal(goal.right)) return undefined;
    const forward = proveRealLinearArithmetic({ ...context, goal: relates(false, goal.left, goal.right) });
    if (!forward) return undefined;
    const backward = proveRealLinearArithmetic({ ...context, goal: relates(false, goal.right, goal.left) });
    if (!backward) return undefined;
    return context.rule("realLe.antisymmetric", [goal.left, goal.right], [forward, backward]);
  }

  const hypotheses: Hypothesis[] = [];
  const addFact = (formula: Formula, proof: Proof, depth = 0): void => {
    if (depth > 8) return;
    const comparison = relation(formula);
    if (comparison) { hypotheses.push({ ...comparison, proof }); return; }
    if (formula.tag === "and") {
      addFact(formula.left, andElimLeft(proof), depth + 1);
      addFact(formula.right, andElimRight(proof), depth + 1);
      return;
    }
    if (formula.tag === "eq" && context.isReal(formula.left) && context.isReal(formula.right)) {
      const reflexive = context.rule("realLe.reflexive", [formula.left], []);
      if (!reflexive) return;
      const variable = freshVariable([formula.left, formula.right]);
      hypotheses.push({ left: formula.left, right: formula.right, strict: false,
        proof: eqElim(proof, variable, relates(false, formula.left, v(variable)), reflexive) });
      hypotheses.push({ left: formula.right, right: formula.left, strict: false,
        proof: eqElim(proof, variable, relates(false, v(variable), formula.left), reflexive) });
      return;
    }
    if (formula.tag === "imp" && formula.right.tag === "bottom") {
      const denied = relation(formula.left);
      if (!denied) return;
      // ¬(l ≤ r) gives r < l, and ¬(l < r) gives r ≤ l.
      const flipped = denied.strict
        ? context.rule("realLe.of_not_less", [denied.right, denied.left], [proof])
        : context.rule("realLess.of_not_le", [denied.left, denied.right], [proof]);
      if (flipped) hypotheses.push({ left: denied.right, right: denied.left, strict: !denied.strict, proof: flipped });
    }
  };
  for (const fact of context.facts) addFact(fact.formula, fact.proof);

  // Negate the goal and look for a contradiction.
  let finish: ((absurdity: Proof) => Proof) | undefined;
  const target = relation(goal);
  if (target) {
    context.extraAssumptions.push(not(goal));
    const negated = assume(not(goal));
    const flipped = target.strict
      ? context.rule("realLe.of_not_less", [target.right, target.left], [negated])
      : context.rule("realLess.of_not_le", [target.left, target.right], [negated]);
    if (!flipped) { debug("could not negate the goal"); return undefined; }
    hypotheses.push({ left: target.right, right: target.left, strict: !target.strict, proof: flipped });
    finish = absurdity => dne(goal, impIntro(not(goal), absurdity));
  } else if (goal.tag === "bottom") {
    finish = absurdity => absurdity;
  } else if (goal.tag === "imp" && goal.right.tag === "bottom" && relation(goal.left)) {
    const assumed = relation(goal.left)!;
    context.extraAssumptions.push(goal.left);
    hypotheses.push({ ...assumed, proof: assume(goal.left) });
    finish = absurdity => impIntro(goal.left, absurdity);
  } else {
    return undefined;
  }

  // A quotient t / k by a numeral, anywhere in a hypothesis or the goal,
  // brings the identity t = k * (t / k) as a hypothesis; the quotient itself
  // is an atom below.
  if (context.quotient && context.symbols.zero) {
    const zero = app(context.symbols.zero);
    const seen = new Set<string>();
    const visit = (term: Term): void => {
      if (term.tag !== "app") return;
      const parsed = context.quotient!.parse(term);
      const key = termCanonical(term);
      if (parsed && !seen.has(key)) {
        seen.add(key);
        const positive = proveRealLinearArithmetic({ ...context, goal: relates(true, zero, parsed.divisor), facts: [] });
        const identity = positive && context.quotient!.identity(parsed.numerator, parsed.divisor, term, positive);
        if (identity) {
          try { addFact(context.check(identity), identity); } catch { debug(`quotient identity for ${key} failed`); }
        }
      }
      term.args.forEach(visit);
    };
    for (const hypothesis of [...hypotheses]) { visit(hypothesis.left); visit(hypothesis.right); }
  }

  // Linearize over atoms. Zero is the additive identity; one is an atom with
  // the library fact 0 < 1 attached whenever it occurs.
  const atoms = new Map<string, Term>();
  const linearize = (term: Term): LinearForm => {
    const result: LinearForm = new Map();
    const accumulate = (current: Term, sign: bigint): void => {
      const value = context.numeral?.(current);
      if (value !== undefined && context.symbols.one) {
        if (value !== 0n) accumulate(app(context.symbols.one), sign * value);
        return;
      }
      if (current.tag === "app") {
        const { symbols } = context;
        if (current.args.length === 0 && symbols.zero && current.fn === symbols.zero) return;
        if (current.args.length === 2 && symbols.add && current.fn === symbols.add) {
          accumulate(current.args[0]!, sign); accumulate(current.args[1]!, sign); return;
        }
        if (current.args.length === 2 && symbols.sub && current.fn === symbols.sub) {
          accumulate(current.args[0]!, sign); accumulate(current.args[1]!, -sign); return;
        }
        if (current.args.length === 1 && symbols.neg && current.fn === symbols.neg) {
          accumulate(current.args[0]!, -sign); return;
        }
        if (current.args.length === 3 && current.fn.endsWith(".Algebra.call2") && symbols.addGraph &&
            termEquals(current.args[0]!, symbols.addGraph)) {
          accumulate(current.args[1]!, sign); accumulate(current.args[2]!, sign); return;
        }
        if (current.args.length === 2 && current.fn === "apply" && symbols.negGraph &&
            termEquals(current.args[0]!, symbols.negGraph)) {
          accumulate(current.args[1]!, -sign); return;
        }
        // A product with a numeral factor is a scalar multiple, so k * t and
        // t * k linearize to k times the form of t.
        const factors = current.args.length === 2 && symbols.mul && current.fn === symbols.mul ? [current.args[0]!, current.args[1]!]
          : current.args.length === 3 && current.fn.endsWith(".Algebra.call2") && symbols.mulGraph &&
            termEquals(current.args[0]!, symbols.mulGraph) ? [current.args[1]!, current.args[2]!] : undefined;
        if (factors && context.numeral) {
          const [left, right] = factors;
          const leftValue = context.numeral(left);
          if (leftValue !== undefined) { if (leftValue !== 0n) accumulate(right, sign * leftValue); return; }
          const rightValue = context.numeral(right);
          if (rightValue !== undefined) { if (rightValue !== 0n) accumulate(left, sign * rightValue); return; }
        }
      }
      const key = termCanonical(current);
      atoms.set(key, current);
      const next = (result.get(key) ?? 0n) + sign;
      if (next === 0n) result.delete(key); else result.set(key, next);
    };
    accumulate(term, 1n);
    return result;
  };
  const difference = (left: LinearForm, right: LinearForm): LinearForm => {
    const result = new Map(left);
    for (const [key, value] of right) {
      const next = (result.get(key) ?? 0n) - value;
      if (next === 0n) result.delete(key); else result.set(key, next);
    }
    return result;
  };
  let constraints: Constraint[] = hypotheses.map((hypothesis, index) => ({
    strict: hypothesis.strict,
    form: difference(linearize(hypothesis.left), linearize(hypothesis.right)),
    multipliers: new Map([[index, 1n]]),
  }));
  if (context.symbols.one && context.symbols.zero && atoms.has(termCanonical(app(context.symbols.one)))) {
    const positiveOne = context.theoremFact("realZero.lt_one");
    if (positiveOne) {
      const index = hypotheses.length;
      hypotheses.push({ left: app(context.symbols.zero), right: app(context.symbols.one), strict: true, proof: positiveOne });
      constraints.push({ strict: true, form: new Map([[termCanonical(app(context.symbols.one)), -1n]]), multipliers: new Map([[index, 1n]]) });
    }
  }

  debug(`${hypotheses.length} hypotheses, ${atoms.size} atoms: ${[...constraints].map(c => `${c.strict ? "<" : "≤"} ${[...c.form].map(([k, v]) => `${v}·${k.slice(0, 24)}`).join(" + ")}`).join(" ; ")}`);
  const contradiction = eliminate(constraints, context.constraintLimit ?? 16_384);
  if (!contradiction) { debug("no contradiction"); return undefined; }
  debug(`multipliers ${JSON.stringify([...contradiction.multipliers].map(([i, m]) => [i, m.toString()]))}`);

  // Certificate: scale each used hypothesis by its multiplier through
  // repeated checked addition, add the results, and normalize both sides.
  const { call2, addGraph } = context.symbols;
  if (!call2 || !addGraph) { debug("no graph addition symbol"); return undefined; }
  const addTerm = (left: Term, right: Term): Term => app(call2, addGraph, left, right);
  const combine = (first: Comparison, second: Comparison): Comparison | undefined => {
    const left = addTerm(first.left, second.left);
    const right = addTerm(first.right, second.right);
    let proof: Proof | undefined;
    if (!first.strict && !second.strict) {
      proof = context.rule("realLe.add", [first.left, first.right, second.left, second.right], [first.proof, second.proof]);
    } else if (first.strict && second.strict) {
      proof = context.rule("realLess.add", [first.left, first.right, second.left, second.right], [first.proof, second.proof]);
    } else if (!first.strict) {
      const shifted = context.rule("realLe.add_right", [first.left, first.right, second.left], [first.proof]);
      const raised = context.rule("realLess.add_left", [second.left, second.right, first.right], [second.proof]);
      if (shifted && raised) proof = context.rule("realLe.transitive_less",
        [left, addTerm(first.right, second.left), right], [shifted, raised]);
    } else {
      const shifted = context.rule("realLess.add_right", [first.left, first.right, second.left], [first.proof]);
      const raised = context.rule("realLe.add_left", [second.left, second.right, first.right], [second.proof]);
      if (shifted && raised) proof = context.rule("realLess.transitive_le",
        [left, addTerm(first.right, second.left), right], [shifted, raised]);
    }
    return proof ? { left, right, strict: first.strict || second.strict, proof } : undefined;
  };
  const scale = (base: Comparison, count: bigint): Comparison | undefined => {
    let result: Comparison | undefined;
    let power: Comparison | undefined = base;
    let remaining = count;
    while (remaining > 0n) {
      if (remaining & 1n) {
        result = result ? combine(result, power!) : power;
        if (!result) return undefined;
      }
      remaining >>= 1n;
      if (remaining > 0n) {
        power = combine(power!, power!);
        if (!power) return undefined;
      }
    }
    return result;
  };
  let total: Comparison | undefined;
  let copies = 0n;
  for (const [index, multiplier] of [...contradiction.multipliers].sort((a, b) => a[0] - b[0])) {
    if (multiplier <= 0n) continue;
    copies += multiplier;
    if (copies > 4_096n) return undefined;
    const hypothesis = hypotheses[index]!;
    const scaled = scale({ left: hypothesis.left, right: hypothesis.right, strict: hypothesis.strict, proof: hypothesis.proof }, multiplier);
    if (!scaled) { debug(`scaling hypothesis ${index} failed`); return undefined; }
    total = total ? combine(total, scaled) : scaled;
    if (!total) { debug(`combining hypothesis ${index} failed`); return undefined; }
  }
  if (!total || !total.strict) return undefined;
  const identity = termEquals(total.left, total.right) ? refl(total.left) : context.ringEquality(total.left, total.right);
  if (!identity) { debug("ring identity failed"); return undefined; }
  const variable = freshVariable([total.left, total.right]);
  const cycle = eqElim(identity, variable, relates(true, v(variable), total.right), total.proof);
  const absurdity = context.rule("realLess.not_self", [total.right], [cycle]);
  if (!absurdity) { debug("irreflexivity failed"); return undefined; }
  const result = finish(absurdity);
  return formulaEquals(context.check(result), goal) ? result : undefined;
}

function freshVariable(terms: readonly Term[]): string {
  const forbidden = new Set(terms.flatMap(term => [...freeTermVariables(term)]));
  let variable = "__linarith";
  while (forbidden.has(variable)) variable += "_";
  return variable;
}

function formKey(constraint: Constraint): string {
  return `${constraint.strict ? "<" : "≤"}|${[...constraint.form].sort((a, b) => a[0] < b[0] ? -1 : a[0] > b[0] ? 1 : 0)
    .map(([key, value]) => `${key}:${value}`).join(",")}`;
}

function gcd(left: bigint, right: bigint): bigint {
  let a = left < 0n ? -left : left;
  let b = right < 0n ? -right : right;
  while (b) [a, b] = [b, a % b];
  return a;
}

function scaleConstraint(constraint: Constraint, factor: bigint): Constraint {
  const form: LinearForm = new Map();
  for (const [key, value] of constraint.form) form.set(key, value * factor);
  const multipliers = new Map<number, bigint>();
  for (const [key, value] of constraint.multipliers) multipliers.set(key, value * factor);
  return { strict: constraint.strict, form, multipliers };
}

function addConstraints(first: Constraint, second: Constraint): Constraint {
  const form = new Map(first.form);
  for (const [key, value] of second.form) {
    const next = (form.get(key) ?? 0n) + value;
    if (next === 0n) form.delete(key); else form.set(key, next);
  }
  const multipliers = new Map(first.multipliers);
  for (const [key, value] of second.multipliers) multipliers.set(key, (multipliers.get(key) ?? 0n) + value);
  return { strict: first.strict || second.strict, form, multipliers };
}

/** Fourier-Motzkin elimination over the rationals; returns a derived 0 < 0 with its multipliers. */
function eliminate(input: readonly Constraint[], limit: number): Constraint | undefined {
  const deduplicate = (items: readonly Constraint[]): Constraint[] => {
    const unique = new Map<string, Constraint>();
    for (const item of items) if (!unique.has(formKey(item))) unique.set(formKey(item), item);
    return [...unique.values()];
  };
  let constraints = deduplicate(input);
  const contradiction = (): Constraint | undefined => constraints.find(item => item.strict && item.form.size === 0);
  if (contradiction()) return contradiction();
  const variables = new Set(constraints.flatMap(item => [...item.form.keys()]));
  while (variables.size > 0) {
    let selected: string | undefined;
    let selectedCost: bigint | undefined;
    for (const variable of variables) {
      let positive = 0n, negative = 0n;
      for (const item of constraints) {
        const coefficient = item.form.get(variable) ?? 0n;
        if (coefficient > 0n) positive += 1n; else if (coefficient < 0n) negative += 1n;
      }
      const cost = positive * negative;
      if (selectedCost === undefined || cost < selectedCost || (cost === selectedCost && variable < selected!)) {
        selected = variable; selectedCost = cost;
      }
    }
    const variable = selected!;
    variables.delete(variable);
    const positive = constraints.filter(item => (item.form.get(variable) ?? 0n) > 0n);
    const negative = constraints.filter(item => (item.form.get(variable) ?? 0n) < 0n);
    const next = constraints.filter(item => !item.form.has(variable));
    for (const upper of positive) for (const lower of negative) {
      const upperCoefficient = upper.form.get(variable)!;
      const lowerCoefficient = -lower.form.get(variable)!;
      const divisor = gcd(upperCoefficient, lowerCoefficient);
      const combined = addConstraints(
        scaleConstraint(upper, lowerCoefficient / divisor), scaleConstraint(lower, upperCoefficient / divisor));
      next.push(combined);
      if (next.length > limit) return undefined;
    }
    constraints = deduplicate(next);
    const found = contradiction();
    if (found) return found;
  }
  return contradiction();
}
