// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { app, not, or, formulaCanonical, formulaEquals, freeFormulaVariables, freeTermVariables, nat, naturalValue, pred, substituteFormula, termCanonical, termEquals, v, type Formula, type Term } from "./ast.ts";
import type { Kernel } from "./kernel.ts";
import { formatFormula, formatTerm } from "./pretty.ts";
import { proveCongruence, proveGround } from "./decision-procedures.ts";
import { isTransparentPredicate, openGuardFact, prepareRefinementProver, proveLiteralDistinctnessGoal, proveRefinement, proveSoftType, refuteLiteralEquation, tauRelievable, type RefinementProver, type ScopeVisibility } from "./type-system.ts";
import {
  andElimLeft, andElimRight, andIntro, assume, at, calc, congr, dne, eqElim, existsElim, existsIntro, falseElim, forallElim, forallIntro, iffElimLeft, iffElimRight,
  iffIntro, impElim, impIntro, orElim, orIntroLeft, orIntroRight, refl, symm, type Proof,
} from "./proof.ts";

export interface SimpOptions {
  readonly using: readonly Proof[] | PreparedRewrites;
  readonly assumptions?: readonly Formula[];
  readonly facts?: readonly Proof[];
  readonly fuel?: number;
  /** Permit capture-safe transport of binder-independent terms beneath quantifiers. */
  readonly underBinders?: boolean;
  readonly stats?: SettleStats;
  /** Recursive rewrite-hypothesis relief is disabled unless explicitly configured. */
  readonly backchain?: false | BackchainOptions;
  readonly [reliefSession]?: ReliefState;
  /** Whether contextual equalities become rewrite rules. Defaults to true. */
  readonly useContextEqualities?: boolean;
  /**
   * Universal lemmas for ground classical reasoning with equality, such as
   * the visible membership characterizations; when present, logical goals
   * are first tried by `proveGround` with these lemmas and the rules.
   */
  readonly ground?: readonly Proof[];
  /** The declarations and guards the current scope sees; absent, the whole kernel. */
  readonly visibility?: ScopeVisibility;
}


const reliefSession = Symbol("simp relief session");

/** Share relief work across closure and residual simplification of one tactic. */
export function createSimpSession(options: SimpOptions): SimpOptions {
  return { ...options, [reliefSession]: reliefState(options) };
}

export interface BackchainOptions {
  /** Maximum number of recursive rule applications on a hypothesis path. */
  readonly depth: number;
  /** Shared allowance for relief entries, rule views, and contextual binding attempts. */
  readonly work: number;
  /** Maximum canonical formula length admitted to recursive relief. */
  readonly maxFormulaSize?: number;
  /** Optional per-rule, per-hypothesis extra-depth caps; they only tighten depth. */
  readonly hypothesisDepths?: ReadonlyMap<Proof, readonly number[]>;
  readonly trace?: (event: ReliefTrace) => void;
}

export interface ReliefTrace {
  readonly goal: string;
  readonly depth: number;
  readonly remaining: number;
  readonly rule?: string;
  readonly result: "context" | "rule" | "disabled" | "depth" | "work" | "size" | "cycle" | "unproved";
}

/** One request owns this state; every guard and failed candidate shares it. */
interface ReliefState {
  readonly policy: false | BackchainOptions;
  remaining: number;
  readonly active: Set<string>;
  readonly visibility?: ScopeVisibility;
}

function reliefState(options: SimpOptions): ReliefState {
  if (options[reliefSession]) return options[reliefSession];
  const policy = options.backchain ?? false;
  if (policy && (![policy.depth, policy.work, policy.maxFormulaSize ?? 16384]
    .every(n => Number.isSafeInteger(n) && n >= 0) || policy.depth > 128)) {
    throw new Error("backchain requires nonnegative safe integer limits and depth at most 128");
  }
  if (policy && [...(policy.hypothesisDepths?.values() ?? [])].some(limits =>
    limits.some(n => !Number.isSafeInteger(n) || n < 0))) throw new Error("invalid hypothesis depth limit");
  return { policy, remaining: policy ? policy.work : 0, active: new Set(), visibility: options.visibility };
}

/** No case splits, existential guesses, or calls into the general settle search. */
function relieveHypothesis(
  kernel: Kernel, wanted: Formula, rules: readonly Proof[],
  context: readonly Formula[], facts: readonly Proof[], state: ReliefState, depth = 0, ceiling = state.policy ? state.policy.depth : 0,
): Proof | undefined {
  const goal = formulaCanonical(wanted);
  const report = (result: ReliefTrace["result"], rule?: string): void => {
    if (state.policy) state.policy.trace?.({ goal, depth, remaining: state.remaining, result, ...(rule ? { rule } : {}) });
  };
  // Direct evidence remains available even at depth/work zero.
  const available = expandFacts(kernel, [
    ...context.map(formula => ({ formula, proof: assume(formula) })),
    ...facts.map(proof => ({ formula: kernel.checkProof(proof, context), proof })),
  ], state.visibility);
  const direct = available.find(item => formulaEquals(item.formula, wanted));
  if (direct) { report("context"); return direct.proof; }
  const doubleNegative = available.find(item => formulaEquals(item.formula, not(not(wanted))));
  if (doubleNegative) { report("context"); return dne(wanted, doubleNegative.proof); }
  if (wanted.tag === "eq" && termEquals(wanted.left, wanted.right)) return refl(wanted.left);
  if (wanted.tag === "pred" && tauRelievable(kernel, wanted, state.visibility)) {
    const typed = proveRefinement(kernel, wanted.args.at(-1)!, wanted.pred, wanted.args.slice(0, -1), context, facts, state.visibility);
    if (typed) { report("context"); return typed; }
  }
  if (wanted.tag === "and") {
    const left = relieveHypothesis(kernel, wanted.left, rules, context, facts, state, depth, ceiling);
    if (!left) return undefined;
    const right = relieveHypothesis(kernel, wanted.right, rules, context, facts, state, depth, ceiling);
    return right ? andIntro(left, right) : undefined;
  }
  if (!state.policy) { report("disabled"); return undefined; }
  if (goal.length > (state.policy.maxFormulaSize ?? 16384)) { report("size"); return undefined; }
  if (depth >= ceiling) { report("depth"); return undefined; }
  if (state.remaining <= 0) { report("work"); return undefined; }
  state.remaining -= 1;
  const key = JSON.stringify([goal, context.map(formulaCanonical), facts.map(proof => formulaCanonical(kernel.checkProof(proof, context)))]);
  if (state.active.has(key)) { report("cycle"); return undefined; }
  state.active.add(key);
  try {
    for (const rule of rules) {
      if (state.remaining <= 0) { report("work"); return undefined; }
      state.remaining -= 1;
      let schema = kernel.checkProof(rule, context);
      const variables: string[] = [];
      while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
      // A negative conclusion is itself an implication to false. Try each
      // suffix, retaining precisely how many hypotheses precede it.
      let hypothesisCount = 0;
      const conditions: Formula[] = [];
      const variableSet = new Set(variables);
      // Bind variables absent from the conclusion only by matching a rule
      // hypothesis against checked contextual evidence. Never invent terms.
      function* bindings(initial: Map<string, Term>, premises: readonly Formula[]): Generator<Map<string, Term>> {
        if (variables.every(variable => initial.has(variable))) { yield initial; return; }
        const condition = premises.find(item =>
          [...freeFormulaVariables(item)].some(name => variableSet.has(name) && !initial.has(name)));
        if (!condition) return;
        let found = false;
        for (const fact of available) {
          if (state.remaining <= 0) { report("work"); return; }
          state.remaining -= 1;
          const next = new Map(initial);
          if (matchFormula(condition, fact.formula, variableSet, next) && next.size > initial.size) {
            found = true;
            yield* bindings(next, premises);
          }
        }
        // No contextual fact has the shape of a typed guard such as
        // `F(f) : a ⟶ b`: its open endpoints are completed through the
        // certified rules and instances, as the guards of a composite's
        // factors fix its endpoints. Terms are still never invented: a
        // completion is a checked proof of the guard at those endpoints.
        if (!found && condition.tag === "pred" && isTransparentPredicate(kernel, condition.pred, state.visibility)) {
          let instantiated: Formula = condition;
          for (const [name, value] of initial) instantiated = substituteFormula(instantiated, name, value);
          if (instantiated.tag !== "pred") return;
          const request = instantiated.args.map(argument =>
            [...freeTermVariables(argument)].some(name => variableSet.has(name) && !initial.has(name)) ? undefined : argument);
          if (request.every(argument => argument === undefined)) return;
          let completed;
          try { completed = refinementProver()?.complete(condition.pred, request); } catch { completed = undefined; }
          if (!completed) return;
          const next = new Map(initial);
          if (matchFormula(condition, pred(condition.pred, ...completed.arguments), variableSet, next) && next.size > initial.size) {
            yield* bindings(next, premises);
          }
        }
      }
      let refinements: RefinementProver | undefined;
      const refinementProver = (): RefinementProver | undefined => {
        try { return refinements ??= prepareRefinementProver(kernel, context, facts, state.visibility); } catch { return undefined; }
      };
      function* projections(formula: Formula, path: readonly boolean[] = []): Generator<{ formula: Formula; path: readonly boolean[] }> {
        yield { formula, path };
        if (formula.tag === "and") {
          yield* projections(formula.left, [...path, false]);
          yield* projections(formula.right, [...path, true]);
        }
      }
      function* alternatives(formula: Formula) {
        for (const candidate of projections(formula)) yield { ...candidate, direction: 0, premise: undefined as Formula | undefined };
        if (formula.tag === "iff") {
          for (const candidate of projections(formula.right)) yield { ...candidate, direction: 1, premise: formula.left };
          for (const candidate of projections(formula.left)) yield { ...candidate, direction: -1, premise: formula.right };
        }
      }
      while (true) {
        for (const candidate of alternatives(schema)) {
          if (state.remaining <= 0) { report("work"); return undefined; }
          state.remaining -= 1;
          const matched = new Map<string, Term>();
          if (!matchFormula(candidate.formula, wanted, variableSet, matched)) continue;
          for (const substitution of bindings(matched, candidate.premise ? [...conditions, candidate.premise] : conditions)) {
            let proof = at(rule, ...variables.map(variable => substitution.get(variable)!));
            let conclusion = kernel.checkProof(proof, context);
            let failed = false;
            for (let i = 0; i < hypothesisCount; i += 1) {
              if (conclusion.tag !== "imp") { failed = true; break; }
              const cap = state.policy.hypothesisDepths?.get(rule)?.[i];
              const childCeiling = cap === undefined ? ceiling : Math.min(ceiling, depth + 1 + cap);
              const evidence = relieveHypothesis(kernel, conclusion.left, rules, context, facts, state, depth + 1, childCeiling);
              if (!evidence) { failed = true; break; }
              proof = impElim(proof, evidence);
              conclusion = kernel.checkProof(proof, context);
            }
            if (failed) continue;
            if (candidate.direction !== 0) {
              if (conclusion.tag !== "iff") continue;
              const premise = candidate.direction === 1 ? conclusion.left : conclusion.right;
              const cap = state.policy.hypothesisDepths?.get(rule)?.[hypothesisCount];
              const childCeiling = cap === undefined ? ceiling : Math.min(ceiling, depth + 1 + cap);
              const evidence = relieveHypothesis(kernel, premise, rules, context, facts, state, depth + 1, childCeiling);
              if (!evidence) continue;
              proof = impElim(candidate.direction === 1 ? iffElimLeft(proof) : iffElimRight(proof), evidence);
            }
            for (const right of candidate.path) proof = right ? andElimRight(proof) : andElimLeft(proof);
            if (formulaEquals(kernel.checkProof(proof, context), wanted)) {
              report("rule", formulaCanonical(kernel.checkProof(rule, context)));
              return proof;
            }
          }
        }
        if (schema.tag !== "imp") break;
        conditions.push(schema.left);
        schema = schema.right;
        hypothesisCount += 1;
      }
    }
    report("unproved");
    return undefined;
  } finally { state.active.delete(key); }
}

export interface SettleStats {
  rules: number;
  termsVisited: number;
  candidatesConsidered: number;
  rewrites: number;
}

interface AvailableFact {
  readonly formula: Formula;
  readonly proof: Proof;
}

class SettleSearchLimit extends Error {}

/** An equation without variables that mentions a numeral under a function. */
export function closedNumeralEquation(formula: Extract<Formula, { tag: "eq" }>): boolean {
  if (freeFormulaVariables(formula).size) return false;
  const literalUnderFunction = (term: Term): boolean =>
    term.tag === "app" && term.args.some(item => item.tag === "nat" || literalUnderFunction(item));
  return literalUnderFunction(formula.left) || literalUnderFunction(formula.right);
}

function preserveSettleSearchLimit(error: unknown): void {
  if (error instanceof SettleSearchLimit) throw error;
}

export interface PreparedRewrites {
  readonly tag: "prepared-rewrites";
  readonly rules: readonly RewriteRule[];
  readonly byRoot: ReadonlyMap<string, readonly RewriteRule[]>;
}

export interface GoalRewrite {
  readonly goal: Formula;
  /** Turn a proof of the rewritten goal into a proof of the original goal. */
  readonly lift: (proof: Proof) => Proof;
}

export interface SimplifiedFact {
  readonly formula: Formula;
  readonly proof: Proof;
}

/**
 * A rewrite whose rule selects nothing in its target. The rule is the
 * equality or equivalence beneath the rule's quantifiers and premises,
 * oriented as the rewrite read it; the target is the goal or the fact.
 */
export class RewriteMismatch extends Error {
  readonly rule: Formula;
  readonly target: Formula;

  constructor(rule: Formula, target: Formula) {
    super(`rewrite rule ${formatFormula(rule)} does not match ${formatFormula(target)}`);
    this.rule = rule;
    this.target = target;
    this.name = "RewriteMismatch";
  }
}

/** The equality or equivalence a rule rewrites with, in the direction read. */
function orientedRule(schema: Formula, reverse: boolean): Formula {
  if (!reverse || (schema.tag !== "eq" && schema.tag !== "iff")) return schema;
  return { tag: schema.tag, left: schema.right, right: schema.left };
}

/** The subformulas a propositional rewrite may select, outermost first. */
function formulaCandidates(formula: Formula, underBinders: boolean): Formula[] {
  const result: Formula[] = [];
  const visit = (item: Formula): void => {
    result.push(item);
    switch (item.tag) {
      case "imp": case "and": case "or": case "iff": visit(item.left); visit(item.right); return;
      case "forall": case "exists": if (underBinders) visit(item.body); return;
      default: return;
    }
  };
  visit(formula);
  return result;
}

/**
 * Transport along an equivalence: given `source ↔ target`, the formula with
 * every occurrence of `source` replaced by `target`, and the implications
 * each way, built from the introduction and elimination rules of the
 * connectives on the path. A quantifier is crossed only on request and only
 * when neither side mentions its variable. Undefined when nothing changes.
 */
function transportEquivalence(
  formula: Formula, source: Formula, target: Formula, equivalence: Proof, underBinders: boolean,
): { readonly formula: Formula; readonly forward: Proof; readonly backward: Proof } | undefined {
  const identity = (item: Formula): Proof => impIntro(item, assume(item));
  const transport = (item: Formula): { formula: Formula; forward: Proof; backward: Proof } => {
    if (formulaEquals(item, source)) return { formula: target, forward: iffElimLeft(equivalence), backward: iffElimRight(equivalence) };
    switch (item.tag) {
      case "bottom": case "eq": case "pred": return { formula: item, forward: identity(item), backward: identity(item) };
      case "and": case "or": case "imp": case "iff": {
        const left = transport(item.left);
        const right = transport(item.right);
        const rewritten: Formula = { tag: item.tag, left: left.formula, right: right.formula };
        if (formulaEquals(rewritten, item)) return { formula: item, forward: identity(item), backward: identity(item) };
        // Each direction is the same construction with the roles of the two
        // formulas exchanged.
        const direction = (from: Formula, to: Formula, l: Proof, r: Proof, lBack: Proof, rBack: Proof): Proof => {
          const h = assume(from);
          switch (item.tag) {
            case "and": return impIntro(from, andIntro(impElim(l, andElimLeft(h)), impElim(r, andElimRight(h))));
            case "or": {
              const toLeft = (to as Extract<Formula, { tag: "or" }>).left;
              const toRight = (to as Extract<Formula, { tag: "or" }>).right;
              const fromLeft = (from as Extract<Formula, { tag: "or" }>).left;
              const fromRight = (from as Extract<Formula, { tag: "or" }>).right;
              return impIntro(from, orElim(h, orIntroLeft(impElim(l, assume(fromLeft)), toRight),
                orIntroRight(toLeft, impElim(r, assume(fromRight)))));
            }
            case "imp": {
              const toLeft = (to as Extract<Formula, { tag: "imp" }>).left;
              return impIntro(from, impIntro(toLeft, impElim(r, impElim(h, impElim(lBack, assume(toLeft))))));
            }
            default: {
              const toLeft = (to as Extract<Formula, { tag: "iff" }>).left;
              const toRight = (to as Extract<Formula, { tag: "iff" }>).right;
              return impIntro(from, iffIntro(
                impIntro(toLeft, impElim(r, impElim(iffElimLeft(h), impElim(lBack, assume(toLeft))))),
                impIntro(toRight, impElim(l, impElim(iffElimRight(h), impElim(rBack, assume(toRight)))))));
            }
          }
        };
        return {
          formula: rewritten,
          forward: direction(item, rewritten, left.forward, right.forward, left.backward, right.backward),
          backward: direction(rewritten, item, left.backward, right.backward, left.forward, right.forward),
        };
      }
      case "forall": case "exists": {
        if (!underBinders || freeFormulaVariables(source).has(item.variable) || freeFormulaVariables(target).has(item.variable)) {
          return { formula: item, forward: identity(item), backward: identity(item) };
        }
        const body = transport(item.body);
        if (formulaEquals(body.formula, item.body)) return { formula: item, forward: identity(item), backward: identity(item) };
        const rewritten: Formula = { ...item, body: body.formula };
        const x = v(item.variable);
        if (item.tag === "forall") {
          return {
            formula: rewritten,
            forward: impIntro(item, forallIntro(item.variable, impElim(body.forward, forallElim(assume(item), x)))),
            backward: impIntro(rewritten, forallIntro(item.variable, impElim(body.backward, forallElim(assume(rewritten), x)))),
          };
        }
        return {
          formula: rewritten,
          forward: impIntro(item, existsElim(assume(item), item.variable,
            existsIntro(item.variable, body.formula, x, impElim(body.forward, assume(item.body))))),
          backward: impIntro(rewritten, existsElim(assume(rewritten), item.variable,
            existsIntro(item.variable, item.body, x, impElim(body.backward, assume(body.formula))))),
        };
      }
    }
  };
  const result = transport(formula);
  return formulaEquals(result.formula, formula) ? undefined : result;
}

/**
 * Instantiate a rule at a match and discharge its premises; undefined when a
 * premise has no evidence. The result is the checked equality or
 * equivalence beneath the premises.
 */
function instantiateRule(
  kernel: Kernel, ruleProof: Proof, variables: readonly string[], substitution: ReadonlyMap<string, Term>,
  conditions: readonly Formula[], assumptions: readonly Formula[], facts: readonly Proof[],
  relief: { rules: readonly Proof[]; state: ReliefState } | undefined, visibility: ScopeVisibility | undefined,
): { readonly proof: Proof; readonly formula: Formula } | undefined {
  let proof = at(ruleProof, ...variables.map(name => substitution.get(name)!));
  let checked = kernel.checkProof(proof, assumptions);
  for (const _condition of conditions) {
    if (checked.tag !== "imp") return undefined;
    const evidence = relieveHypothesis(kernel, checked.left, relief?.rules ?? [], assumptions, facts,
      relief?.state ?? { policy: false, remaining: 0, active: new Set(), visibility });
    if (!evidence) return undefined;
    proof = impElim(proof, evidence);
    checked = kernel.checkProof(proof, assumptions);
  }
  return { proof, formula: checked };
}

/**
 * Rewrite a formula with an equivalence rule: the first subformula the
 * rule's selected side matches is replaced, at every occurrence, by the
 * other side. The result carries the implications each way between the
 * formula and its rewrite, checked here so that a blocked binder is
 * reported at the rewrite and not when the proof closes.
 */
function rewriteWithEquivalence(
  kernel: Kernel, formula: Formula, ruleProof: Proof, schema: Extract<Formula, { tag: "iff" }>,
  variables: readonly string[], conditions: readonly Formula[], assumptions: readonly Formula[],
  facts: readonly Proof[], reverse: boolean, underBinders: boolean,
  relief: { rules: readonly Proof[]; state: ReliefState } | undefined, visibility: ScopeVisibility | undefined,
): { readonly formula: Formula; readonly forward: Proof; readonly backward: Proof } {
  const pattern = reverse ? schema.right : schema.left;
  const variableSet = new Set(variables);
  for (const candidate of formulaCandidates(formula, underBinders)) {
    const substitution = new Map<string, Term>();
    if (!matchFormula(pattern, candidate, variableSet, substitution) || variables.some(name => !substitution.has(name))) continue;
    const instantiated = instantiateRule(kernel, ruleProof, variables, substitution, conditions, assumptions, facts, relief, visibility);
    if (!instantiated || instantiated.formula.tag !== "iff") continue;
    const equivalence = reverse ? iffIntro(iffElimRight(instantiated.proof), iffElimLeft(instantiated.proof)) : instantiated.proof;
    const source = reverse ? instantiated.formula.right : instantiated.formula.left;
    const target = reverse ? instantiated.formula.left : instantiated.formula.right;
    const transported = transportEquivalence(formula, source, target, equivalence, underBinders);
    if (!transported) continue;
    const forward = kernel.checkProof(transported.forward, assumptions);
    const backward = kernel.checkProof(transported.backward, assumptions);
    if (forward.tag !== "imp" || !formulaEquals(forward.left, formula) || !formulaEquals(forward.right, transported.formula) ||
        backward.tag !== "imp" || !formulaEquals(backward.left, transported.formula) || !formulaEquals(backward.right, formula)) {
      throw new Error("equivalence rewrite produced the wrong implications");
    }
    return transported;
  }
  throw new RewriteMismatch(orientedRule(schema, reverse), formula);
}

/**
 * Forward-simplify an arbitrary proved formula.  Every step is either
 * equality elimination or one direction of a checked equivalence; the
 * returned proof is therefore suitable for immediate kernel replay.
 */
export function simplifyFormulaFact(
  kernel: Kernel,
  factProof: Proof,
  options: SimpOptions,
): SimplifiedFact {
  let proof = factProof;
  let formula = kernel.checkProof(proof, options.assumptions ?? []);
  const assumptions = options.assumptions ?? [];
  const facts = options.facts ?? [];
  if (!Array.isArray(options.using)) throw new Error("formula simp needs its explicit rule proofs");
  const rules = options.using;
  const relief = { rules, state: reliefState(options) };
  const seen = new Set<string>();
  const fuel = options.fuel ?? 256;
  for (let step = 0; step < fuel; step += 1) {
    const key = formulaCanonical(formula);
    if (seen.has(key)) break;
    seen.add(key);
    let changed = false;
    for (const ruleProof of rules) {
      let schema = kernel.checkProof(ruleProof, assumptions);
      const variables: string[] = [];
      while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
      if (schema.tag === "iff") {
        const substitution = new Map<string, Term>();
        if (!matchFormula(schema.left, formula, new Set(variables), substitution) ||
            variables.some(variable => !substitution.has(variable))) continue;
        const instantiated = at(ruleProof, ...variables.map(variable => substitution.get(variable)!));
        const equivalence = kernel.checkProof(instantiated, assumptions);
        if (equivalence.tag !== "iff" || !formulaEquals(equivalence.left, formula)) continue;
        proof = impElim(iffElimLeft(instantiated), proof);
        formula = equivalence.right;
        changed = true;
        break;
      }
      if (schema.tag === "eq" || schema.tag === "imp") {
        try {
          const rewritten = rewriteFact(kernel, proof, ruleProof, assumptions, facts, false, options.underBinders ?? false, relief);
          proof = rewritten.proof;
          formula = rewritten.formula;
          changed = true;
          break;
        } catch {}
      }
    }
    if (!changed) break;
  }
  return { formula, proof };
}

/** Rewrite a proved formula and retain evidence for the transformed fact. */
export function rewriteFact(
  kernel: Kernel,
  factProof: Proof,
  ruleProof: Proof,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  reverse = false,
  underBinders = false,
  relief?: { rules: readonly Proof[]; state: ReliefState },
  visibility: ScopeVisibility | undefined = relief?.state.visibility,
): SimplifiedFact {
  const original = kernel.checkProof(factProof, assumptions);
  let schema = kernel.checkProof(ruleProof, assumptions);
  const variables: string[] = [];
  while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
  const conditions: Formula[] = [];
  while (schema.tag === "imp") { conditions.push(schema.left); schema = schema.right; }
  // An equivalence rule rewrites a subformula of the fact.
  if (schema.tag === "iff") {
    const transported = rewriteWithEquivalence(kernel, original, ruleProof, schema, variables, conditions,
      assumptions, facts, reverse, underBinders, relief, visibility);
    return { formula: transported.formula, proof: impElim(transported.forward, factProof) };
  }
  if (schema.tag !== "eq") throw new Error(`rewrite needs an equality or an equivalence, under ∀ and premises; the rule states ${formatFormula(schema)}`);
  const pattern = reverse ? schema.right : schema.left;
  for (const candidate of rewriteCandidates(original, underBinders)) {
    const substitution = new Map<string, Term>();
    if (!match(pattern, candidate, new Set(variables), substitution) || variables.some(name => !substitution.has(name))) continue;
    const instantiated = instantiateRule(kernel, ruleProof, variables, substitution, conditions, assumptions, facts, relief, visibility);
    if (!instantiated || instantiated.formula.tag !== "eq") continue;
    const equality = instantiated.proof;
    const checked = instantiated.formula;
    const source = reverse ? checked.right : checked.left;
    const target = reverse ? checked.left : checked.right;
    let variable = "__rewrite";
    const forbidden = new Set([...freeFormulaVariables(original), ...boundFormulaVariables(original),
      ...freeTermVariables(source), ...freeTermVariables(target)]);
    while (forbidden.has(variable)) variable += "_";
    const motive = replaceFormulaTerm(original, source, v(variable), underBinders);
    const formula = replaceFormulaTerm(original, source, target, underBinders);
    if (formulaEquals(formula, original)) continue;
    const proof = eqElim(equality, variable, motive, factProof, reverse);
    if (!formulaEquals(kernel.checkProof(proof, assumptions), formula)) throw new Error("rewrite at produced the wrong fact");
    return { formula, proof };
  }
  throw new RewriteMismatch(orientedRule(schema, reverse), original);
}

interface RewriteRule {
  readonly variables: readonly string[];
  readonly conditions: readonly Formula[];
  readonly left: Term;
  readonly right: Term;
  readonly proof: Proof;
  readonly ordered: boolean;
}

/**
 * Close an equality by normalization. `settle` is untrusted: it
 * constructs a primitive equality proof and asks the kernel to check it before
 * returning. Rules are used only left-to-right and must themselves check.
 */
export function settle(kernel: Kernel, goal: Formula, options: SimpOptions): Proof {
  const assumptions = options.assumptions ?? [];
  if (goal.tag !== "eq") {
    if (!Array.isArray(options.using)) throw new Error("logical settle needs its explicit rule proofs");
    const result = settleLogical(kernel, goal, options.using, assumptions, options.facts ?? [], options.fuel ?? 1_000, options.backchain === undefined ? undefined : reliefState(options), options.ground, options.visibility);
    const checked = kernel.checkProof(result, assumptions);
    if (!formulaEquals(checked, goal)) throw new Error("settle produced a proof of the wrong logical goal");
    return result;
  }
  const logicalRules = Array.isArray(options.using) ? options.using : [];
  const assumptionFacts = expandFacts(kernel, assumptions.map(formula => ({ formula, proof: assume(formula) })), options.visibility);
  const suppliedFacts = expandFacts(kernel, (options.facts ?? []).map(proof => ({
    formula: kernel.checkProof(proof, assumptions), proof,
  })), options.visibility);
  const facts: AvailableFact[] = [...assumptionFacts, ...suppliedFacts];
  // A fact equating distinct literals refutes the goal outright.
  const refuted = refuteLiteralEquation(kernel, facts);
  if (refuted) {
    const result = falseElim(goal, refuted);
    if (!formulaEquals(kernel.checkProof(result, assumptions), goal)) throw new Error("settle produced a proof of the wrong goal");
    return result;
  }
  const explicitRewrites = Array.isArray(options.using)
    ? indexRules(options.using.flatMap(proof => {
        const rule = compileRule(kernel, proof, assumptions, false);
        return rule ? [rule] : [];
      }))
    : options.using;
  const localRewriteFacts = options.useContextEqualities === false ? suppliedFacts : facts;
  const localRewrites = localRewriteFacts.flatMap(fact => fact.formula.tag === "eq" &&
    !termEquals(fact.formula.left, fact.formula.right)
    ? [compileContextRule(kernel, fact.proof, assumptions)]
    : []);
  const rewrites = localRewrites.length === 0
    ? explicitRewrites
    : indexRules([...explicitRewrites.rules, ...localRewrites]);
  const stats = options.stats;
  if (stats) {
    stats.rules = rewrites.rules.length;
    stats.termsVisited = 0;
    stats.candidatesConsidered = 0;
    stats.rewrites = 0;
  }
  const budget = { remaining: options.fuel ?? 10_000 };
  const refinements = prepareRefinementProver(kernel, assumptions, options.facts ?? [], options.visibility);
  const factIndex = indexFacts(facts);
  const relief = reliefState(options);
  const relieve = (goal: Formula): Proof | undefined => {
    const doubleNegative = factIndex.get(formulaCanonical(not(not(goal))));
    if (doubleNegative) return dne(goal, doubleNegative);
    return relief.policy ? relieveHypothesis(
      kernel, goal, logicalRules, assumptions, facts.map(fact => fact.proof), relief) : undefined;
  };
  const left = normalize(kernel, goal.left, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, stats);
  const right = normalize(kernel, goal.right, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, stats);
  if (!termEquals(left.value, right.value)) {
    throw new Error(`settle did not close this goal; rewriting leaves ${formatTerm(left.value)} ≠ ${formatTerm(right.value)}`);
  }
  const result = calc(left.proof, symm(right.proof));
  const checked = kernel.checkProof(result, assumptions);
  if (!formulaEquals(checked, goal)) throw new Error("settle produced a proof of the wrong goal");
  return result;
}

/** Normalize both sides of an equality while retaining a proof back to it. */
export function simplifyEqualityGoal(kernel: Kernel, goal: Formula, options: SimpOptions): GoalRewrite {
  if (goal.tag !== "eq") throw new Error("simp currently transforms equality goals; introduce logical structure first");
  const assumptions = options.assumptions ?? [];
  const logicalRules = Array.isArray(options.using) ? options.using : [];
  const facts: AvailableFact[] = expandFacts(kernel, [
    ...assumptions.map(formula => ({ formula, proof: assume(formula) })),
    ...(options.facts ?? []).map(proof => ({ formula: kernel.checkProof(proof, assumptions), proof })),
  ], options.visibility);
  const explicit = Array.isArray(options.using)
    ? indexRules(options.using.flatMap(proof => {
        const rule = compileRule(kernel, proof, assumptions, false);
        return rule ? [rule] : [];
      }))
    : options.using;
  const locals = facts.flatMap(fact => fact.formula.tag === "eq" ? [compileContextRule(kernel, fact.proof, assumptions)] : []);
  const rewrites = locals.length === 0 ? explicit : indexRules([...explicit.rules, ...locals]);
  const budget = { remaining: options.fuel ?? 10_000 };
  const refinements = prepareRefinementProver(kernel, assumptions, options.facts ?? [], options.visibility);
  const factIndex = indexFacts(facts);
  const relief = reliefState(options);
  const relieve = (goal: Formula): Proof | undefined => {
    const doubleNegative = factIndex.get(formulaCanonical(not(not(goal))));
    if (doubleNegative) return dne(goal, doubleNegative);
    return relief.policy ? relieveHypothesis(
      kernel, goal, logicalRules, assumptions, facts.map(fact => fact.proof), relief) : undefined;
  };
  const left = normalize(kernel, goal.left, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, options.stats);
  const right = normalize(kernel, goal.right, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, options.stats);
  return {
    goal: { tag: "eq", left: left.value, right: right.value },
    lift: proof => calc(left.proof, proof, symm(right.proof)),
  };
}

/**
 * Simplify the outer proposition of a goal with a checked equivalence.
 *
 * This is the non-closing half of `simp`: if bounded logical search cannot
 * finish a proposition, an applicable `P ↔ Q` rule may still replace the
 * focused goal P by Q.  The continuation records Q → P, so the
 * eventual proof remains a kernel-checked natural-deduction term.
 */
export function simplifyFormulaGoal(kernel: Kernel, goal: Formula, options: SimpOptions): GoalRewrite {
  const assumptions = options.assumptions ?? [];
  if (!Array.isArray(options.using)) throw new Error("formula goal simp needs its explicit rule proofs");
  const relief = { rules: options.using, state: reliefState(options) };
  for (const ruleProof of options.using) {
    let schema = kernel.checkProof(ruleProof, assumptions);
    const variables: string[] = [];
    while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
    if (schema.tag !== "iff") continue;
    const substitution = new Map<string, Term>();
    if (!matchFormula(schema.left, goal, new Set(variables), substitution) ||
        variables.some(variable => !substitution.has(variable))) continue;
    const instantiated = at(ruleProof, ...variables.map(variable => substitution.get(variable)!));
    const equivalence = kernel.checkProof(instantiated, assumptions);
    if (equivalence.tag !== "iff" || !formulaEquals(equivalence.left, goal)) continue;
    return {
      goal: equivalence.right,
      lift: proof => impElim(iffElimRight(instantiated), proof),
    };
  }
  // A logical goal need not close after term simplification. Reuse checked
  // equality transport under connectives (including negation), leaving an
  // explicit residual goal. This fallback performs one productive rewrite;
  // it neither splits cases nor recursively launches logical search.
  // The rewrite repeats on the residual goal, to a bounded fixed point, so
  // nested projections `fst(fst(p))` are reduced through every layer.
  let residual: GoalRewrite | undefined;
  // Opposing rules would cycle; a goal seen before ends the repetition at
  // the step before it, so one productive step is always kept.
  const seen: Formula[] = [goal];
  for (let round = 0; round < 64; round += 1) {
    let step: GoalRewrite | undefined;
    for (const ruleProof of options.using) {
      try {
        step = rewriteGoal(kernel, residual?.goal ?? goal, ruleProof, assumptions, options.facts ?? [], false, options.underBinders ?? false, relief);
        break;
      } catch (error) { preserveSettleSearchLimit(error); }
    }
    if (!step || seen.some(earlier => formulaEquals(step!.goal, earlier))) break;
    seen.push(step.goal);
    const previous = residual;
    const current = step;
    residual = { goal: current.goal, lift: proof => previous ? previous.lift(current.lift(proof)) : current.lift(proof) };
  }
  if (residual) return residual;
  if (goal.tag === "or") {
    const literals: Formula[] = [];
    const flatten = (formula: Formula): void => {
      if (formula.tag === "or") { flatten(formula.left); flatten(formula.right); }
      else literals.push(formula);
    };
    flatten(goal);
    const inject = (tree: Formula, index: number, evidence: Proof): Proof => {
      if (tree.tag !== "or") return evidence;
      const count = (f: Formula): number => f.tag === "or" ? count(f.left) + count(f.right) : 1;
      const leftCount = count(tree.left);
      return index < leftCount ? orIntroLeft(inject(tree.left, index, evidence), tree.right)
        : orIntroRight(tree.left, inject(tree.right, index - leftCount, evidence));
    };
    for (let selected = 0; selected < literals.length; selected += 1) {
      const temporary = literals.flatMap((literal, index) => index === selected ? [] : [not(literal)]);
      const context = [...assumptions, ...temporary];
      for (const rule of options.using) {
        let rewritten: GoalRewrite;
        try {
          rewritten = rewriteGoal(kernel, literals[selected]!, rule, context,
            options.facts ?? [], false, false, relief);
        } catch (error) { preserveSettleSearchLimit(error); continue; }
        let cursor = 0;
        const replace = (tree: Formula): Formula => tree.tag === "or"
          ? or(replace(tree.left), replace(tree.right))
          : cursor++ === selected ? rewritten.goal : tree;
        const residual = replace(goal);
        return {
          goal: residual,
          lift: evidence => {
            // Under ¬C, every sibling literal is false. Discharge each scoped
            // assumption by implication introduction/application before DNE.
            const denial = not(goal);
            const negations = literals.flatMap((literal, index) => index === selected ? [] : [
              impIntro(literal, impElim(assume(denial), inject(goal, index, assume(literal)))),
            ]);
            let position = 0;
            const eliminate = (tree: Formula, proof: Proof): Proof => {
              if (tree.tag === "or") return orElim(proof,
                eliminate(tree.left, assume(tree.left)), eliminate(tree.right, assume(tree.right)));
              const index = position++;
              let original = index === selected ? rewritten.lift(proof) : proof;
              if (index === selected) for (let i = 0; i < temporary.length; i += 1)
                original = impElim(impIntro(temporary[i]!, original), negations[i]!);
              return inject(goal, index, original);
            };
            return dne(goal, impIntro(denial, impElim(assume(denial), eliminate(residual, evidence))));
          },
        };
      }
    }
  }
  throw new Error(`simp did not simplify the logical goal ${formatFormula(goal)}`);
}

/** Normalize a proved equality and retain a proof of its normalized form. */
export function simplifyEqualityFact(kernel: Kernel, proof: Proof, options: SimpOptions): SimplifiedFact {
  const assumptions = options.assumptions ?? [];
  const original = kernel.checkProof(proof, assumptions);
  if (original.tag !== "eq") throw new Error("simp at currently requires an equality hypothesis");
  const logicalRules = Array.isArray(options.using) ? options.using : [];
  // A context fact whose proof is still being discharged, such as a
  // destructured witness, does not check on its own and is left out.
  const facts: AvailableFact[] = expandFacts(kernel, [
    ...assumptions.map(formula => ({ formula, proof: assume(formula) })),
    ...(options.facts ?? []).flatMap(item => {
      try { return [{ formula: kernel.checkProof(item, assumptions), proof: item }]; } catch { return []; }
    }),
  ], options.visibility);
  const explicit = Array.isArray(options.using)
    ? indexRules(options.using.flatMap(item => {
        const rule = compileRule(kernel, item, assumptions, false);
        return rule ? [rule] : [];
      }))
    : options.using;
  const locals = facts.flatMap(fact => fact.formula.tag === "eq" ? [compileContextRule(kernel, fact.proof, assumptions)] : []);
  const rewrites = locals.length === 0 ? explicit : indexRules([...explicit.rules, ...locals]);
  const budget = { remaining: options.fuel ?? 10_000 };
  const refinements = prepareRefinementProver(kernel, assumptions, options.facts ?? [], options.visibility);
  const factIndex = indexFacts(facts);
  const relief = reliefState(options);
  const relieve = (goal: Formula): Proof | undefined => {
    const doubleNegative = factIndex.get(formulaCanonical(not(not(goal))));
    if (doubleNegative) return dne(goal, doubleNegative);
    return relief.policy ? relieveHypothesis(
      kernel, goal, logicalRules, assumptions, facts.map(fact => fact.proof), relief) : undefined;
  };
  const left = normalize(kernel, original.left, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, options.stats);
  const right = normalize(kernel, original.right, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, options.stats);
  const formula = { tag: "eq", left: left.value, right: right.value } as const;
  const simplified = calc(symm(left.proof), proof, right.proof);
  if (!formulaEquals(kernel.checkProof(simplified, assumptions), formula)) throw new Error("simp at produced the wrong fact");
  return { formula, proof: simplified };
}

/** Rewrite every occurrence selected by one checked equality rule. */
export function rewriteGoal(
  kernel: Kernel,
  goal: Formula,
  ruleProof: Proof,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  reverse = false,
  underBinders = false,
  relief?: { rules: readonly Proof[]; state: ReliefState },
  visibility: ScopeVisibility | undefined = relief?.state.visibility,
): GoalRewrite {
  let schema = kernel.checkProof(ruleProof, assumptions);
  const variables: string[] = [];
  while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
  const conditions: Formula[] = [];
  while (schema.tag === "imp") { conditions.push(schema.left); schema = schema.right; }
  // An equivalence rule rewrites a subformula of the goal; the proof of the
  // rewritten goal is carried back through the implication.
  if (schema.tag === "iff") {
    const transported = rewriteWithEquivalence(kernel, goal, ruleProof, schema, variables, conditions,
      assumptions, facts, reverse, underBinders, relief, visibility);
    return { goal: transported.formula, lift: proof => impElim(transported.backward, proof) };
  }
  if (schema.tag !== "eq") throw new Error(`rewrite needs an equality or an equivalence, under ∀ and premises; the rule states ${formatFormula(schema)}`);
  const pattern = reverse ? schema.right : schema.left;
  const candidates = rewriteCandidates(goal, underBinders);
  const variableSet = new Set(variables);
  const available = conditions.length && variables.length ? expandFacts(kernel, [
    ...assumptions.map(formula => ({ formula, proof: assume(formula) })),
    ...facts.map(proof => ({ formula: kernel.checkProof(proof, assumptions), proof })),
  ], visibility) : [];
  // A prover for completing open condition arguments, prepared only when a
  // condition needs it; a local fact that does not check in this context
  // merely withholds that completion.
  let refinements: RefinementProver | undefined;
  const prover = (): RefinementProver | undefined => {
    try { return refinements ??= prepareRefinementProver(kernel, assumptions, facts, visibility); } catch { return undefined; }
  };
  for (const candidate of candidates) {
    const matched = new Map<string, Term>();
    if (!match(pattern, candidate, variableSet, matched)) continue;
    // A variable the pattern leaves unbound is bound by matching a condition
    // against a local fact, as the middle object of an associativity law is.
    for (const substitution of bindConditionVariables(variables, conditions, matched, variableSet, available, prover)) {
      let equality = at(ruleProof, ...variables.map(name => substitution.get(name)!));
      let checked = kernel.checkProof(equality, assumptions);
      let failed = false;
      for (const condition of conditions) {
        if (checked.tag !== "imp") { failed = true; break; }
        const evidence = relieveHypothesis(kernel, checked.left, relief?.rules ?? [], assumptions, facts,
          relief?.state ?? { policy: false, remaining: 0, active: new Set(), visibility });
        if (!evidence) { failed = true; break; }
        equality = impElim(equality, evidence);
        checked = kernel.checkProof(equality, assumptions);
      }
      if (failed || checked.tag !== "eq") continue;
      const source = reverse ? checked.right : checked.left;
      const target = reverse ? checked.left : checked.right;
      let variable = "__rewrite";
      const forbidden = new Set([...freeFormulaVariables(goal), ...boundFormulaVariables(goal),
        ...freeTermVariables(source), ...freeTermVariables(target)]);
      while (forbidden.has(variable)) variable += "_";
      const motive = replaceFormulaTerm(goal, source, v(variable), underBinders);
      const rewritten = replaceFormulaTerm(goal, source, target, underBinders);
      if (formulaEquals(rewritten, goal)) continue;
      return {
        goal: rewritten,
        lift: proof => eqElim(equality, variable, motive, proof, !reverse),
      };
    }
  }
  throw new RewriteMismatch(orientedRule(schema, reverse), goal);
}

function settleLogical(
  kernel: Kernel,
  goal: Formula,
  rules: readonly Proof[],
  assumptions: readonly Formula[],
  extraFacts: readonly Proof[],
  fuel: number,
  relief?: ReliefState,
  ground?: readonly Proof[],
  visibility: ScopeVisibility | undefined = relief?.visibility,
): Proof {
  // Ground classical reasoning with equality and instantiated lemmas is
  // tried at a bounded number of quantifier-free goals before the structural
  // search; a failure costs its fuel and nothing else.
  const groundState = { attempts: 0 };
  const tryGround = (wanted: Formula, context: readonly Formula[], facts: readonly Proof[]): Proof | undefined => {
    if (!ground || groundState.attempts >= 8 || wanted.tag === "forall" || wanted.tag === "exists") return undefined;
    groundState.attempts += 1;
    try { return proveGround(kernel, wanted, context, facts, { rules: [...rules, ...ground] }); }
    catch (error) {
      if ((globalThis as { process?: { env?: Record<string, string | undefined> } }).process?.env?.G17_GROUND_DEBUG) {
        console.error(`ground: ${formatFormula(wanted)} :: ${error instanceof Error ? error.message : String(error)}`);
      }
      // The ground attempt is optional: any failure, including a kernel
      // rejection of an instantiation, leaves the structural search intact.
      return undefined;
    }
  };
  const profile = (globalThis as typeof globalThis & {
    process?: { env?: Record<string, string | undefined> };
  }).process?.env?.GRACE_PROFILE_SETTLE === "1";
  const started = globalThis.performance?.now();
  let congruenceMilliseconds = 0;
  const seedFacts: AvailableFact[] = expandFacts(kernel, [
    ...assumptions.map(formula => ({ formula, proof: assume(formula) })),
    ...extraFacts.map(proof => ({ formula: kernel.checkProof(proof, assumptions), proof })),
  ], visibility);
  // Equality-heavy goals are common after unpacking structured witnesses.
  // Ground congruence closure is deterministic and near-linear here; run it
  // before branching logical search so a handful of coordinate equalities can
  // never trigger exponential case/existential exploration.
  if (goal.tag === "eq" || goal.tag === "pred") {
    const congruenceStarted = globalThis.performance?.now();
    try { return proveCongruence(kernel, goal, assumptions, extraFacts); }
    catch (error) {
      if (!(error instanceof Error) || !error.message.includes("cc found no congruence")) throw error;
    } finally {
      if (congruenceStarted !== undefined) congruenceMilliseconds = globalThis.performance.now() - congruenceStarted;
    }
  }
  const forwardStarted = globalThis.performance?.now();
  const facts = forwardRuleFacts(kernel, seedFacts, rules, assumptions);
  const forwardMilliseconds = forwardStarted === undefined ? 0 : globalThis.performance.now() - forwardStarted;
  const budget = { remaining: fuel };
  const active = new Set<string>();

  const guard = (wanted: Formula, context: readonly Formula[], available: readonly AvailableFact[]): Proof => {
    if (!relief) return solve(wanted, context, available);
    const proof = relieveHypothesis(kernel, wanted, rules, context, available.map(item => item.proof), relief);
    if (!proof) throw new Error(`unrelieved hypothesis ${formatFormula(wanted)}`);
    return proof;
  };
  const solve = (wanted: Formula, context: readonly Formula[], available: readonly AvailableFact[]): Proof => {
    if (budget.remaining-- <= 0) {
      throw new SettleSearchLimit(
        `settle stopped after ${fuel} logical search steps; use a structural tactic or give settle a smaller relevant rule set`,
      );
    }
    const direct = available.find(fact => formulaEquals(fact.formula, wanted));
    if (direct) return direct.proof;
    const absurdity = available.find(fact => fact.formula.tag === "bottom");
    if (absurdity) return falseElim(wanted, absurdity.proof);
    // Distinct natural literals are distinct: `2 ≠ 5` closes, and a fact
    // `2 = 5` refutes any goal, in every module.
    const literals = proveLiteralDistinctnessGoal(kernel, wanted);
    if (literals) return literals;
    const refuted = refuteLiteralEquation(kernel, available);
    if (refuted) return wanted.tag === "bottom" ? refuted : falseElim(wanted, refuted);
    if (wanted.tag === "eq" && termCanonical(wanted.left) === termCanonical(wanted.right)) return refl(wanted.left);
    // A closed equation between numeral expressions is evaluated, so
    // `1 + 1 = 2` closes by computation inside a logical goal.
    if (wanted.tag === "eq" && closedNumeralEquation(wanted)) {
      try { return kernel.proveComputation(wanted.left, wanted.right); } catch {}
    }
    const grounded = tryGround(wanted, context, available.map(fact => fact.proof));
    if (grounded) return grounded;
    // Total fuel alone permits a long branch to retain quadratic context/key
    // data. Bound retained search depth before allocating the next state key.
    if (active.size >= 64) throw new SettleSearchLimit(
      "settle stopped at 64 nested logical search steps; use a structural tactic or simplify the goal first",
    );
    const key = JSON.stringify([formulaCanonical(wanted), context.map(formulaCanonical),
      available.map(fact => formulaCanonical(fact.formula))]);
    if (active.has(key)) throw new Error("cyclic logical rewrite");
    active.add(key);
    try {
    // Treat local universally quantified implications as goal-directed rules.
    // Unlike eager pairwise saturation, this stays linear in the local context
    // and only instantiates a fact when its conclusion matches the goal.
    for (const fact of available) {
      let schema = fact.formula;
      const variables: string[] = [];
      while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
      const conditions: Formula[] = [];
      while (schema.tag === "imp") { conditions.push(schema.left); schema = schema.right; }
      if (conditions.length === 0) continue;
      const substitution = new Map<string, Term>();
      if (!matchFormula(schema, wanted, new Set(variables), substitution)) continue;
      if (variables.some(variable => !substitution.has(variable))) continue;
      const instantiatedConditions = conditions.map(condition => substituteManyFormula(condition, substitution));
      if (instantiatedConditions.some(condition => formulaEquals(condition, wanted))) continue;
      try {
        let proof = at(fact.proof, ...variables.map(variable => substitution.get(variable)!));
        for (const condition of instantiatedConditions) proof = impElim(proof, guard(condition, context, available));
        if (formulaEquals(kernel.checkProof(proof, context), wanted)) return proof;
      } catch (error) { preserveSettleSearchLimit(error); }
    }
    // The invertible introductions come first: a conjunction, an
    // implication, and a universal are decomposed before any hypothesis is
    // split, which loses nothing and keeps the case analysis below out of
    // the goals that never needed it. The context's disjunctions are then
    // split only beneath the decomposed goal, so an unrelated hypothesis
    // `P ∨ Q` costs one split at most once rather than at every level.
    if (wanted.tag === "and") return andIntro(solve(wanted.left, context, available), solve(wanted.right, context, available));
    if (wanted.tag === "imp") {
      const fact = { formula: wanted.left, proof: assume(wanted.left) };
      const nextContext = [...context, wanted.left];
      const learned = forwardRuleFacts(kernel, expandFacts(kernel, [fact], visibility), rules, nextContext);
      return impIntro(wanted.left, solve(wanted.right, nextContext, [...available, ...learned]));
    }
    if (wanted.tag === "forall") {
      // The bound variable is renamed when it occurs free in the context,
      // as a definition's bound name may coincide with a theorem parameter.
      const taken = new Set([
        ...context.flatMap(formula => [...freeFormulaVariables(formula)]),
        ...available.flatMap(fact => [...freeFormulaVariables(fact.formula)]),
      ]);
      if (!taken.has(wanted.variable)) return forallIntro(wanted.variable, solve(wanted.body, context, available));
      let fresh = `${wanted.variable}_`;
      while (taken.has(fresh) || freeFormulaVariables(wanted.body).has(fresh)) fresh += "_";
      return forallIntro(fresh, solve(substituteFormula(wanted.body, wanted.variable, v(fresh)), context, available));
    }
    // Eliminate data-bearing hypotheses before committing to a choice.  In
    // particular, to prove P ∨ Q from R ∨ S we must split R ∨ S first;
    // greedily choosing P would incorrectly require P in both cases.
    for (let index = 0; index < available.length; index += 1) {
      const disjunction = available[index]!;
      if (disjunction.formula.tag !== "or") continue;
      const remaining = [...available.slice(0, index), ...available.slice(index + 1)];
      const leftFact = { formula: disjunction.formula.left, proof: assume(disjunction.formula.left) };
      const rightFact = { formula: disjunction.formula.right, proof: assume(disjunction.formula.right) };
      try {
        const leftContext = [...context, leftFact.formula];
        const rightContext = [...context, rightFact.formula];
        const left = solve(wanted, leftContext,
          forwardRuleFacts(kernel, [...remaining, leftFact], rules, leftContext, remaining));
        const right = solve(wanted, rightContext,
          forwardRuleFacts(kernel, [...remaining, rightFact], rules, rightContext, remaining));
        return orElim(disjunction.proof, left, right);
      } catch (error) { preserveSettleSearchLimit(error); }
    }
    for (let index = 0; index < available.length; index += 1) {
      const existential = available[index]!;
      if (existential.formula.tag !== "exists") continue;
      const forbidden = new Set([
        ...freeFormulaVariables(wanted),
        ...context.flatMap(formula => [...freeFormulaVariables(formula)]),
        ...freeFormulaVariables(existential.formula),
      ]);
      let witness = "__settleWitness";
      while (forbidden.has(witness)) witness += "_";
      const instance = substituteFormula(existential.formula.body, existential.formula.variable, v(witness));
      const remaining = [...available.slice(0, index), ...available.slice(index + 1)];
      const witnessFact = { formula: instance, proof: assume(instance) };
      const branchContext = [...context, instance];
      try {
        return existsElim(
          existential.proof,
          witness,
          solve(wanted, branchContext,
            forwardRuleFacts(kernel, [...remaining, witnessFact], rules, branchContext, remaining)),
        );
      } catch (error) { preserveSettleSearchLimit(error); }
    }
    if (wanted.tag === "or") {
      try { return orIntroLeft(solve(wanted.left, context, available), wanted.right); }
      catch (error) { preserveSettleSearchLimit(error); }
      return orIntroRight(wanted.left, solve(wanted.right, context, available));
    }
    if (wanted.tag === "exists") {
      const candidates = uniqueTerms([
        ...formulaTerms(wanted.body),
        ...available.flatMap(fact => formulaTerms(fact.formula)),
      ]).filter(term => !freeTermVariables(term).has(wanted.variable));
      for (const witness of candidates) {
        const instance = substituteFormula(wanted.body, wanted.variable, witness);
        try { return existsIntro(wanted.variable, wanted.body, witness, solve(instance, context, available)); }
        catch (error) { preserveSettleSearchLimit(error); }
      }
    }

    if (wanted.tag === "pred") {
      // Transport known predicate facts across local equalities.  This is what
      // lets a branch containing y = A and x ∈ y immediately establish x ∈ A.
      for (const equalityFact of available) {
        if (equalityFact.formula.tag !== "eq") continue;
        for (const predicateFact of available) {
          if (predicateFact.formula.tag !== "pred") continue;
          for (let argumentIndex = 0; argumentIndex < predicateFact.formula.args.length; argumentIndex += 1) {
            const argument = predicateFact.formula.args[argumentIndex]!;
            const reverse = termCanonical(argument) === termCanonical(equalityFact.formula.right);
            if (!reverse && termCanonical(argument) !== termCanonical(equalityFact.formula.left)) continue;
            const forbidden = freeFormulaVariables(predicateFact.formula);
            let variable = "__settleTransport";
            while (forbidden.has(variable)) variable += "_";
            const motiveArgs = [...predicateFact.formula.args];
            motiveArgs[argumentIndex] = v(variable);
            const transported = eqElim(
              equalityFact.proof, variable, pred(predicateFact.formula.pred, ...motiveArgs), predicateFact.proof, reverse,
            );
            if (formulaEquals(kernel.checkProof(transported, context), wanted)) return transported;
          }
        }
      }
      for (const rule of rules) {
        let schema = kernel.checkProof(rule, context);
        const variables: string[] = [];
        while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
        const conditions: Formula[] = [];
        while (schema.tag === "imp") { conditions.push(schema.left); schema = schema.right; }
        if (schema.tag !== "eq") continue;
        if (isVariablePermutation(schema.left, schema.right, variables)) continue;
        for (let argumentIndex = 0; argumentIndex < wanted.args.length; argumentIndex += 1) {
          const substitution = new Map<string, Term>();
          if (!match(schema.left, wanted.args[argumentIndex]!, new Set(variables), substitution)) continue;
          if (variables.some(variable => !substitution.has(variable))) continue;
          let equality = at(rule, ...variables.map(variable => substitution.get(variable)!));
          let failed = false;
          for (const condition of conditions) {
            const instantiatedCondition = substituteManyFormula(condition, substitution);
            try { equality = impElim(equality, guard(instantiatedCondition, context, available)); }
            catch (error) {
              preserveSettleSearchLimit(error);
              const typed = instantiatedCondition.tag === "pred" && instantiatedCondition.args.length === 1
                ? proveSoftType(kernel, instantiatedCondition.args[0]!, instantiatedCondition.pred,
                    context, available.map(item => item.proof), visibility)
                : undefined;
              if (typed) equality = impElim(equality, typed);
              else { failed = true; break; }
            }
          }
          if (failed) continue;
          const conclusion = kernel.checkProof(equality, context);
          if (conclusion.tag !== "eq") continue;
          const rewrittenArgs = [...wanted.args];
          rewrittenArgs[argumentIndex] = conclusion.right;
          const rewritten = pred(wanted.pred, ...rewrittenArgs);
          try {
            const evidence = solve(rewritten, context, available);
            const forbidden = freeFormulaVariables(wanted);
            let variable = "__settleRewrite";
            while (forbidden.has(variable)) variable += "_";
            const motiveArgs = [...wanted.args];
            motiveArgs[argumentIndex] = v(variable);
            return eqElim(equality, variable, pred(wanted.pred, ...motiveArgs), evidence, true);
          } catch (error) { preserveSettleSearchLimit(error); }
        }
      }
    }

      for (const rule of rules) {
        let schema = kernel.checkProof(rule, context);
        const variables: string[] = [];
        while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
        while (schema.tag === "imp") schema = schema.right;
        const candidates = schema.tag === "iff"
          ? [
              { pattern: schema, premise: undefined, reverse: false },
              { pattern: schema.left, premise: schema.right, reverse: true },
              { pattern: schema.right, premise: schema.left, reverse: false },
            ]
          : [{ pattern: schema, premise: undefined, reverse: false }];
        for (const candidate of candidates) {
          const substitution = new Map<string, Term>();
          if (!matchFormula(candidate.pattern, wanted, new Set(variables), substitution)) continue;
          if (variables.some(variable => !substitution.has(variable))) continue;
          let instantiated = at(rule, ...variables.map(variable => substitution.get(variable)!));
          let conclusion = kernel.checkProof(instantiated, context);
          let failed = false;
          while (conclusion.tag === "imp") {
            try {
              instantiated = impElim(instantiated, guard(conclusion.left, context, available));
              conclusion = kernel.checkProof(instantiated, context);
            } catch (error) {
              preserveSettleSearchLimit(error);
              failed = true;
              break;
            }
          }
          if (failed) continue;
          if (candidate.premise === undefined) {
            if (formulaEquals(conclusion, wanted)) return instantiated;
            continue;
          }
          if (conclusion.tag !== "iff") continue;
          const premise = candidate.reverse ? conclusion.right : conclusion.left;
          const implication = candidate.reverse ? iffElimRight(instantiated) : iffElimLeft(instantiated);
          try { return impElim(implication, solve(premise, context, available)); }
          catch (error) { preserveSettleSearchLimit(error); }
        }
      }
      if (wanted.tag === "iff") {
        return {
          rule: "iffIntro",
          forward: solve({ tag: "imp", left: wanted.left, right: wanted.right }, context, available),
          backward: solve({ tag: "imp", left: wanted.right, right: wanted.left }, context, available),
        };
      }
    } finally {
      active.delete(key);
    }
    throw new Error(`settle did not close the logical goal ${formatFormula(wanted)}`);
  };
  try { return solve(goal, assumptions, facts); }
  finally {
    if (profile && started !== undefined) {
      const elapsed = globalThis.performance.now() - started;
      if (elapsed >= 10) console.error(
        `${elapsed.toFixed(2)} ms settle (${congruenceMilliseconds.toFixed(2)} cc, ${forwardMilliseconds.toFixed(2)} forward, ${seedFacts.length} facts) ${formatFormula(goal)}`,
      );
    }
  }
}

function substituteManyFormula(formula: Formula, substitution: ReadonlyMap<string, Term>): Formula {
  let result = formula;
  for (const [variable, term] of substitution) {
    result = substituteFormula(result, variable, term);
  }
  return result;
}

function uniqueTerms(terms: readonly Term[]): Term[] {
  const seen = new Set<string>();
  return terms.filter(term => {
    const key = termCanonical(term);
    if (seen.has(key)) return false;
    seen.add(key);
    return true;
  });
}

/** Conjunctions split into their conjuncts, and transparent guard facts opened to theirs. */
function expandFacts(kernel: Kernel, facts: readonly AvailableFact[], visibility?: ScopeVisibility): AvailableFact[] {
  const result: AvailableFact[] = [];
  const add = (fact: AvailableFact): void => {
    result.push(fact);
    if (fact.formula.tag === "and") {
      add({ formula: fact.formula.left, proof: andElimLeft(fact.proof) });
      add({ formula: fact.formula.right, proof: andElimRight(fact.proof) });
    } else {
      result.push(...openGuardFact(kernel, fact, visibility));
    }
  };
  facts.forEach(add);
  return result;
}

function forwardRuleFacts(
  kernel: Kernel,
  seeds: readonly AvailableFact[],
  rules: readonly Proof[],
  context: readonly Formula[],
  preprocessed: readonly AvailableFact[] = [],
): AvailableFact[] {
  const result: AvailableFact[] = [];
  const seen = new Set<string>();
  const add = (fact: AvailableFact): void => {
    const key = formulaCanonical(fact.formula);
    if (seen.has(key)) return;
    seen.add(key);
    result.push(fact);
    if (fact.formula.tag === "and") {
      add({ formula: fact.formula.left, proof: andElimLeft(fact.proof) });
      add({ formula: fact.formula.right, proof: andElimRight(fact.proof) });
    }
  };
  const preprocessedKeys = new Set(preprocessed.map(fact => formulaCanonical(fact.formula)));
  interface LocalAtomicRule {
    readonly fact: AvailableFact;
    readonly variables: readonly string[];
    readonly variableSet: ReadonlySet<string>;
    readonly implication: Extract<Formula, { readonly tag: "imp" }>;
  }
  const prepareLocalAtomicImplication = (fact: AvailableFact): LocalAtomicRule | undefined => {
    let schema = fact.formula;
    const variables: string[] = [];
    while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
    if (schema.tag !== "imp" || !["pred", "eq", "bottom"].includes(schema.right.tag)) return undefined;
    return { fact, variables, variableSet: new Set(variables), implication: schema };
  };
  const applyLocalAtomicImplication = (rule: LocalAtomicRule, argument: AvailableFact): void => {
    const substitution = new Map<string, Term>();
    if (!matchFormula(rule.implication.left, argument.formula, rule.variableSet, substitution)) return;
    if (rule.variables.some(variable => !substitution.has(variable))) return;
    const instantiated = at(rule.fact.proof, ...rule.variables.map(variable => substitution.get(variable)!));
    const implication = kernel.checkProof(instantiated, context);
    if (implication.tag === "imp" && formulaEquals(implication.left, argument.formula)) {
      add({ formula: implication.right, proof: impElim(instantiated, argument.proof) });
    }
  };
  // Validate each supplied rule exactly once. Instantiations below are derived
  // structurally from that checked schema; the completed tactic proof is still
  // replayed by the kernel before it can become a theorem.
  const ruleSchemas = rules.map(rule => ({ rule, formula: kernel.checkProof(rule, context) }));
  seeds.forEach(add);
  const localRules: LocalAtomicRule[] = [];
  for (let cursor = 0; cursor < result.length && cursor < 256; cursor += 1) {
    const fact = result[cursor]!;
    const localRule = prepareLocalAtomicImplication(fact);
    if (localRule) {
      localRules.push(localRule);
      for (const argument of [...result]) applyLocalAtomicImplication(localRule, argument);
    }
    for (const rule of localRules) {
      if (rule !== localRule) applyLocalAtomicImplication(rule, fact);
    }
    if (preprocessedKeys.has(formulaCanonical(fact.formula))) continue;
    for (const candidate of ruleSchemas) {
      const rule = candidate.rule;
      let schema = candidate.formula;
      const variables: string[] = [];
      while (schema.tag === "forall") { variables.push(schema.variable); schema = schema.body; }
      if (schema.tag === "imp") {
        const substitution = new Map<string, Term>();
        if (!matchFormula(schema.left, fact.formula, new Set(variables), substitution)) continue;
        if (variables.some(variable => !substitution.has(variable))) continue;
        const instantiated = at(rule, ...variables.map(variable => substitution.get(variable)!));
        const implication = kernel.checkProof(instantiated, context);
        if (implication.tag === "imp" && formulaEquals(implication.left, fact.formula)) {
          add({ formula: implication.right, proof: impElim(instantiated, fact.proof) });
        }
        continue;
      }
      if (schema.tag === "iff") {
        const substitution = new Map<string, Term>();
        if (!matchFormula(schema.left, fact.formula, new Set(variables), substitution)) continue;
        if (variables.some(variable => !substitution.has(variable))) continue;
        const instantiated = at(rule, ...variables.map(variable => substitution.get(variable)!));
        const equivalence = kernel.checkProof(instantiated, context);
        if (equivalence.tag === "iff" && formulaEquals(equivalence.left, fact.formula)) {
          add({ formula: equivalence.right, proof: impElim(iffElimLeft(instantiated), fact.proof) });
        }
        continue;
      }
      if (schema.tag !== "eq" || fact.formula.tag !== "pred") continue;
      for (let argumentIndex = 0; argumentIndex < fact.formula.args.length; argumentIndex += 1) {
        const substitution = new Map<string, Term>();
        if (!match(schema.left, fact.formula.args[argumentIndex]!, new Set(variables), substitution)) continue;
        if (variables.some(variable => !substitution.has(variable))) continue;
        const equality = at(rule, ...variables.map(variable => substitution.get(variable)!));
        const conclusion = kernel.checkProof(equality, context);
        if (conclusion.tag !== "eq") continue;
        const forbidden = freeFormulaVariables(fact.formula);
        let variable = "__settleForward";
        while (forbidden.has(variable)) variable += "_";
        const motiveArgs = [...fact.formula.args];
        motiveArgs[argumentIndex] = v(variable);
        const proof = eqElim(equality, variable, pred(fact.formula.pred, ...motiveArgs), fact.proof);
        add({ formula: kernel.checkProof(proof, context), proof });
      }
    }
  }
  return result;
}

function formulaTerms(formula: Formula): Term[] {
  const nested = (term: Term): Term[] => term.tag === "app" ? [term, ...term.args.flatMap(nested)] : [term];
  switch (formula.tag) {
    case "bottom": return [];
    case "eq": return [...nested(formula.left), ...nested(formula.right)];
    case "pred": return formula.args.flatMap(nested);
    case "imp":
    case "and":
    case "or":
    case "iff": return [...formulaTerms(formula.left), ...formulaTerms(formula.right)];
    case "forall":
    case "exists": return formulaTerms(formula.body);
  }
}

export function matchFormula(
  pattern: Formula,
  target: Formula,
  variables: ReadonlySet<string>,
  substitution: Map<string, Term>,
): boolean {
  if (pattern.tag !== target.tag) return false;
  switch (pattern.tag) {
    case "bottom": return true;
    case "eq": return target.tag === "eq" && match(pattern.left, target.left, variables, substitution) && match(pattern.right, target.right, variables, substitution);
    case "pred": return target.tag === "pred" && pattern.pred === target.pred && pattern.args.length === target.args.length &&
      pattern.args.every((argument, index) => match(argument, target.args[index]!, variables, substitution));
    case "imp":
    case "and":
    case "or":
    case "iff": return target.tag === pattern.tag && matchFormula(pattern.left, target.left, variables, substitution) &&
      matchFormula(pattern.right, target.right, variables, substitution);
    case "forall":
    case "exists": return target.tag === pattern.tag && pattern.variable === target.variable &&
      matchFormula(pattern.body, target.body, variables, substitution);
  }
}

/** Conventional alias; GRACE17's surface name for this operation is `settle`. */
export const simp = settle;

/** Validate and index a stable theorem collection once for reuse across goals. */
export function prepareRewrites(kernel: Kernel, proofs: readonly Proof[]): PreparedRewrites {
  return indexRules(proofs.map(proof => compileRule(kernel, proof, [])!));
}

function indexRules(rules: readonly RewriteRule[]): PreparedRewrites {
  const mutable = new Map<string, RewriteRule[]>();
  for (const rule of rules) {
    const key = rule.left.tag === "app" ? rule.left.fn : "*";
    const bucket = mutable.get(key) ?? [];
    bucket.push(rule);
    mutable.set(key, bucket);
  }
  return Object.freeze({
    tag: "prepared-rewrites" as const,
    rules: Object.freeze([...rules]),
    byRoot: new Map([...mutable].map(([key, bucket]) => [key, Object.freeze([...bucket])])),
  });
}

function compileRule(
  kernel: Kernel,
  proof: Proof,
  assumptions: readonly Formula[],
  requireEquality = true,
): RewriteRule | undefined {
  let formula = kernel.checkProof(proof, assumptions);
  const variables: string[] = [];
  while (formula.tag === "forall") {
    if (variables.includes(formula.variable)) throw new Error("settle rule has shadowed quantifiers");
    variables.push(formula.variable);
    formula = formula.body;
  }
  const conditions: Formula[] = [];
  while (formula.tag === "imp") {
    conditions.push(formula.left);
    formula = formula.right;
  }
  if (formula.tag !== "eq") {
    if (requireEquality) throw new Error("settle rules must prove universally quantified equalities");
    return undefined;
  }
  return {
    variables,
    conditions,
    left: formula.left,
    right: formula.right,
    proof,
    ordered: isVariablePermutation(formula.left, formula.right, variables),
  };
}

/**
 * Context equalities are user facts, not an ordered rewrite system. Orient an
 * occurs-expanding fact toward the smaller side so facts such as `x = f(x)`
 * cannot grow forever. Other facts retain their stated direction: this keeps
 * contextual substitution predictable while making the dangerous case safe.
 */
function compileContextRule(
  kernel: Kernel,
  proof: Proof,
  assumptions: readonly Formula[],
): RewriteRule {
  const rule = compileRule(kernel, proof, assumptions)!;
  if (containsProperSubterm(rule.right, rule.left) && !containsProperSubterm(rule.left, rule.right)) {
    return { ...rule, left: rule.right, right: rule.left, proof: symm(proof) };
  }
  return rule;
}

function containsProperSubterm(term: Term, sought: Term): boolean {
  return term.tag === "app" && term.args.some(argument =>
    termEquals(argument, sought) || containsProperSubterm(argument, sought));
}

function normalize(
  kernel: Kernel,
  term: Term,
  rewrites: PreparedRewrites,
  assumptions: readonly Formula[],
  facts: readonly AvailableFact[],
  factIndex: ReadonlyMap<string, Proof>,
  refinements: RefinementProver,
  relieve: (goal: Formula) => Proof | undefined,
  budget: { remaining: number },
  stats?: SettleStats,
  rewritePath: ReadonlySet<string> = new Set(),
  depth = 0,
): { readonly value: Term; readonly proof: Proof } {
  if (depth > 512) throw new Error("settle exceeded its normalization depth");
  if (budget.remaining-- <= 0) throw new Error("settle exhausted its rewrite fuel");
  if (stats) stats.termsVisited += 1;

  let value = term;
  let proof: Proof = refl(term);
  if (term.tag === "app") {
    const args = term.args.map(argument => normalize(
      kernel, argument, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, stats,
      new Set(), depth + 1,
    ));
    value = app(term.fn, ...args.map(argument => argument.value));
    proof = congr(term.fn, ...args.map(argument => argument.proof));
  }

  const numeral = naturalValue(value);
  const candidates = [
    ...(value.tag === "app" ? rewrites.byRoot.get(value.fn) ?? [] : []),
    ...(numeral !== undefined && numeral > 0n ? rewrites.byRoot.get("succ") ?? [] : []),
    ...(rewrites.byRoot.get("*") ?? []),
  ];
  if (stats) stats.candidatesConsidered += candidates.length;
  for (const rule of candidates) {
    const matched = new Map<string, Term>();
    const variables = new Set(rule.variables);
    if (!match(rule.left, value, variables, matched)) continue;
    // A variable the left side leaves unbound, such as the middle object of
    // an associativity law, is bound by matching a condition against a
    // local fact; nothing is invented.
    for (const substitution of bindConditionVariables(rule.variables, rule.conditions, matched, variables, facts, () => refinements)) {
      let instantiated = at(rule.proof, ...rule.variables.map(variable => substitution.get(variable)!));
      let conclusion = kernel.checkProof(instantiated, assumptions);
      let unavailableCondition = false;
      while (conclusion.tag === "imp") {
        let evidence = factIndex.get(formulaCanonical(conclusion.left));
        if (!evidence && conclusion.left.tag === "pred" && tauRelievable(kernel, conclusion.left, refinements.visibility)) {
          const premise = conclusion.left;
          evidence = refinements.prove(premise.args.at(-1)!, premise.pred, premise.args.slice(0, -1));
        }
        if (!evidence) evidence = relieve(conclusion.left);
        if (!evidence) { unavailableCondition = true; break; }
        instantiated = impElim(instantiated, evidence);
        conclusion = kernel.checkProof(instantiated, assumptions);
      }
      if (unavailableCondition || conclusion.tag !== "eq" || !termEquals(conclusion.left, value)) continue;
      const equality = conclusion;
      if (rule.ordered && termCanonical(equality.right) >= termCanonical(equality.left)) continue;
      if (termEquals(equality.left, equality.right)) continue;
      const valueKey = termCanonical(value);
      const rightKey = termCanonical(equality.right);
      if (rewritePath.has(rightKey) || rightKey === valueKey) continue;
      if (stats) stats.rewrites += 1;
      const nextPath = new Set(rewritePath);
      nextPath.add(valueKey);
      const rest = normalize(
        kernel, equality.right, rewrites, assumptions, facts, factIndex, refinements, relieve, budget, stats,
        nextPath, depth + 1,
      );
      return { value: rest.value, proof: calc(proof, instantiated, rest.proof) };
    }
  }
  return { value, proof };
}

/**
 * The substitutions completing a left-side match of a conditional rewrite
 * rule: the match itself when it binds every variable, and otherwise its
 * extensions by matching each condition that mentions an unbound variable,
 * most constrained first, against the local facts, and failing that by
 * completing the condition through the certified rules. The enumeration is
 * bounded.
 */
function bindConditionVariables(
  ruleVariables: readonly string[], conditions: readonly Formula[], matched: ReadonlyMap<string, Term>,
  variables: ReadonlySet<string>, facts: readonly AvailableFact[], refinements?: () => RefinementProver | undefined,
): Map<string, Term>[] {
  if (ruleVariables.every(variable => matched.has(variable))) return [new Map(matched)];
  const atoms: Formula[] = [];
  const flatten = (formula: Formula): void => {
    if (formula.tag === "and") { flatten(formula.left); flatten(formula.right); } else atoms.push(formula);
  };
  conditions.forEach(flatten);
  const results: Map<string, Term>[] = [];
  let attempts = 0;
  const extend = (current: Map<string, Term>): void => {
    if (results.length >= 16 || attempts > 1024) return;
    if (ruleVariables.every(variable => current.has(variable))) { results.push(current); return; }
    // The most constrained open condition first: the one sharing the most
    // already-bound variables, so a structure hypothesis fixes the carriers
    // before a membership condition is matched against every membership fact.
    const openConditions = atoms.filter(atom => [...freeFormulaVariables(atom)].some(name => variables.has(name) && !current.has(name)));
    const bound = (atom: Formula): number => [...freeFormulaVariables(atom)].filter(name => variables.has(name) && current.has(name)).length;
    const condition = openConditions.sort((left, right) => bound(right) - bound(left))[0];
    if (!condition) return;
    const before = results.length;
    for (const fact of facts) {
      // Only facts of the condition's predicate are candidates; the others
      // do not count against the budget.
      if (condition.tag === "pred" && (fact.formula.tag !== "pred" || fact.formula.pred !== condition.pred)) continue;
      attempts += 1;
      if (attempts > 1024) return;
      const next = new Map(current);
      if (matchFormula(condition, fact.formula, variables, next)) extend(next);
    }
    // No local fact has the condition's shape: the certified rules may still
    // determine its open arguments, as the endpoints of a composite are
    // determined by the guards of its factors.
    if (results.length === before && condition.tag === "pred" && refinements) {
      const open = (term: Term): boolean => [...freeTermVariables(term)].some(name => variables.has(name) && !current.has(name));
      const request = condition.args.map(argument => open(argument) ? undefined : substituteMany(argument, current));
      if (request.every(argument => argument === undefined)) return;
      attempts += 1;
      // The endpoints of one guard may complete in more than one way; each
      // completion is tried in turn, since a later guard may need another.
      for (const completed of refinements()?.completions(condition.pred, request) ?? []) {
        const next = new Map(current);
        if (matchFormula(condition, pred(condition.pred, ...completed.arguments), variables, next)) extend(next);
      }
    }
  };
  extend(new Map(matched));
  return results;
}

function indexFacts(facts: readonly AvailableFact[]): ReadonlyMap<string, Proof> {
  const result = new Map<string, Proof>();
  for (const fact of facts) result.set(formulaCanonical(fact.formula), fact.proof);
  return result;
}

function isVariablePermutation(left: Term, right: Term, variables: readonly string[]): boolean {
  if (variables.length === 0) return false;
  const substitution = new Map<string, Term>();
  if (!match(left, right, new Set(variables), substitution)) return false;
  const images = variables.map(variable => substitution.get(variable));
  if (images.some(image => image?.tag !== "var" || !variables.includes(image.name))) return false;
  if (new Set(images.map(image => (image as Extract<Term, { tag: "var" }>).name)).size !== variables.length) return false;
  const permutedRight = substituteMany(right, substitution);
  return termCanonical(permutedRight) === termCanonical(left);
}

function substituteMany(term: Term, substitution: ReadonlyMap<string, Term>): Term {
  if (term.tag === "var") return substitution.get(term.name) ?? term;
  if (term.tag === "nat") return term;
  return app(term.fn, ...term.args.map(argument => substituteMany(argument, substitution)));
}

function boundFormulaVariables(formula: Formula): Set<string> {
  const result = new Set<string>();
  const visit = (item: Formula): void => {
    switch (item.tag) {
      case "forall": case "exists": result.add(item.variable); visit(item.body); return;
      case "imp": case "and": case "or": case "iff": visit(item.left); visit(item.right); return;
      default: return;
    }
  };
  visit(formula);
  return result;
}

function rewriteCandidates(formula: Formula, underBinders = false): Term[] {
  const result: Term[] = [];
  const visitTerm = (term: Term): void => {
    result.push(term);
    if (term.tag === "app") term.args.forEach(visitTerm);
  };
  const visitFormula = (item: Formula): void => {
    switch (item.tag) {
      case "bottom": return;
      case "eq": visitTerm(item.left); visitTerm(item.right); return;
      case "pred": item.args.forEach(visitTerm); return;
      case "imp": case "and": case "or": case "iff": visitFormula(item.left); visitFormula(item.right); return;
      case "forall": case "exists": if (underBinders) visitFormula(item.body); return;
    }
  };
  visitFormula(formula);
  return result;
}

function replaceFormulaTerm(formula: Formula, source: Term, target: Term, underBinders = false): Formula {
  const replaceTerm = (term: Term): Term => {
    if (termEquals(term, source)) return target;
    if (term.tag !== "app") return term;
    return app(term.fn, ...term.args.map(replaceTerm));
  };
  switch (formula.tag) {
    case "bottom": return formula;
    case "eq": return { tag: "eq", left: replaceTerm(formula.left), right: replaceTerm(formula.right) };
    case "pred": return pred(formula.pred, ...formula.args.map(replaceTerm));
    case "imp": return { tag: "imp", left: replaceFormulaTerm(formula.left, source, target, underBinders), right: replaceFormulaTerm(formula.right, source, target, underBinders) };
    case "and": return { tag: "and", left: replaceFormulaTerm(formula.left, source, target, underBinders), right: replaceFormulaTerm(formula.right, source, target, underBinders) };
    case "or": return { tag: "or", left: replaceFormulaTerm(formula.left, source, target, underBinders), right: replaceFormulaTerm(formula.right, source, target, underBinders) };
    case "iff": return { tag: "iff", left: replaceFormulaTerm(formula.left, source, target, underBinders), right: replaceFormulaTerm(formula.right, source, target, underBinders) };
    case "forall": case "exists": {
      // Do not transport an equality that depends on this bound variable.
      // The kernel checks the resulting equality elimination either way.
      if (!underBinders || freeTermVariables(source).has(formula.variable)) return formula;
      // A binder that would capture a free variable of the replacement is
      // renamed first, so that substituting W := V reaches a body bound by
      // its own V instead of skipping it.
      if (!freeTermVariables(target).has(formula.variable)) {
        return { ...formula, body: replaceFormulaTerm(formula.body, source, target, true) };
      }
      const forbidden = new Set([...freeFormulaVariables(formula.body), ...boundFormulaVariables(formula.body),
        ...freeTermVariables(source), ...freeTermVariables(target)]);
      let renamed = formula.variable;
      for (let index = 1; forbidden.has(renamed); index += 1) renamed = `${formula.variable}_${index}`;
      const body = substituteFormula(formula.body, formula.variable, v(renamed));
      return { ...formula, variable: renamed, body: replaceFormulaTerm(body, source, target, true) };
    }
  }
}

function match(
  pattern: Term,
  target: Term,
  variables: ReadonlySet<string>,
  substitution: Map<string, Term>,
): boolean {
  if (pattern.tag === "var" && variables.has(pattern.name)) {
    const previous = substitution.get(pattern.name);
    if (previous) return termCanonical(previous) === termCanonical(target);
    substitution.set(pattern.name, target);
    return true;
  }
  if (pattern.tag === "var" || target.tag === "var") {
    return pattern.tag === "var" && target.tag === "var" && pattern.name === target.name;
  }
  const patternNat = naturalValue(pattern);
  const targetNat = naturalValue(target);
  if (patternNat !== undefined) return targetNat === patternNat;
  if (pattern.tag === "app" && pattern.fn === "succ" && pattern.args.length === 1 && targetNat !== undefined && targetNat > 0n) {
    return match(pattern.args[0]!, nat(targetNat - 1n), variables, substitution);
  }
  if (pattern.tag !== "app" || target.tag !== "app") return false;
  return pattern.fn === target.fn && pattern.args.length === target.args.length &&
    pattern.args.every((argument, index) => match(argument, target.args[index]!, variables, substitution));
}
