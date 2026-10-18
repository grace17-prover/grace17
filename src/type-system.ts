// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { pred, app, canonical, freeTermVariables, nat, naturalValue, termCanonical, v, type Formula, type Term } from "./ast.ts";
import type { Kernel } from "./kernel.ts";
import { eqElim,
  andElimLeft, andElimRight, andIntro, at, axiom, definition, iffElimLeft, iffElimRight, impElim, theorem, type Proof,
} from "./proof.ts";

interface TypePremise {
  readonly predicate: string;
  readonly arguments: readonly Term[];
}

/** Numerals up to this value are typed by their successor chain; larger ones by halving. */
const NUMERAL_CHAIN_LIMIT = 64n;
const NUMERAL_RULE_FUEL = 4_096;

/** Successor, then arithmetic operations, then anything else. */
function numeralRulePriority(rule: TypeRule): number {
  const head = rule.arguments[0];
  if (rule.arguments.length !== 1 || head?.tag !== "app") return 0;
  if (head.fn === "succ") return 3;
  return /(^|\.)(add|mul|plus|times)$/.test(head.fn) ? 2 : 1;
}

interface TypeRule {
  readonly name: string;
  readonly variables: readonly string[];
  readonly conditions: readonly Formula[];
  readonly premises: readonly TypePremise[];
  readonly predicate: string;
  readonly arguments: readonly Term[];
  readonly proof: Proof;
  readonly transform?: "iffRight" | "iffLeft";
  /** The kernel declaration the rule comes from; a local rule has none. */
  readonly origin?: string;
}

/**
 * What a scope sees of the kernel: a typing rule is consulted only when
 * the declaration it comes from is visible there, and a guard predicate
 * only when a visible module registered it. Without one, the whole kernel
 * is visible, as it is to a file that stands outside the module system.
 */
export interface ScopeVisibility {
  readonly declaration: (name: string) => boolean;
  readonly module: (module: string | undefined) => boolean;
}

function ruleVisible(rule: TypeRule, visibility: ScopeVisibility | undefined): boolean {
  return visibility === undefined || rule.origin === undefined || visibility.declaration(rule.origin);
}

// Rules are immutable once indexed. Reuse their pattern-variable sets across
// candidate matching and across successive refinement contexts.
const ruleVariableSets = new WeakMap<TypeRule, ReadonlySet<string>>();
function ruleVariables(rule: TypeRule): ReadonlySet<string> {
  let variables = ruleVariableSets.get(rule);
  if (!variables) { variables = new Set(rule.variables); ruleVariableSets.set(rule, variables); }
  return variables;
}

interface TypeIndex {
  stamp: string;
  theoremCount: number;
  axiomCount: number;
  definitionCount: number;
  propertyCount: number;
  readonly processed: Set<string>;
  readonly byPredicate: Map<string, readonly TypeRule[]>;
  readonly byName: Map<string, TypeRule>;
}

export interface SoftTypeResult {
  readonly predicate: string;
  readonly proof: Proof;
}

export interface SoftTypeDiagnostic {
  readonly term: Term;
  readonly expected: string;
  readonly inferred: readonly string[];
  readonly candidateRules: readonly string[];
}

export interface SoftTypeRuleReport {
  readonly name: string;
  readonly variables: readonly string[];
  readonly premises: readonly { readonly predicate: string; readonly arguments: readonly string[] }[];
  readonly conclusion: { readonly predicate: string; readonly arguments: readonly string[] };
}

export interface RefinementProver {
  /** The scope the prover answers for, carried to the guards opened beside it. */
  readonly visibility?: ScopeVisibility;
  prove(term: Term, predicate: string, parameters?: readonly Term[]): Proof | undefined;
  /**
   * Find the arguments at the holes of a predicate from the local facts and
   * the certified rules, with the first completion found; the proof is
   * checked by the kernel like any other.
   */
  complete(predicate: string, arguments_: readonly (Term | undefined)[]): InstanceSynthesisResult | undefined;
  /** Up to `limit` completions, the first found first. */
  completions(predicate: string, arguments_: readonly (Term | undefined)[], limit?: number): InstanceSynthesisResult[];
}

export interface InstanceResolutionStats {
  readonly goalsVisited: number;
  readonly memoHits: number;
  readonly rulesConsidered: number;
  readonly successfulCandidates: number;
  readonly maximumDepth: number;
}

export interface InstanceResolutionLimits {
  readonly maximumDepth?: number;
  readonly maximumGoals?: number;
  readonly maximumRuleAttempts?: number;
}

export interface InstanceProver extends RefinementProver {
  /**
   * Resolve a class head with explicit output holes. Known arguments constrain
   * search; every hole is returned as a concrete term from the unique checked
   * instance. The kernel checks the resulting proof like any other.
   */
  resolve(predicate: string, arguments_: readonly (Term | undefined)[]): InstanceSynthesisResult | undefined;
  stats(): InstanceResolutionStats;
}

export interface InstanceSynthesisResult {
  readonly arguments: readonly Term[];
  readonly proof: Proof;
  readonly instance: string;
}

export interface InstanceResolutionDiagnostic {
  readonly predicate: string;
  readonly arguments: readonly Term[];
  readonly candidates: readonly string[];
}

export class InstanceResolutionError extends Error {
  readonly diagnostic: InstanceResolutionDiagnostic;

  constructor(diagnostic: InstanceResolutionDiagnostic) {
    super(`ambiguous instance for ${diagnostic.predicate}(${diagnostic.arguments.map(canonical).join(", ")}): ${diagnostic.candidates.join(", ")}`);
    this.name = "InstanceResolutionError";
    this.diagnostic = diagnostic;
  }
}

export class InstanceResolutionLimitError extends Error {
  readonly limit: keyof Required<InstanceResolutionLimits>;
  readonly value: number;

  constructor(limit: keyof Required<InstanceResolutionLimits>, value: number) {
    super(`instance resolution exceeded ${limit} (${value})`);
    this.name = "InstanceResolutionLimitError";
    this.limit = limit;
    this.value = value;
  }
}

export class SoftTypeError extends Error {
  readonly diagnostic: SoftTypeDiagnostic;

  constructor(diagnostic: SoftTypeDiagnostic) {
    super(`expected ${diagnostic.expected}(${canonical(diagnostic.term)}); inferred ${diagnostic.inferred.join(", ") || "no soft type"}`);
    this.name = "SoftTypeError";
    this.diagnostic = diagnostic;
  }
}

const indices = new WeakMap<Kernel, TypeIndex>();

/**
 * Elaboration metadata about predicates that notation declarations single
 * out. A transparent predicate is a typed guard such as `Morphism(M, dom,
 * cod, f, a, b)`: a local fact of it is opened to its definitional conjuncts
 * (`f ∈ M`, `dom(f) = a`, `cod(f) = b`) wherever local evidence is consulted.
 * A binding predicate is the shape of a structure hypothesis, such as
 * `Category(O, M, dom, cod, comp, id)`, or a transparent guard: a rule
 * variable that its conclusion leaves unbound may be bound by matching such
 * a premise against a local fact, as `b` in `(f : a ⟶ b) → (g : b ⟶ c) →
 * …` is. Each role records the modules whose notations registered it, so
 * that a scope consults a guard only through its imports; a registration
 * made outside any module holds everywhere. Neither set reaches the kernel;
 * every use produces a checked proof.
 */
interface GuardRegistration { readonly transparent: Set<string | undefined>; readonly binding: Set<string | undefined> }
type GuardPredicates = Map<string, GuardRegistration>;
const guardPredicates = new WeakMap<Kernel, GuardPredicates>();

function guardRegistry(kernel: Kernel): GuardPredicates {
  let registry = guardPredicates.get(kernel);
  if (!registry) { registry = new Map(); guardPredicates.set(kernel, registry); }
  return registry;
}

export function registerGuardPredicate(
  kernel: Kernel, predicate: string, role: "transparent" | "binding", module?: string,
): void {
  const registry = guardRegistry(kernel);
  let registration = registry.get(predicate);
  if (!registration) { registration = { transparent: new Set(), binding: new Set() }; registry.set(predicate, registration); }
  registration.binding.add(module);
  if (role === "transparent") registration.transparent.add(module);
}

function guardVisible(modules: ReadonlySet<string | undefined> | undefined, visibility: ScopeVisibility | undefined): boolean {
  if (!modules?.size) return false;
  if (!visibility) return true;
  for (const module of modules) if (visibility.module(module)) return true;
  return false;
}

export function isTransparentPredicate(kernel: Kernel, predicate: string, visibility?: ScopeVisibility): boolean {
  return guardVisible(guardPredicates.get(kernel)?.get(predicate)?.transparent, visibility);
}

export function isBindingPredicate(kernel: Kernel, predicate: string, visibility?: ScopeVisibility): boolean {
  return guardVisible(guardPredicates.get(kernel)?.get(predicate)?.binding, visibility);
}

/**
 * Whether a side condition of a rewrite rule is relieved by the Tau search:
 * a unary soft type, a membership, or a guard or hypothesis shape. Other
 * parameterized refinements are relieved only by direct evidence, so that
 * rewriting stays predictable.
 */
export function tauRelievable(kernel: Kernel, formula: Formula, visibility?: ScopeVisibility): boolean {
  return formula.tag === "pred" && formula.args.length >= 1 &&
    (formula.args.length === 1 || formula.pred === "in" || isBindingPredicate(kernel, formula.pred, visibility));
}

export interface GuardFact { readonly formula: Formula; readonly proof: Proof }

/**
 * The definitional conjuncts of a local fact of a transparent predicate,
 * each with a kernel proof through the predicate's equation; empty for any
 * other fact. Nested conjunctions are split; nested transparent facts are
 * opened in turn.
 */
export function openGuardFact(kernel: Kernel, fact: GuardFact, visibility?: ScopeVisibility, depth = 2): GuardFact[] {
  if (fact.formula.tag !== "pred" || depth <= 0 || !isTransparentPredicate(kernel, fact.formula.pred, visibility)) return [];
  const record = kernel.definitions.get(fact.formula.pred);
  if (!record?.properties.has("equation") || record.parameters.length !== fact.formula.args.length) return [];
  let equivalence: Formula;
  const instantiated = at(definition(fact.formula.pred, "equation"), ...fact.formula.args);
  try { equivalence = kernel.checkProof(instantiated); } catch { return []; }
  if (equivalence.tag !== "iff") return [];
  const result: GuardFact[] = [];
  const add = (item: GuardFact): void => {
    result.push(item);
    if (item.formula.tag === "and") {
      add({ formula: item.formula.left, proof: andElimLeft(item.proof) });
      add({ formula: item.formula.right, proof: andElimRight(item.proof) });
    } else {
      result.push(...openGuardFact(kernel, item, visibility, depth - 1));
    }
  };
  add({ formula: equivalence.right, proof: impElim(iffElimLeft(instantiated), fact.proof) });
  return result;
}

/**
 * Carry the untrusted type index and prepared instance rules of a kernel to
 * its fork, which holds the same declarations and extends them. Both caches
 * are keyed by declaration counts or by the instance registry, so the fork
 * continues incrementally instead of recompiling every rule.
 */
/** Re-key the type index and prepared rules from `source` to `target`. */
export function moveTypeIndex(source: Kernel, target: Kernel): void {
  const index = indices.get(source);
  if (index) { indices.set(target, index); indices.delete(source); }
  const prepared = preparedInstanceRules.get(source);
  if (prepared) { preparedInstanceRules.set(target, prepared); preparedInstanceRules.delete(source); }
  const guards = guardPredicates.get(source);
  if (guards) { guardPredicates.set(target, guards); guardPredicates.delete(source); }
}

export function forkTypeIndex(source: Kernel, target: Kernel): void {
  const index = indices.get(source);
  if (index && !indices.has(target)) {
    indices.set(target, {
      stamp: index.stamp, theoremCount: index.theoremCount, axiomCount: index.axiomCount,
      definitionCount: index.definitionCount, propertyCount: index.propertyCount,
      processed: new Set(index.processed), byName: new Map(index.byName),
      // Buckets are extended in place, so a fork takes its own copies.
      byPredicate: new Map([...index.byPredicate].map(([predicate, rules]) => [predicate, [...rules]])),
    });
  }
  const prepared = preparedInstanceRules.get(source);
  if (prepared && !preparedInstanceRules.has(target)) preparedInstanceRules.set(target, new Map(prepared));
  const guards = guardPredicates.get(source);
  if (guards && !guardPredicates.has(target)) {
    guardPredicates.set(target, new Map([...guards].map(([predicate, registration]) =>
      [predicate, { transparent: new Set(registration.transparent), binding: new Set(registration.binding) }])));
  }
}

/**
 * Produce a kernel proof of a unary predicate on a term using certified
 * subtype and function-signature rules.  The index and search are untrusted;
 * callers may pass the returned proof straight back to Kernel.checkProof.
 */
export function proveSoftType(
  kernel: Kernel,
  term: Term,
  predicate: string,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  visibility?: ScopeVisibility,
): Proof | undefined {
  return proveRefinement(kernel, term, predicate, [], assumptions, facts, visibility);
}

/**
 * Prove a parameterized refinement `predicate(parameters..., term)`.
 * With no parameters this is the ACL2-style Tau query used by `typecheck` for
 * unary soft types.  It is not type-class or mathematical-class resolution.
 */
export function proveRefinement(
  kernel: Kernel,
  term: Term,
  predicate: string,
  parameters: readonly Term[] = [],
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  visibility?: ScopeVisibility,
): Proof | undefined {
  return prepareRefinementProver(kernel, assumptions, facts, visibility).prove(term, predicate, parameters);
}

/**
 * Index one proof context once when a tactic needs several related type
 * queries. The rule index is shared by every scope; `visibility` selects
 * the rules of the declarations the scope sees.
 */
export function prepareRefinementProver(
  kernel: Kernel,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  visibility?: ScopeVisibility,
): RefinementProver {
  const index = typeIndex(kernel);
  return prepareRuleProver(kernel, index.byPredicate, assumptions, facts, false, {}, undefined, visibility);
}

interface PreparedInstanceRules {
  readonly selected: ReadonlyMap<string, readonly TypeRule[]>;
  readonly candidates: RuleCandidates;
}

// A module normally performs many instance queries against the same imported
// registry.  Selecting those declarations and constructing their rigid-head
// index is independent of the changing local proof context, so retain that
// immutable work until the kernel environment stamp changes.
const preparedInstanceRules = new WeakMap<Kernel, Map<string, PreparedInstanceRules>>();

/**
 * Resolve evidence using only registered instance declarations.
 *
 * Search is first-order and indexed by the requested conclusion predicate.
 * Exact local evidence wins; global ambiguity is rejected. Per-context
 * tabling, active-goal cycle detection, and explicit limits prevent the
 * unbounded recursive behavior that can make type-class search unpredictable.
 */
export function prepareInstanceProver(
  kernel: Kernel,
  instanceNames: ReadonlySet<string>,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  limits: InstanceResolutionLimits = {},
  visibility?: ScopeVisibility,
): InstanceProver {
  const index = typeIndex(kernel);
  const registryKey = [...instanceNames].sort().join("\n");
  const kernelCache = preparedInstanceRules.get(kernel) ?? new Map<string, PreparedInstanceRules>();
  if (!preparedInstanceRules.has(kernel)) preparedInstanceRules.set(kernel, kernelCache);
  let prepared = kernelCache.get(registryKey);
  if (!prepared) {
    const mutable = new Map<string, TypeRule[]>();
    for (const name of instanceNames) {
      const rule = index.byName.get(name);
      if (!rule) continue;
      const bucket = mutable.get(rule.predicate) ?? [];
      bucket.push(rule);
      mutable.set(rule.predicate, bucket);
    }
    const selected = new Map([...mutable].map(([predicate, rules]) =>
      [predicate, Object.freeze(rules.sort((left, right) => left.name.localeCompare(right.name)))] as const));
    prepared = Object.freeze({ selected, candidates: prepareInstanceCandidateIndex(selected) });
    kernelCache.set(registryKey, prepared);
  }
  return prepareRuleProver(kernel, prepared.selected, assumptions, facts, true, limits,
    prepared.candidates, visibility) as InstanceProver;
}

type RuleCandidates = (predicate: string, arguments_: readonly (Term | undefined)[]) => readonly TypeRule[];

interface DiscriminationNode {
  readonly edges: Map<string, DiscriminationNode>;
  readonly rules: Set<TypeRule>;
}

const DISCRIMINATION_WILDCARD = "*";
const DISCRIMINATION_END = ")";

/**
 * Refine the conclusion-predicate index by rigid argument heads.  For each
 * query we select the most discriminating argument position, while retaining
 * every variable-headed rule as a wildcard.  This is an
 * elaborator optimization only: the resulting proof is still checked by Kernel.
 */
function prepareInstanceCandidateIndex(
  rulesByPredicate: ReadonlyMap<string, readonly TypeRule[]>,
): RuleCandidates {
  const indices = new Map<string, readonly DiscriminationNode[]>();
  for (const [predicate, rules] of rulesByPredicate) {
    const arity = rules[0]?.arguments.length ?? 0;
    const positions = Array.from({ length: arity }, (_, position): DiscriminationNode => {
      const root = discriminationNode();
      for (const rule of rules) {
        const variables = ruleVariables(rule);
        const argument = rule.arguments[position]!;
        const tokens = flexibleNaturalPattern(argument, variables)
          ? [DISCRIMINATION_WILDCARD]
          : discriminationTokens(argument, variables);
        insertDiscriminationRule(root, tokens, rule);
      }
      return root;
    });
    indices.set(predicate, Object.freeze(positions));
  }
  return (predicate, arguments_) => {
    const all = rulesByPredicate.get(predicate) ?? [];
    const positions = indices.get(predicate);
    if (!positions || positions.length !== arguments_.length) return all;
    let candidates: Set<TypeRule> | undefined;
    for (let position = 0; position < positions.length; position += 1) {
      const argument = arguments_[position];
      if (!argument) continue;
      const matching = retrieveDiscriminationRules(positions[position]!, discriminationTokens(argument));
      candidates = candidates === undefined
        ? matching
        : new Set([...candidates].filter(rule => matching.has(rule)));
      if (candidates.size === 0) break;
    }
    return [...(candidates ?? new Set(all))].sort((left, right) => left.name.localeCompare(right.name));
  };
}

function discriminationNode(): DiscriminationNode {
  return { edges: new Map(), rules: new Set() };
}

function discriminationTokens(term: Term, variables: ReadonlySet<string> = new Set()): string[] {
  if (term.tag === "var" && variables.has(term.name)) return [DISCRIMINATION_WILDCARD];
  const value = naturalValue(term);
  if (value !== undefined) return [`nat:${value}`, DISCRIMINATION_END];
  if (term.tag === "var") return [`var:${term.name}`, DISCRIMINATION_END];
  return [`fn:${term.fn}/${term.args.length}`,
    ...term.args.flatMap(argument => discriminationTokens(argument, variables)), DISCRIMINATION_END];
}

function flexibleNaturalPattern(term: Term, variables: ReadonlySet<string>): boolean {
  if (term.tag !== "app") return false;
  return (term.fn === "succ" && naturalValue(term) === undefined &&
    [...freeRuleTermVariables(term)].some(variable => variables.has(variable))) ||
    term.args.some(argument => flexibleNaturalPattern(argument, variables));
}

function insertDiscriminationRule(root: DiscriminationNode, tokens: readonly string[], rule: TypeRule): void {
  let node = root;
  for (const token of tokens) {
    let child = node.edges.get(token);
    if (!child) { child = discriminationNode(); node.edges.set(token, child); }
    node = child;
  }
  node.rules.add(rule);
}

function retrieveDiscriminationRules(root: DiscriminationNode, tokens: readonly string[]): Set<TypeRule> {
  const result = new Set<TypeRule>();
  const skipTerm = (position: number): number => {
    let depth = 0;
    for (let index = position; index < tokens.length; index += 1) {
      if (tokens[index] === DISCRIMINATION_END) {
        if (depth <= 1) return index + 1;
        depth -= 1;
      } else {
        // Variables and numerals have closing tokens too. Counting only
        // function heads cuts a compound target short at its first atom.
        depth += 1;
      }
    }
    return tokens.length;
  };
  const visit = (node: DiscriminationNode, position: number): void => {
    if (position === tokens.length) node.rules.forEach(rule => result.add(rule));
    const exact = node.edges.get(tokens[position] ?? "");
    if (exact) visit(exact, position + 1);
    const wildcard = node.edges.get(DISCRIMINATION_WILDCARD);
    if (wildcard && position < tokens.length) visit(wildcard, skipTerm(position));
  };
  visit(root, 0);
  return result;
}

function prepareRuleProver(
  kernel: Kernel,
  rulesByPredicate: ReadonlyMap<string, readonly TypeRule[]>,
  assumptions: readonly Formula[],
  facts: readonly Proof[],
  rejectAmbiguity: boolean,
  configuredLimits: InstanceResolutionLimits = {},
  candidateRules?: RuleCandidates,
  visibility?: ScopeVisibility,
): RefinementProver | InstanceProver {
  const available = expandFacts(kernel, assumptions, facts, visibility);
  // Instances are selected by name before they reach this prover; the
  // certified type rules are selected here, by the declarations the scope sees.
  const selectRules = (rules: readonly TypeRule[]): readonly TypeRule[] =>
    rejectAmbiguity || visibility === undefined ? rules : rules.filter(rule => ruleVisible(rule, visibility));
  // Generalized induction hypotheses are local certified refinement rules.
  const localRules = new Map<string, TypeRule[]>();
  if (!rejectAmbiguity) for (const [index, item] of available.entries()) {
    if (item.formula.tag !== "forall") continue;
    const rule = compileTypeRule(kernel, `local_${index}`, item.proof, assumptions);
    if (rule) localRules.set(rule.predicate, [...(localRules.get(rule.predicate) ?? []), rule]);
  }
  const directFacts = new Map<string, Proof>();
  const localPredicates = new Map<string, Map<string, AvailableFact>>();
  for (const item of available) {
    if (item.formula.tag !== "pred") continue;
    const key = refinementKey(item.formula.pred, item.formula.args);
    directFacts.set(key, item.proof);
    // Repeated proofs of one local proposition are not distinct instance
    // choices. Index complete argument tuples, retaining ambiguity
    // when a partially specified request matches different tuples.
    const bucket = localPredicates.get(item.formula.pred) ?? new Map<string, AvailableFact>();
    bucket.set(key, item);
    localPredicates.set(item.formula.pred, bucket);
  }
  /**
   * The substitutions that complete a head match. A rule whose conclusion
   * binds every variable yields the match itself. Otherwise each remaining
   * variable must occur in a premise whose predicate is a binding predicate,
   * and the premise, most constrained first, is matched against the local
   * facts of that predicate, first-order and without inventing terms; at
   * most a bounded number of completions is enumerated, and a rule none of
   * whose premises can bind a variable yields nothing, as before.
   */
  const bindRuleVariables = (
    rule: TypeRule, matched: ReadonlyMap<string, Term>, variables: ReadonlySet<string>, depth = 0,
  ): Map<string, Term>[] => {
    if (rule.variables.every(variable => matched.has(variable))) return [new Map(matched)];
    const results: Map<string, Term>[] = [];
    let attempts = 0;
    const extend = (current: Map<string, Term>): void => {
      if (results.length >= 16 || attempts > 256) return;
      if (rule.variables.every(variable => current.has(variable))) { results.push(current); return; }
      const open = (term: Term): boolean => [...freeTermVariables(term)].some(name => variables.has(name) && !current.has(name));
      // A binding-predicate premise first, since only those bind; among them
      // the most constrained, the one sharing the most already-bound
      // variables. So Subgroup(H, G) binds H for a rule whose premise h ∈ H
      // comes earlier.
      const bound = (item: TypePremise): number => item.arguments.reduce((total, argument) =>
        total + [...freeTermVariables(argument)].filter(name => variables.has(name) && current.has(name)).length, 0);
      const binding = (item: TypePremise): number => isBindingPredicate(kernel, item.predicate, visibility) ? 1 : 0;
      const premise = rule.premises.filter(item => item.arguments.some(open))
        .sort((left, right) => binding(right) - binding(left) || bound(right) - bound(left))[0];
      if (!premise || !isBindingPredicate(kernel, premise.predicate, visibility)) return;
      const before = results.length;
      for (const fact of localPredicates.get(premise.predicate)?.values() ?? []) {
        if (fact.formula.tag !== "pred" || fact.formula.args.length !== premise.arguments.length) continue;
        attempts += 1;
        if (attempts > 256) return;
        const next = new Map(current);
        if (premise.arguments.every((argument, index) => matchTerm(argument, fact.formula.args[index]!, variables, next))) extend(next);
      }
      // No local fact has the premise's shape: the rules may still determine
      // its open arguments, as the guards of two factors determine the
      // endpoints of their composite. The completion is bounded in depth and
      // guarded against cycles.
      if (results.length === before && depth < 8) {
        const request = premise.arguments.map(argument => open(argument) ? undefined : instantiateRuleTerm(argument, current));
        if (request.every(argument => argument === undefined)) return;
        attempts += 1;
        const completed = resolve(premise.predicate, request, depth + 1);
        if (!completed) return;
        const next = new Map(current);
        if (premise.arguments.every((argument, index) => matchTerm(argument, completed.arguments[index]!, variables, next))) extend(next);
      }
    };
    extend(new Map(matched));
    return results;
  };
  const activeCompletions = new Set<string>();
  const memo = new Map<string, Proof | false>();
  const outputMemo = new Map<string, InstanceSynthesisResult | false>();
  const active = new Set<string>();
  const limits = {
    maximumDepth: configuredLimits.maximumDepth ?? 64,
    maximumGoals: configuredLimits.maximumGoals ?? 4096,
    maximumRuleAttempts: configuredLimits.maximumRuleAttempts ?? 100_000,
  };
  const counters = {
    goalsVisited: 0, memoHits: 0, rulesConsidered: 0,
    successfulCandidates: 0, maximumDepth: 0,
  };

  const enforce = (name: keyof typeof limits, value: number): void => {
    if (!rejectAmbiguity || value <= limits[name]) return;
    throw new InstanceResolutionLimitError(name, limits[name]);
  };

  // Tau also follows certified parameterized predicate rules. Unlike registered
  // instances, it previously had no search limits: a missing relational premise
  // could repeatedly grow its terms until canonical memo keys exhausted memory.
  // Bound automatic refinement search before constructing those keys. Returning
  // no evidence is safe; callers can supply an explicit checked proof instead.
  const refinementTermsFit = (arguments_: readonly Term[]): boolean => {
    const pending = [...arguments_];
    let visited = 0;
    while (pending.length) {
      if (++visited > 4096) return false;
      const term = pending.pop()!;
      if (term.tag === "app") pending.push(...term.args);
    }
    return true;
  };
  // Rules whose conclusion names the shape of the term, `f(x) ∈ B` for an
  // application, come before rules concluding about a bare variable, `x ∈ ℝ`
  // from a premise about x: a specific rule closes the goal at once, while
  // the general ones open premise searches of their own, and with enough
  // such rules visible those searches spend the budget before the specific
  // rule is reached. The order is a property of the rule set, not of the
  // declarations loaded, so a proof found alone is found in any larger
  // environment too.
  const specificityCache = new WeakMap<readonly TypeRule[], readonly TypeRule[]>();
  const rigidArguments = (rule: TypeRule): number => rule.arguments.filter(argument => argument.tag !== "var").length;
  const bySpecificity = (rules: readonly TypeRule[]): readonly TypeRule[] => {
    let ordered = specificityCache.get(rules);
    if (!ordered) {
      ordered = rules.map((rule, index) => ({ rule, index, rigid: rigidArguments(rule) }))
        .sort((left, right) => right.rigid - left.rigid || left.index - right.index).map(item => item.rule);
      specificityCache.set(rules, ordered);
    }
    return ordered;
  };
  const solve = (wantedArguments: readonly Term[], wantedPredicate: string, depth = 0): Proof | undefined => {
    if (!rejectAmbiguity && !refinementTermsFit(wantedArguments)) return undefined;
    const key = refinementKey(wantedPredicate, wantedArguments);
    const cached = memo.get(key);
    if (cached !== undefined) { counters.memoHits += 1; return cached || undefined; }
    const direct = directFacts.get(key);
    if (direct) { memo.set(key, direct); return direct; }
    if (!rejectAmbiguity && (depth > 256 || counters.goalsVisited >= 4096 ||
      counters.rulesConsidered >= 100_000)) return undefined;
    if (active.has(key)) return undefined;
    counters.goalsVisited += 1;
    counters.maximumDepth = Math.max(counters.maximumDepth, depth);
    enforce("maximumGoals", counters.goalsVisited);
    enforce("maximumDepth", depth);
    active.add(key);
    try {
      // A large numeral is typed in logarithmic depth without entering the
      // general rule loop, whose other rules can send a numeral down a
      // descent by ones. An even k is f(2, k/2) for a closure rule f whose
      // value the kernel recomputes; an odd k is succ(k - 1) by a successor
      // rule. Small numerals keep the successor chain other code expects.
      // The chain descends to a smaller numeral at every step, so it is
      // not charged against the search depth. Above 128 binary digits the
      // numeral is split in two halves instead, k = q * 2^h + r with q, 2^h,
      // and r of about half the digits, so the certificate's nesting grows
      // with the logarithm of the digit count and a literal of any length
      // is typed by these rules alone.
      const numeral = wantedArguments.length === 1 ? naturalValue(wantedArguments[0]!) : undefined;
      // A literal in a fixed carrier, `k ∈ ℕ`, goes through the rule that
      // reads membership off the literal's soft type, `Nat(n) → n ∈ ω`.
      const member = wantedArguments.length === 2 && wantedPredicate === "in" ? naturalValue(wantedArguments[0]!) : undefined;
      if (member !== undefined && member > NUMERAL_CHAIN_LIMIT) {
        for (const rule of selectRules(rulesByPredicate.get(wantedPredicate) ?? [])) {
          const subject = rule.arguments[0];
          const condition = rule.conditions[0];
          if (rule.arguments.length !== 2 || subject?.tag !== "var" || rule.conditions.length !== 1 ||
            rule.variables.length !== 1 || rule.variables[0] !== subject.name ||
            !sameTerms([rule.arguments[1]!], [wantedArguments[1]!]) ||
            condition?.tag !== "pred" || condition.args.length !== 1 ||
            condition.args[0]!.tag !== "var" || condition.args[0]!.name !== subject.name) continue;
          const evidence = solve([wantedArguments[0]!], condition.pred, depth);
          if (!evidence) continue;
          let proof = at(rule.proof, wantedArguments[0]!);
          if (rule.transform === "iffRight") proof = iffElimRight(proof);
          if (rule.transform === "iffLeft") proof = iffElimLeft(proof);
          proof = impElim(proof, evidence);
          let conclusion: Formula;
          try { conclusion = kernel.checkProof(proof, assumptions); } catch { continue; }
          if (conclusion.tag !== "pred" || conclusion.pred !== wantedPredicate || !sameTerms(conclusion.args, wantedArguments)) continue;
          memo.set(key, proof);
          return proof;
        }
      }
      if (numeral !== undefined && numeral > NUMERAL_CHAIN_LIMIT) {
        const digits = numeral.toString(2).length;
        let pair: readonly [bigint, bigint] | undefined;
        let single: bigint | undefined;
        if (digits <= 128) {
          if (numeral % 2n === 0n) pair = [2n, numeral / 2n]; else single = numeral - 1n;
        } else {
          const half = BigInt(Math.ceil(digits / 2));
          const block = 1n << half;
          const low = numeral % block;
          pair = low === 0n ? [numeral / block, block] : [numeral - low, low];
        }
        const placeholder = "__numeral";
        const applyRule = (rule: TypeRule, candidate: Term, bindings: ReadonlyMap<string, Term>): Proof | undefined => {
          let equation: Proof;
          // Native successor, addition, and multiplication need a handful of
          // steps; a bounded budget stops an unrelated closure function such
          // as a binomial coefficient from being evaluated as a candidate.
          try { equation = kernel.proveComputation(candidate, wantedArguments[0]!, NUMERAL_RULE_FUEL); } catch { return undefined; }
          const evidence: Proof[] = [];
          for (const condition of rule.conditions) {
            if (condition.tag !== "pred" || condition.args[0]!.tag !== "var") return undefined;
            const found = solve([bindings.get(condition.args[0]!.name)!], wantedPredicate, depth);
            if (!found) return undefined;
            evidence.push(found);
          }
          let proof = at(rule.proof, ...rule.variables.map(variable => bindings.get(variable)!));
          for (const premise of evidence) proof = impElim(proof, premise);
          const conclusion = kernel.checkProof(proof, assumptions);
          if (conclusion.tag !== "pred" || conclusion.pred !== wantedPredicate || !sameTerms(conclusion.args, [candidate])) return undefined;
          return eqElim(equation, placeholder, pred(wantedPredicate, v(placeholder)), proof);
        };
        const numeralRules = [...selectRules(rulesByPredicate.get(wantedPredicate) ?? [])]
          .sort((left, right) => Number(numeralRulePriority(right)) - Number(numeralRulePriority(left)));
        for (const rule of numeralRules) {
          const head = rule.arguments[0];
          if (rule.arguments.length !== 1 || head?.tag !== "app") continue;
          if (!rule.conditions.every(condition => condition.tag === "pred" && condition.pred === wantedPredicate &&
            condition.args.length === 1 && condition.args[0]!.tag === "var")) continue;
          if (!head.args.every(argument => argument.tag === "var")) continue;
          const variables = head.args.map(argument => (argument as { name: string }).name);
          if (new Set(variables).size !== variables.length || rule.variables.some(variable => !variables.includes(variable))) continue;
          let proof: Proof | undefined;
          if (pair && head.args.length === 2 && rule.conditions.length === 2) {
            proof = applyRule(rule, app(head.fn, nat(pair[0]), nat(pair[1])),
              new Map([[variables[0]!, nat(pair[0])], [variables[1]!, nat(pair[1])]]));
          } else if (single !== undefined && head.args.length === 1 && rule.conditions.length === 1) {
            proof = applyRule(rule, app(head.fn, nat(single)), new Map([[variables[0]!, nat(single)]]));
          }
          if (!proof) continue;
          memo.set(key, proof);
          return proof;
        }
      }
      const solutions: { readonly name: string; readonly proof: Proof }[] = [];
      for (const rule of [...(localRules.get(wantedPredicate) ?? []),
        ...bySpecificity(selectRules(candidateRules?.(wantedPredicate, wantedArguments) ?? rulesByPredicate.get(wantedPredicate) ?? []))]) {
        if (!rejectAmbiguity && counters.rulesConsidered >= 100_000) return undefined;
        counters.rulesConsidered += 1;
        enforce("maximumRuleAttempts", counters.rulesConsidered);
        const matched = new Map<string, Term>();
        const variables = ruleVariables(rule);
        if (rule.arguments.length !== wantedArguments.length ||
            !rule.arguments.every((argument, index) =>
              matchTerm(argument, wantedArguments[index]!, variables, matched))) continue;
        let found = false;
        for (const substitution of bindRuleVariables(rule, matched, variables, depth)) {
          // Relieve premises before allocating losing candidates' certificates.
          // Every completed application is still checked by the kernel below.
          const evidence: Proof[] = [];
          for (const condition of rule.conditions) {
            const premise = proveInstantiatedCondition(condition, substitution,
              (arguments_, predicate) => solve(arguments_, predicate, depth + 1));
            if (!premise) break;
            evidence.push(premise);
          }
          if (evidence.length !== rule.conditions.length) continue;
          let proof = at(rule.proof, ...rule.variables.map(variable => substitution.get(variable)!));
          if (rule.transform === "iffRight") proof = iffElimRight(proof);
          if (rule.transform === "iffLeft") proof = iffElimLeft(proof);
          for (const premise of evidence) proof = impElim(proof, premise);
          const conclusion = kernel.checkProof(proof, assumptions);
          if (conclusion.tag === "pred" && conclusion.pred === wantedPredicate &&
            sameTerms(conclusion.args, wantedArguments)) {
            counters.successfulCandidates += 1;
            solutions.push({ name: rule.name, proof });
            found = true;
            break;
          }
        }
        if (found && !rejectAmbiguity) break;
      }
      if (solutions.length > 1) throw new InstanceResolutionError({
        predicate: wantedPredicate, arguments: wantedArguments,
        candidates: solutions.map(item => item.name),
      });
      if (solutions[0]) {
        memo.set(key, solutions[0].proof);
        return solutions[0].proof;
      }
      // A membership premise of an instance that no instance proves is left
      // to the certified type rules, as `with *` leaves it: the objects
      // F(a) ∈ obj(D) of a functor's image are typed this way. Sort premises
      // keep their registry-only discipline, so that instances distinguished
      // by a sort premise stay distinct.
      if (rejectAmbiguity && depth > 0 && wantedPredicate === "in") {
        const fallback = typeRuleProver().prove(wantedArguments.at(-1)!, wantedPredicate, wantedArguments.slice(0, -1));
        if (fallback) { memo.set(key, fallback); return fallback; }
      }
    } finally {
      active.delete(key);
    }
    memo.set(key, false);
    return undefined;
  };
  let typeRules: RefinementProver | undefined;
  const typeRuleProver = (): RefinementProver => typeRules ??=
    prepareRuleProver(kernel, typeIndex(kernel).byPredicate, assumptions, facts, false, {}, undefined, visibility) as RefinementProver;
  const resolve = (
    wantedPredicate: string, wantedArguments: readonly (Term | undefined)[], depth = 0,
  ): InstanceSynthesisResult | undefined => {
    if (!wantedArguments.some(argument => argument === undefined)) {
      const concrete = wantedArguments as readonly Term[];
      const proof = solve(concrete, wantedPredicate, depth);
      return proof ? { arguments: concrete, proof, instance: "exact" } : undefined;
    }

    const outputKey = `${wantedPredicate}:${wantedArguments.map(argument =>
      argument === undefined ? "_" : termCanonical(argument)).join("|")}`;
    const cached = outputMemo.get(outputKey);
    if (cached !== undefined) { counters.memoHits += 1; return cached || undefined; }
    if (activeCompletions.has(outputKey)) return undefined;
    activeCompletions.add(outputKey);
    try {
      return complete(wantedPredicate, wantedArguments, outputKey, depth)[0];
    } finally {
      activeCompletions.delete(outputKey);
    }
  };
  const complete = (
    wantedPredicate: string, wantedArguments: readonly (Term | undefined)[], outputKey: string, depth: number,
    limit = 1,
  ): InstanceSynthesisResult[] => {
    counters.goalsVisited += 1;
    enforce("maximumGoals", counters.goalsVisited);

    if (!rejectAmbiguity && (counters.goalsVisited >= 4096 || counters.rulesConsidered >= 100_000)) return [];
    const direct = [...(localPredicates.get(wantedPredicate)?.values() ?? [])].filter(item => item.formula.tag === "pred" &&
      item.formula.args.length === wantedArguments.length &&
      wantedArguments.every((argument, index) => argument === undefined ||
        sameTerms([argument], [item.formula.tag === "pred" ? item.formula.args[index]! : argument])));
    if (direct.length > 1 && rejectAmbiguity) throw new InstanceResolutionError({
      predicate: wantedPredicate,
      arguments: direct[0]!.formula.tag === "pred" ? direct[0]!.formula.args : [],
      candidates: direct.map((_, index) => `local evidence ${index + 1}`),
    });
    if (direct[0]?.formula.tag === "pred") {
      const result = { arguments: direct[0].formula.args, proof: direct[0].proof, instance: "local evidence" };
      outputMemo.set(outputKey, result);
      return [result];
    }

    const solutions: InstanceSynthesisResult[] = [];
    for (const rule of selectRules(candidateRules?.(wantedPredicate, wantedArguments) ??
      rulesByPredicate.get(wantedPredicate) ?? [])) {
      counters.rulesConsidered += 1;
      enforce("maximumRuleAttempts", counters.rulesConsidered);
      if (rule.arguments.length !== wantedArguments.length) continue;
      const matched = new Map<string, Term>();
      const variables = ruleVariables(rule);
      if (!wantedArguments.every((argument, index) => argument === undefined ||
        matchTerm(rule.arguments[index]!, argument, variables, matched))) continue;
      for (const substitution of bindRuleVariables(rule, matched, variables, depth)) {
        const concrete = rule.arguments.map(argument => instantiateRuleTerm(argument, substitution));
        if (concrete.some(argument => argument === undefined)) continue;
        const evidence: Proof[] = [];
        for (const condition of rule.conditions) {
          const found = proveInstantiatedCondition(condition, substitution,
            (arguments_, predicate) => solve(arguments_, predicate, depth + 1));
          if (!found) break;
          evidence.push(found);
        }
        if (evidence.length !== rule.conditions.length) continue;
        let proof = at(rule.proof, ...rule.variables.map(variable => substitution.get(variable)!));
        if (rule.transform === "iffRight") proof = iffElimRight(proof);
        if (rule.transform === "iffLeft") proof = iffElimLeft(proof);
        for (const premise of evidence) proof = impElim(proof, premise);
        const conclusion = kernel.checkProof(proof, assumptions);
        const concreteArguments = concrete as readonly Term[];
        if (conclusion.tag === "pred" && conclusion.pred === wantedPredicate &&
          sameTerms(conclusion.args, concreteArguments)) {
          counters.successfulCandidates += 1;
          solutions.push({ arguments: concreteArguments, proof, instance: rule.name });
          break;
        }
      }
      if (!rejectAmbiguity && solutions.length >= limit) break;
    }
    if (solutions.length > 1 && rejectAmbiguity) throw new InstanceResolutionError({
      predicate: wantedPredicate,
      arguments: solutions[0]!.arguments,
      candidates: solutions.map(item => item.instance),
    });
    outputMemo.set(outputKey, solutions[0] ?? false);
    return solutions;
  };
  const prover = {
    visibility,
    // A prepared refinement prover answers many queries for one tactic; the
    // search budget is per query, while the memo of solved goals is shared.
    prove: (term: Term, predicate: string, parameters: readonly Term[] = []) => {
      if (!rejectAmbiguity) { counters.goalsVisited = 0; counters.rulesConsidered = 0; }
      return solve([...parameters, term], predicate);
    },
    complete: (predicate: string, arguments_: readonly (Term | undefined)[]) => {
      if (!rejectAmbiguity) { counters.goalsVisited = 0; counters.rulesConsidered = 0; }
      return resolve(predicate, arguments_);
    },
    // Several completions, for a caller that must try alternatives: the
    // endpoints of one guard may be completed in more than one way, and only
    // one of them may let a later guard complete.
    completions: (predicate: string, arguments_: readonly (Term | undefined)[], limit = 8): InstanceSynthesisResult[] => {
      if (!rejectAmbiguity) { counters.goalsVisited = 0; counters.rulesConsidered = 0; }
      if (!arguments_.some(argument => argument === undefined)) {
        const single = resolve(predicate, arguments_);
        return single ? [single] : [];
      }
      const outputKey = `${predicate}:${limit}:${arguments_.map(argument =>
        argument === undefined ? "_" : termCanonical(argument)).join("|")}`;
      if (activeCompletions.has(outputKey)) return [];
      activeCompletions.add(outputKey);
      try {
        return complete(predicate, arguments_, outputKey, 0, limit);
      } finally {
        activeCompletions.delete(outputKey);
      }
    },
    ...(rejectAmbiguity ? {
      resolve,
      stats: (): InstanceResolutionStats => Object.freeze({ ...counters }),
    } : {}),
  };
  return Object.freeze(prover) as RefinementProver | InstanceProver;
}

function instantiateRuleTerm(term: Term, substitution: ReadonlyMap<string, Term>): Term | undefined {
  // Simultaneous substitution: caller variables inside a replacement must
  // not be substituted again as if they were the instance's pattern binders.
  if (term.tag === "var") return substitution.get(term.name);
  if (term.tag === "nat") return term;
  const args: Term[] = [];
  for (const argument of term.args) {
    const instantiated = instantiateRuleTerm(argument, substitution);
    if (!instantiated) return undefined;
    args.push(instantiated);
  }
  return args.every((argument, index) => argument === term.args[index]) ? term : app(term.fn, ...args);
}

function refinementKey(predicate: string, arguments_: readonly Term[]): string {
  return `${predicate}:${arguments_.map(term => {
    const value = naturalValue(term);
    return value === undefined ? termCanonical(term) : `#nat:${value}`;
  }).join("|")}`;
}

export function inferSoftTypes(
  kernel: Kernel,
  term: Term,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  visibility?: ScopeVisibility,
): readonly SoftTypeResult[] {
  const prover = prepareRefinementProver(kernel, assumptions, facts, visibility);
  return [...typeIndex(kernel).byPredicate.keys()].sort().flatMap(predicate => {
    const proof = prover.prove(term, predicate);
    return proof ? [{ predicate, proof }] : [];
  });
}

export function softTypeReport(kernel: Kernel): readonly SoftTypeRuleReport[] {
  return [...typeIndex(kernel).byPredicate.values()].flat().map(rule => ({
    name: rule.name,
    variables: [...rule.variables],
    premises: rule.premises.map(item => ({ predicate: item.predicate, arguments: item.arguments.map(canonical) })),
    conclusion: { predicate: rule.predicate, arguments: rule.arguments.map(canonical) },
  })).sort((left, right) => left.name.localeCompare(right.name));
}

export function checkSoftType(
  kernel: Kernel,
  term: Term,
  predicate: string,
  assumptions: readonly Formula[] = [],
  facts: readonly Proof[] = [],
  visibility?: ScopeVisibility,
): Proof {
  const proof = proveSoftType(kernel, term, predicate, assumptions, facts, visibility);
  if (proof) return proof;
  const index = typeIndex(kernel);
  throw new SoftTypeError({
    term,
    expected: predicate,
    inferred: inferSoftTypes(kernel, term, assumptions, facts, visibility).map(item => item.predicate),
    candidateRules: (index.byPredicate.get(predicate) ?? []).filter(rule => ruleVisible(rule, visibility)).map(rule => rule.name),
  });
}

function typeIndex(kernel: Kernel): TypeIndex {
  // A definition's properties are fixed when it is made, so the counts of
  // theorems, axioms, and definitions identify the environment, and a
  // refresh examines only the declarations admitted since the last one.
  const stamp = `${kernel.theorems.size}:${kernel.axioms.size}:${kernel.definitions.size}`;
  let index = indices.get(kernel);
  if (index?.stamp === stamp) return index;
  if (!index || kernel.theorems.size < index.theoremCount || kernel.axioms.size < index.axiomCount ||
      kernel.definitions.size < index.definitionCount) {
    index = {
      stamp: "", theoremCount: 0, axiomCount: 0, definitionCount: 0, propertyCount: 0,
      processed: new Set(), byPredicate: new Map(), byName: new Map(),
    };
    indices.set(kernel, index);
  }
  const addRule = (rule: TypeRule): void => {
    index!.byName.set(rule.name, rule);
    // Insert at the sorted position; the bucket is replaced, never mutated.
    let bucket = index!.byPredicate.get(rule.predicate) as TypeRule[] | undefined;
    if (!bucket) { bucket = []; index!.byPredicate.set(rule.predicate, bucket); }
    let low = 0;
    let high = bucket.length;
    while (low < high) {
      const middle = (low + high) >> 1;
      if (bucket[middle]!.name.localeCompare(rule.name) < 0) low = middle + 1; else high = middle;
    }
    bucket.splice(low, 0, rule);
  };
  const add = (name: string, proof: Proof, origin: string): void => {
    if (index!.processed.has(name)) return;
    index!.processed.add(name);
    const rule = compileTypeRule(kernel, name, proof);
    if (rule) { addRule({ ...rule, origin }); return; }
    // Atomic equivalences include the foundational Nat ↔ membership-in-ω
    // bridge needed by parameterized datatype constructors.
    let formula = kernel.checkProof(proof);
    const variables: string[] = [];
    while (formula.tag === "forall") { variables.push(formula.variable); formula = formula.body; }
    if (formula.tag !== "iff" || formula.left.tag !== "pred" || formula.right.tag !== "pred") return;
    // A direction whose conclusion is bare, `x ∈ A` or `A ⊆ B` over the
    // quantified variables alone, answers every goal of its predicate; when
    // its premise is a membership too, or has the same predicate, as in
    // `{x} ⊆ A ↔ x ∈ A` and `𝒫(A) ⊆ 𝒫(B) ↔ A ⊆ B`, the rule only climbs to
    // an ever larger goal. Such a direction is not a rule; `n ∈ ω → Nat(n)`
    // and its like still are.
    const bare = (side: Formula): boolean => side.tag === "pred" &&
      side.args.every(term => term.tag === "var" && variables.includes(term.name));
    const climbs = (premise: Formula, conclusion: Formula): boolean => bare(conclusion) &&
      conclusion.tag === "pred" && premise.tag === "pred" && (conclusion.pred === "in" || conclusion.pred === premise.pred);
    for (const [premise, conclusion, transform, suffix] of [
      [formula.left, formula.right, "iffLeft", "forward"],
      [formula.right, formula.left, "iffRight", "backward"],
    ] as const) if (!climbs(premise, conclusion)) addRule({ name: `${name}.${suffix}`, variables,
      conditions: [premise], premises: [{ predicate: premise.pred, arguments: premise.args }],
      predicate: conclusion.pred, arguments: conclusion.args, proof, transform, origin });
  };
  let theoremIndex = 0;
  for (const name of kernel.theorems.keys()) { if (theoremIndex++ >= index.theoremCount) add(name, theorem(name), name); }
  let axiomIndex = 0;
  for (const name of kernel.axioms.keys()) { if (axiomIndex++ >= index.axiomCount) add(name, axiom(name), name); }
  let definitionIndex = 0;
  for (const [name, record] of kernel.definitions) {
    if (definitionIndex++ < index.definitionCount) continue;
    for (const property of record.properties.keys()) {
      add(`${name}.${property}`, definition(name, property), name);
      // A transparent predicate alias P(x) := Q(x) contributes the direct
      // proof-producing Tau edge Q(x) → P(x).  This is an indexed, constant
      // candidate lookup, not a recursive class or instance enumeration.
      if (record.kind !== "predicate" || property !== "equation") continue;
      const variables = record.parameters.map(v);
      const instantiated = at(definition(name, property), ...variables);
      const equivalence = kernel.checkProof(instantiated);
      if (equivalence.tag !== "iff" || equivalence.left.tag !== "pred" ||
          equivalence.left.pred !== name || equivalence.right.tag !== "pred") continue;
      const aliasName = `${name}.${property}.tau_alias`;
      if (index!.processed.has(aliasName)) continue;
      index!.processed.add(aliasName);
      addRule({
        name: aliasName,
        variables: [...record.parameters],
        conditions: [equivalence.right],
        premises: [{ predicate: equivalence.right.pred, arguments: equivalence.right.args }],
        predicate: equivalence.left.pred,
        arguments: equivalence.left.args,
        proof: definition(name, property),
        transform: "iffRight",
        origin: name,
      });
    }
  }
  index.stamp = stamp;
  index.theoremCount = kernel.theorems.size;
  index.axiomCount = kernel.axioms.size;
  index.definitionCount = kernel.definitions.size;
  index.propertyCount = 0;
  return index;
}

function compileTypeRule(kernel: Kernel, name: string, proof: Proof, assumptions: readonly Formula[] = []): TypeRule | undefined {
  let formula = kernel.checkProof(proof, assumptions);
  const variables: string[] = [];
  while (formula.tag === "forall") {
    variables.push(formula.variable);
    formula = formula.body;
  }
  const premises: TypePremise[] = [];
  const conditions: Formula[] = [];
  while (formula.tag === "imp") {
    const atoms = typePremises(formula.left);
    if (!atoms) return undefined;
    conditions.push(formula.left);
    premises.push(...atoms);
    formula = formula.right;
  }
  if (formula.tag !== "pred" || formula.args.length === 0) return undefined;
  return { name, variables, conditions, premises, predicate: formula.pred, arguments: formula.args, proof };
}

function typePremises(formula: Formula): TypePremise[] | undefined {
  if (formula.tag === "pred" && formula.args.length > 0) {
    return [{ predicate: formula.pred, arguments: formula.args }];
  }
  if (formula.tag !== "and") return undefined;
  const left = typePremises(formula.left);
  const right = typePremises(formula.right);
  return left && right ? [...left, ...right] : undefined;
}

/** Simultaneous substitution preserves caller variables in premise search. */
function proveInstantiatedCondition(
  formula: Formula,
  substitution: ReadonlyMap<string, Term>,
  solve: (argumentTerms: readonly Term[], predicate: string) => Proof | undefined,
): Proof | undefined {
  const instantiate = (term: Term): Term => {
    if (term.tag === "var") return substitution.get(term.name) ?? term;
    if (term.tag === "nat") return term;
    const args = term.args.map(instantiate);
    return args.every((argument, index) => argument === term.args[index]) ? term : app(term.fn, ...args);
  };
  if (formula.tag === "pred" && formula.args.length > 0)
    return solve(formula.args.map(instantiate), formula.pred);
  if (formula.tag !== "and") return undefined;
  const left = proveInstantiatedCondition(formula.left, substitution, solve);
  if (!left) return undefined;
  const right = proveInstantiatedCondition(formula.right, substitution, solve);
  return right ? andIntro(left, right) : undefined;
}

function sameTerms(left: readonly Term[], right: readonly Term[]): boolean {
  return left.length === right.length && left.every((term, index) => {
    const other = right[index]!;
    if (termCanonical(term) === termCanonical(other)) return true;
    const leftNatural = naturalValue(term);
    const rightNatural = naturalValue(other);
    return leftNatural !== undefined && rightNatural !== undefined && leftNatural === rightNatural;
  });
}

interface AvailableFact { readonly formula: Formula; readonly proof: Proof }

function expandFacts(
  kernel: Kernel, assumptions: readonly Formula[], proofs: readonly Proof[], visibility?: ScopeVisibility,
): AvailableFact[] {
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
  assumptions.forEach(formula => add({ formula, proof: { rule: "assumption", formula } }));
  proofs.forEach(proof => add({ formula: kernel.checkProof(proof, assumptions), proof }));
  return result;
}

function matchTerm(pattern: Term, target: Term, variables: ReadonlySet<string>, substitution: Map<string, Term>): boolean {
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
    return matchTerm(pattern.args[0]!, nat(targetNat - 1n), variables, substitution);
  }
  if (pattern.tag !== "app" || target.tag !== "app") return false;
  return pattern.fn === target.fn && pattern.args.length === target.args.length &&
    pattern.args.every((argument, index) => matchTerm(argument, target.args[index]!, variables, substitution));
}
