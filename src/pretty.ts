// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { freeTermVariables, naturalValue, substituteTerm, termCanonical, termEquals, type Formula, type Term } from "./ast.ts";

/** The pieces a ring scope names: `R.carrier`, `R.add`, `R.zero`, `R.neg`, `R.mul`, `R.one`. */
export type RingPiece = "carrier" | "add" | "zero" | "neg" | "mul" | "one";

/**
 * One argument of the target of a `notation scoped` form: a written
 * parameter passed through, or a piece of a parameter that names a ring
 * scope.
 */
export interface ScopedArgument {
  readonly parameter: string;
  readonly piece?: RingPiece;
}

export interface RingNotation {
  readonly name: string;
  readonly carrier: Term;
  readonly add: Term;
  readonly zero: Term;
  readonly neg: Term;
  readonly mul: Term;
  readonly one: Term;
  readonly call1: string;
  readonly call2: string;
  /** A bare literal outside the ring's operations stays natural, as the
   * index of u(2) does; set for a ring selected by a tactic rather than
   * declared by a section. */
  readonly plainLiterals?: boolean;
}

/**
 * An operation graph read as an infix operator because a hypothesis in scope
 * supplies it: `call2(comp, g, f)` prints as `g ∘ f` while the statement's
 * context carries `Category(O, M, dom, cod, comp, id)`.
 */
export interface OperationNotation {
  readonly operation: Term;
  readonly token: string;
  readonly precedence: number;
  readonly associativity: "left" | "right" | "none";
  /** The canonical application symbol: call2 for a binary operation, apply for a unary one. */
  readonly call: string;
  /**
   * A unary operation written as a postfix or prefix token, such as a⁻¹ for
   * apply(inv(G), a), or a constant written as a token, such as ⊥ for bot(P).
   */
  readonly fixity?: "postfix" | "prefix" | "constant";
  /**
   * An infix form whose left operand is the operation itself, G ⧸ N for
   * quotientGroup(G, N): the call takes the operation and the right operand.
   */
  readonly structure?: true;
}

/**
 * A mixfix predicate form supplied by a hypothesis in scope: `Morphism(M,
 * dom, cod, f, a, b)` prints as `f : a ⟶ b` while a category with these
 * morphisms, domains, and codomains is among the hypotheses. The fixed
 * arguments are those read from the hypothesis; the others are the
 * placeholders, printed around the literals.
 */
export interface PredicateNotation {
  readonly predicate: string;
  readonly fixed: readonly (Term | undefined)[];
  readonly literals: readonly string[];
  /** An infix predicate such as `a ≤ b`, printed without parentheses inside a larger formula. */
  readonly infix?: boolean;
}

/**
 * A function form supplied by a hypothesis in scope, `ker(f)` for
 * `ringKernel(f, R.carrier, S.zero)` under `f : R →+* S`: the template at
 * the hypothesis, with the free written arguments as the holes
 * `$argument0`, `$argument1`, …, and the arguments the hypothesis fixes.
 */
export interface FunctionNotation {
  readonly token: string;
  readonly template: Term;
  /** The printed arguments, in order: a term fixed by the hypothesis, or undefined for a hole of the template. */
  readonly arguments: readonly (Term | undefined)[];
}

/** A structure variable and the carrier a hypothesis in scope gives it. */
export interface CarrierNotation {
  readonly structure: string;
  readonly carrier: Term;
  /** A structure value rather than a variable, `polynomialRing(R, I)`, printed as a term. */
  readonly term?: Term;
}

export interface PrettyOptions {
  readonly rings?: readonly RingNotation[];
  /** Operations supplied by hypotheses in scope, printed with their declared tokens. */
  readonly operations?: readonly OperationNotation[];
  /** Mixfix predicate forms supplied by hypotheses in scope. */
  readonly predicates?: readonly PredicateNotation[];
  /** Functors in scope: `obj(F)(x)` and `map(F)(x)` print as `F(x)`. */
  readonly functors?: readonly Term[];
  /**
   * The carriers that hypotheses in scope give structure variables, `G` for
   * `G.carrier` under `Group(G)`: a membership binder in one prints as the
   * carrier binder `(a : G)`.
   */
  readonly carriers?: readonly CarrierNotation[];
  /** Function forms supplied by hypotheses in scope, printed as `ker(f)`. */
  readonly functions?: readonly FunctionNotation[];
  /** Render a canonical symbol with the shortest name valid in this view. */
  readonly symbol?: (name: string) => string;
  /** Predicates represented as surface classes print with membership syntax. */
  readonly classPredicate?: (name: string) => boolean;
  /** Active surface notations used to recover mathematical syntax from the
   * explicit kernel term (including instance-selected call1/call2 terms). */
  readonly notations?: readonly PrettyNotation[];
  /**
   * The sorts the enclosing quantifier prefix gives its variables, `A ↦ Real`
   * under `∀ A B : ℝ`, and the codomain sorts of its function variables,
   * `f ↦ Real` under `(f : ℝ → ℝ)`: a coerced natural number beside a term
   * of visible sort prints without the coercion.
   */
  readonly sorts?: ReadonlyMap<string, string>;
  readonly codomains?: ReadonlyMap<string, string>;
  /**
   * The notation identities one spelling would confuse in the formula being
   * printed: of two declarations that print with one token, the one met
   * later prints by name. Filled in once at the top of a formula or term.
   */
  readonly ambiguous?: ReadonlySet<string>;
  /**
   * Print for reading back as the same term: a graph applied to a pair is
   * `f((a, b))`, since `f(a, b)` reads as the two-argument call `call2`.
   */
  readonly reparse?: boolean;
}

export interface PrettyNotation {
  readonly token: string;
  readonly fixity?: "prefix" | "postfix" | "numeral" | "alias" | "binder" | "mixfix" | "constant" | "function" | "sequence" | "coercion" | "scoped";
  readonly kind: "function" | "predicate";
  readonly target: string;
  readonly leadingArguments?: readonly Term[];
  /** A `notation scoped` form: the target's arguments as written parameters or ring-scope pieces. */
  readonly expansion?: readonly ScopedArgument[];
  /** Binding strength and grouping, as declared; printing omits the parentheses they make redundant. */
  readonly precedence?: number;
  readonly associativity?: "left" | "right" | "none";
  /** The operand sorts of a typed declaration, and the sort a coercion produces. */
  readonly operandType?: string;
  readonly leftOperandType?: string;
  readonly rightOperandType?: string;
  readonly resultType?: string;
  /** A graph written out in a big operator: its value over its parameters and index. */
  readonly template?: Term;
  readonly parameters?: readonly string[];
  readonly index?: string;
}

/** Superscript spellings of the characters an index may be written in, f⁽ⁿ⁺¹⁾. */
const SUPERSCRIPT_GLYPHS: Readonly<Record<string, string>> = Object.freeze({
  "0": "⁰", "1": "¹", "2": "²", "3": "³", "4": "⁴", "5": "⁵", "6": "⁶", "7": "⁷", "8": "⁸", "9": "⁹",
  "+": "⁺", "-": "⁻",
  a: "ᵃ", b: "ᵇ", c: "ᶜ", d: "ᵈ", e: "ᵉ", f: "ᶠ", g: "ᵍ", h: "ʰ", i: "ⁱ", j: "ʲ", k: "ᵏ", l: "ˡ", m: "ᵐ",
  n: "ⁿ", o: "ᵒ", p: "ᵖ", r: "ʳ", s: "ˢ", t: "ᵗ", u: "ᵘ", v: "ᵛ", w: "ʷ", x: "ˣ", y: "ʸ", z: "ᶻ",
});
const SUPERSCRIPT_VALUES = new Map(Object.entries(SUPERSCRIPT_GLYPHS).map(([plain, glyph]) => [glyph, plain] as const));

/** The index written in superscript, `n + 1` as `ⁿ⁺¹`, or undefined when a character has no superscript. */
export function toSuperscript(text: string): string | undefined {
  const glyphs = [...text.replaceAll(" ", "")].map(character => SUPERSCRIPT_GLYPHS[character]);
  return glyphs.length && glyphs.every(Boolean) ? glyphs.join("") : undefined;
}

/** The plain spelling of a superscript index, `ⁿ⁺¹` as `n+1`; other characters are kept. */
export function fromSuperscript(text: string): string {
  return [...text].map(character => SUPERSCRIPT_VALUES.get(character) ?? character).join("");
}

const leafName = (name: string): string => name.slice(name.lastIndexOf(".") + 1);

/** The term a coercion into `sort` reads from, when `term` is that coercion applied. */
function coercedOperand(term: Term, sort: string | undefined, options?: PrettyOptions): Term | undefined {
  if (!sort || term.tag !== "app" || term.args.length !== 1) return undefined;
  const coercion = options?.notations?.find(item => item.fixity === "coercion" && item.target === term.fn &&
    item.resultType !== undefined && leafName(item.resultType) === leafName(sort));
  return coercion ? term.args[0]! : undefined;
}

/**
 * Whether the text of a term shows its sort: a variable the quantifier prefix
 * sorts, the value of a function variable with that codomain, or a term
 * built by a typed notation of the sort. A numeral and a coerced term show
 * nothing, since they take their sort from their neighbours.
 */
function visiblySorted(term: Term, sort: string | undefined, options?: PrettyOptions): boolean {
  if (!sort) return false;
  const expected = leafName(sort);
  if (term.tag === "var") return options?.sorts?.get(term.name) === expected;
  if (term.tag !== "app" || naturalValue(term) !== undefined) return false;
  if (leafName(term.fn) === "apply" && term.args.length === 2 && term.args[0]!.tag === "var") {
    return options?.codomains?.get(term.args[0]!.name) === expected;
  }
  // A big operator over a sequence of the sort is a value of the sort.
  if (term.args.length === 2 && options?.notations?.some(notation => notation.fixity === "binder" &&
      notation.target === term.fn && notation.operandType !== undefined && leafName(notation.operandType) === expected)) return true;
  const notation = termNotation(term, options);
  if (!notation || notation.fixity === "numeral" || notation.fixity === "coercion") return false;
  const produced = notation.leftOperandType ?? notation.operandType;
  if (produced === undefined || leafName(produced) !== expected) return false;
  // A typed operation shows its sort through an operand that shows its own:
  // realNat(n) + 1 shows nothing, while (B - A) ^ k does under B A : ℝ.
  const operands = term.args.slice(notation.leadingArguments?.length ?? 0);
  if (notation.fixity === "prefix" || notation.fixity === "postfix") return visiblySorted(operands[0]!, notation.operandType, options);
  return visiblySorted(operands[0]!, notation.leftOperandType ?? notation.operandType, options) ||
    visiblySorted(operands[1]!, notation.rightOperandType ?? notation.operandType, options);
}

/** The operand with its coercion dropped when its neighbour shows the sort the coercion produces. */
function uncoerced(term: Term, sort: string | undefined, neighbour: Term, neighbourSort: string | undefined, options?: PrettyOptions): Term {
  const operand = coercedOperand(term, sort, options);
  return operand && sort && neighbourSort && leafName(neighbourSort) === leafName(sort) && visiblySorted(neighbour, sort, options) ? operand : term;
}

/**
 * A member of a `structure` declaration: the projection `Category.obj`
 * prints as `C.obj` on a variable or a chain of projections and as
 * `Category.obj(t)` on any other receiver, the constructor as
 * `Category.mk(…)`, and the datatype predicate as `Category.Data(C)`.
 * Symbols are fully qualified, so the registry is shared by every kernel.
 */
export interface StructureMember {
  readonly structure: string;
  readonly member: string;
  readonly role: "projection" | "parent" | "constructor" | "data";
}

const structureMembers = new Map<string, StructureMember>();

export function registerStructureMember(symbol: string, member: StructureMember): void {
  structureMembers.set(symbol, member);
}

export function structureMember(symbol: string): StructureMember | undefined {
  return structureMembers.get(symbol);
}

/** The projection symbol of a structure's field, `Group.one` for the unit of `Group`. */
export function structureProjection(structure: string, member: string): string | undefined {
  for (const [symbol, item] of structureMembers) {
    if (item.structure === structure && item.member === member && item.role === "projection") return symbol;
  }
  return undefined;
}

/**
 * A carrier printed as its structure variable where a set of elements is
 * meant, `x ∈ G` for `x ∈ G.carrier` under `Group(G)`; any other term as it is.
 */
/**
 * The functions whose arguments are sets of elements, so that a structure
 * variable there is read as its carrier and printed back as the variable:
 * cardinality(G), ringKernel(f, R, S.zero), idealComap(f, R, J).
 */
export const CARRIER_ARGUMENT_FUNCTIONS: ReadonlySet<string> = new Set(["cardinality", "ringKernel", "idealComap", "idealMap"]);

function formatCarrier(term: Term, options?: PrettyOptions): string {
  const carrier = term.tag === "var" ? undefined : options?.carriers?.find(item => termEquals(item.carrier, term));
  return carrier ? (carrier.term ? formatTerm(carrier.term, options) : carrier.structure) : formatTerm(term, options);
}

/** A receiver written before a dot: a variable, a constant, or a chain of projections of one. */
function dottedReceiver(term: Term): boolean {
  if (term.tag === "var") return true;
  if (term.tag !== "app") return false;
  if (term.args.length === 0) return structureMember(term.fn) === undefined;
  const role = term.args.length === 1 ? structureMember(term.fn)?.role : undefined;
  return (role === "projection" || role === "parent") && dottedReceiver(term.args[0]!);
}

/**
 * The receiver of a ring structure's numeral: `ringNat(R.add, R.zero, R.one, k)`
 * prints as `R[k]`, the form it is written in under a bundled hypothesis.
 */
function ringStructureNumeral(term: Term): { readonly receiver: Term; readonly value: bigint } | undefined {
  if (term.tag !== "app" || term.args.length !== 4 || !term.fn.endsWith(".ringNat")) return undefined;
  const members = term.args.slice(0, 3).map(argument =>
    argument.tag === "app" && argument.args.length === 1 ? structureMember(argument.fn) : undefined);
  const receiver = (term.args[0] as Term & { tag: "app" }).args?.[0];
  if (!receiver) return undefined;
  const expected = ["add", "zero", "one"];
  if (!members.every((member, index) => member?.role === "projection" && member.member === expected[index] &&
      member.structure === members[0]!.structure)) return undefined;
  if (!term.args.slice(1, 3).every(argument => argument.tag === "app" && termEquals(argument.args[0]!, receiver))) return undefined;
  const value = naturalValue(term.args[3]!);
  return value === undefined ? undefined : { receiver, value };
}

/** How tightly a rendering binds: atoms and applications never need parentheses. */
interface Shape { readonly precedence: number; readonly associativity: "left" | "right" | "none" }
const ATOMIC = 1_000;
const SHAPE_ADD: Shape = { precedence: 60, associativity: "left" };
const SHAPE_MUL: Shape = { precedence: 70, associativity: "left" };
const SHAPE_POW: Shape = { precedence: 80, associativity: "right" };
const SHAPE_NEG: Shape = { precedence: 80, associativity: "none" };
/** Big-operator prefix tokens, printed with a space before their operand: `⨆ S`, not `⨆S`. */
const SPACED_PREFIX = new Set(["⨆", "⨅", "∑", "∏", "⋃", "⋂"]);

/** The literal k when `term` is the scoped-ring numeral ringNat(add, zero, one, k). */
export function ringNumeralValue(term: Term, ring: { readonly add: Term; readonly zero: Term; readonly one: Term }): bigint | undefined {
  if (term.tag !== "app" || term.args.length !== 4 || !term.fn.endsWith(".ringNat")) return undefined;
  if (!termEquals(term.args[0]!, ring.add) || !termEquals(term.args[1]!, ring.zero) ||
      !termEquals(term.args[2]!, ring.one)) return undefined;
  return naturalValue(term.args[3]!);
}

/** The shape of a term's rendering, or undefined when it is atomic. */
function termShape(term: Term, options?: PrettyOptions): Shape | undefined {
  for (const ring of options?.rings ?? []) {
    if (termEquals(term, ring.zero) || termEquals(term, ring.one)) return undefined;
    if (term.tag !== "app") continue;
    if (ringNumeralValue(term, ring) !== undefined) return undefined;
    if (term.fn === "Grace.Cumulus.Algebra.Group.Power.monoidPow" && term.args.length === 4 &&
        termEquals(term.args[0]!, ring.mul) && termEquals(term.args[1]!, ring.one)) return SHAPE_POW;
    if (term.fn === ring.call1 && term.args.length === 2 && termEquals(term.args[0]!, ring.neg)) return SHAPE_NEG;
    if (term.fn === ring.call2 && term.args.length === 3) {
      if (termEquals(term.args[0]!, ring.add)) return SHAPE_ADD;
      if (termEquals(term.args[0]!, ring.mul)) return SHAPE_MUL;
    }
  }
  if (term.tag !== "app" || naturalValue(term) !== undefined) return undefined;
  const operation = operationNotation(term, options);
  if (operation) return { precedence: operation.precedence, associativity: operation.fixity ? "none" : operation.associativity };
  // A big operator extends over a product, so it is a summand of a sum and
  // a parenthesized factor of a product.
  if (term.args.length === 2 && options?.notations?.some(notation => notation.fixity === "binder" &&
      notation.kind === "function" && notation.target === term.fn)) return { precedence: 61, associativity: "none" };
  if (term.args.length > 0 && options?.rings?.some(ring => termEquals(term, ring.carrier))) return undefined;
  const leaf = term.fn.slice(term.fn.lastIndexOf(".") + 1);
  if ((leaf === "plus" || leaf === "add") && term.args.length === 2) return SHAPE_ADD;
  if ((leaf === "times" || leaf === "mul") && term.args.length === 2) return SHAPE_MUL;
  const notation = termNotation(term, options);
  if (!notation || notation.fixity === "numeral") return undefined;
  if (notation.fixity === "prefix") return { precedence: notation.precedence ?? 80, associativity: "none" };
  if (notation.fixity === "postfix") return { precedence: notation.precedence ?? 90, associativity: "none" };
  return { precedence: notation.precedence ?? 50, associativity: notation.associativity ?? "none" };
}

/** Render an operand of an infix operator, parenthesized only when its own binding is looser. */
function infixOperand(term: Term, parent: Shape, side: "left" | "right", options?: PrettyOptions): string {
  const text = formatTerm(term, options);
  const shape = termShape(term, options);
  if (!shape) return text;
  // A negation directly after an operator is written in parentheses: x + (-x).
  if (side === "right" && shape.associativity === "none" && text.startsWith("-")) return `(${text})`;
  const grouped = shape.precedence > parent.precedence ||
    (shape.precedence === parent.precedence && shape.associativity === parent.associativity &&
      (parent.associativity === "left" ? side === "left" : parent.associativity === "right" && side === "right"));
  return grouped ? text : `(${text})`;
}

/** Render the operand of a prefix or postfix operator. */
function unaryOperand(term: Term, parent: Shape, options?: PrettyOptions): string {
  const text = formatTerm(term, options);
  const shape = termShape(term, options);
  return !shape || shape.precedence > parent.precedence ? text : `(${text})`;
}

function displaySymbol(name: string, options?: PrettyOptions): string {
  if (options?.symbol) return options.symbol(name);
  // Canonical names belong in certificates. Human-facing output defaults to
  // the declaration's own name; context-aware clients can retain a longer,
  // unambiguous suffix through `PrettyOptions.symbol`.
  return name.slice(name.lastIndexOf(".") + 1);
}

/** The scoped notations of a notation table by target, built once per table. */
const scopedNotationIndex = new WeakMap<readonly PrettyNotation[], ReadonlyMap<string, readonly PrettyNotation[]>>();

function scopedNotations(notations: readonly PrettyNotation[], target: string): readonly PrettyNotation[] {
  let index = scopedNotationIndex.get(notations);
  if (!index) {
    const built = new Map<string, PrettyNotation[]>();
    for (const notation of notations) {
      if (notation.fixity !== "scoped" || !notation.expansion) continue;
      const entries = built.get(notation.target);
      if (entries) entries.push(notation);
      else built.set(notation.target, [notation]);
    }
    index = built;
    scopedNotationIndex.set(notations, index);
  }
  return index.get(target) ?? [];
}

function formatScopedStructure(symbol: string, terms: readonly Term[], kind: "function" | "predicate", options?: PrettyOptions): string | undefined {
  if (!options?.rings?.length || !options.notations?.length) return undefined;
  for (const notation of scopedNotations(options.notations, symbol)) {
    if (notation.kind !== kind || notation.expansion!.length !== terms.length) continue;
    const printed = formatScopedForm(symbol, notation, terms, options);
    if (printed !== undefined) return printed;
  }
  return undefined;
}

/**
 * The written form of a scoped notation at the target's arguments: each
 * piece argument must be that piece of one active ring scope, with all the
 * pieces of a parameter from the same scope, and a parameter whose only
 * piece is the carrier may also be an ordinary set. Undefined when several
 * scopes fit equally, so that no alias is chosen over another.
 */
function formatScopedForm(symbol: string, notation: PrettyNotation, terms: readonly Term[], options: PrettyOptions): string | undefined {
  const bound = new Map<string, Term>();
  const scopes = new Map<string, readonly RingNotation[]>();
  notation.expansion!.forEach((argument, index) => {
    const term = terms[index]!;
    if (!argument.piece) { bound.set(argument.parameter, term); return; }
    const candidates = scopes.get(argument.parameter) ?? options.rings!;
    scopes.set(argument.parameter, candidates.filter(ring => termEquals(ring[argument.piece!], term)));
  });
  const args: string[] = [];
  for (const parameter of notation.parameters ?? []) {
    const candidates = scopes.get(parameter);
    if (candidates === undefined) {
      const term = bound.get(parameter);
      if (!term) return undefined;
      args.push(formatTerm(term, options));
    } else if (candidates.length === 1) {
      args.push(candidates[0]!.name);
    } else if (candidates.length === 0 &&
        notation.expansion!.every(argument => argument.parameter !== parameter || argument.piece === "carrier")) {
      const index = notation.expansion!.findIndex(argument => argument.parameter === parameter);
      args.push(formatTerm(terms[index]!, options));
    } else return undefined;
  }
  const head = notation.token === symbol.slice(symbol.lastIndexOf(".") + 1) ? displaySymbol(symbol, options) : notation.token;
  return `${head}(${args.join(", ")})`;
}

export function formatTerm(term: Term, options?: PrettyOptions): string {
  if (options && options.ambiguous === undefined && (options.notations?.length || options.operations?.length)) {
    options = { ...options, ambiguous: ambiguousNotations([term], options) };
  }
  for (const ring of options?.rings ?? []) {
    const wrap = (body: string): string => (options?.rings?.length ?? 0) > 1 ? `${ring.name}[${body}]` : body;
    if (termEquals(term, ring.zero)) return wrap("0");
    if (termEquals(term, ring.one)) return wrap("1");
    const numeral = ringNumeralValue(term, ring);
    if (numeral !== undefined) return wrap(String(numeral));
    if (term.tag === "app" && term.fn === "Grace.Cumulus.Algebra.Group.Power.monoidPow" &&
        term.args.length === 4 && termEquals(term.args[0]!, ring.mul) && termEquals(term.args[1]!, ring.one))
      return wrap(`${infixOperand(term.args[2]!, SHAPE_POW, "left", options)} ^ ${infixOperand(term.args[3]!, SHAPE_POW, "right", { ...options, rings: [] })}`);
    if (term.tag === "app" && term.fn === ring.call1 && term.args.length === 2 && termEquals(term.args[0]!, ring.neg))
      return wrap(`-${unaryOperand(term.args[1]!, SHAPE_NEG, options)}`);
    if (term.tag === "app" && term.fn === ring.call2 && term.args.length === 3) {
      const op = termEquals(term.args[0]!, ring.add) ? "+" : termEquals(term.args[0]!, ring.mul) ? "*" : undefined;
      const right = term.args[2]!;
      const shape = op === "+" ? SHAPE_ADD : SHAPE_MUL;
      if (op === "+" && right.tag === "app" && right.fn === ring.call1 && termEquals(right.args[0]!, ring.neg))
        return wrap(`${infixOperand(term.args[1]!, shape, "left", options)} - ${infixOperand(right.args[1]!, shape, "right", options)}`);
      if (op) return wrap(`${infixOperand(term.args[1]!, shape, "left", options)} ${op} ${infixOperand(right, shape, "right", options)}`);
    }
  }
  // Recover named constructed carriers before printing their internal arguments.
  // Keep atomic carrier names, and do not choose between competing aliases.
  if (term.tag === "app" && term.args.length > 0 && options?.rings?.length) {
    const matches = options.rings.filter(ring => termEquals(term, ring.carrier));
    if (matches.length === 1) return matches[0]!.name;
  }
  const numeral = naturalValue(term);
  if (numeral !== undefined) return String(numeral);
  // A constant a hypothesis supplies, such as bot(P), prints as its token.
  const constant = options?.operations?.find(item => item.fixity === "constant" && termEquals(item.operation, term));
  if (constant) return constant.token;
  const supplied = functionNotation(term, options);
  if (supplied) return supplied;
  const structureNumeral = ringStructureNumeral(term);
  if (structureNumeral) return `${formatTerm(structureNumeral.receiver, options)}[${structureNumeral.value}]`;
  if (term.tag === "var") return term.name;
  if (term.tag === "nat") return term.value;
  const structure = formatScopedStructure(term.fn, term.args, "function", options);
  if (structure) return structure;
  if (term.fn === "empty" && term.args.length === 0) return "∅";
  // The set of natural numbers prints as the source writes it; ω reads
  // back to the same term.
  if (term.fn === "omega" && term.args.length === 0) return "ℕ";
  if (term.fn.endsWith("integers") && term.args.length === 0) return "ℤ";
  if (term.fn.endsWith("rationals") && term.args.length === 0) return "ℚ";
  if (term.fn.endsWith("reals") && term.args.length === 0) return "ℝ";
  if (term.fn === "epsilon0" && term.args.length === 0) return "ε₀";
  if (term.fn === "epsilon0.less" && term.args.length === 0) return "ε₀.less";
  const list = listElements(term);
  if (list) return `[${list.map(element => formatTerm(element, options)).join(", ")}]`;
  const finiteSet = finiteSetElements(term);
  if (finiteSet) return `{${finiteSet.map(element => formatTerm(element, options)).join(", ")}}`;
  const leaf = term.fn.slice(term.fn.lastIndexOf(".") + 1);
  if (leaf === "length" && term.args.length === 2 && listElements(term.args[1]!)) {
    return `length(${formatTerm(term.args[1]!, options)})`;
  }
  if (leaf === "powerset" && term.args.length === 1) return `𝒫(${formatTerm(term.args[0]!, options)})`;
  if (leaf === "union" && term.args.length === 1) {
    const argument = formatTerm(term.args[0]!, options);
    return term.args[0]!.tag === "var" ? `⋃ ${argument}` : `⋃(${argument})`;
  }
  if (leaf === "quotient" && term.args.length === 2) {
    return `(${formatTerm(term.args[0]!, options)} ⧸ ${formatTerm(term.args[1]!, options)})`;
  }
  if (leaf === "riemannIntegral" && term.args.length === 3) {
    return `∫[${formatTerm(term.args[1]!, options)}, ${formatTerm(term.args[2]!, options)}] ${formatTerm(term.args[0]!, options)}`;
  }
  if (leaf === "equivalenceClass" && term.args.length === 3) {
    return `⟦${formatTerm(term.args[2]!, options)}⟧[${formatTerm(term.args[0]!, options)}, ${formatTerm(term.args[1]!, options)}]`;
  }
  if (leaf === "orderedPair" && term.args.length === 2) {
    return `(${formatTerm(term.args[0]!, options)}, ${formatTerm(term.args[1]!, options)})`;
  }
  // The members of a structure: C.obj, Category.obj(F ⋙ G), Category.mk(…).
  const member = structureMember(term.fn);
  if ((member?.role === "projection" || member?.role === "parent") && term.args.length === 1) {
    const receiver = term.args[0]!;
    return dottedReceiver(receiver)
      ? `${formatTerm(receiver, options)}.${member.member}`
      : `${displaySymbol(member.structure, options)}.${member.member}(${formatTerm(receiver, options)})`;
  }
  if (member?.role === "constructor") {
    return `${displaySymbol(member.structure, options)}.mk(${term.args.map(argument => formatTerm(argument, options)).join(", ")})`;
  }
  // Operation graphs applied to their arguments print as applications:
  // call2(op, a, b) is op(a, b) and call1(inv, a) is inv(a).
  // An instance-selected prefix notation such as -x for apply(neg, x) wins
  // over function application syntax.
  const operation = operationNotation(term, options);
  // A unary operation a hypothesis supplies, such as inv(G), prints with its
  // postfix or prefix token: apply(inv(G), a) is a⁻¹.
  if (operation?.fixity) {
    // A nested postfix form keeps its parentheses, (a⁻¹)⁻¹ and (aᶜ)ᶜ, as in
    // print: a⁻¹⁻¹ would read as the exponent −1−1.
    const operand = unaryOperand(term.args[1]!, { precedence: operation.precedence, associativity: "none" }, options);
    return operation.fixity === "postfix" ? `${operand}${operation.token}`
      : `${operation.token}${SPACED_PREFIX.has(operation.token) ? " " : ""}${operand}`;
  }
  const applyNotation = leaf === "apply" && term.args.length === 2 ? termNotation(term, options) : undefined;
  if (leaf === "apply" && term.args.length === 2 && !applyNotation) {
    // A functor's object and morphism maps print as the functor applied.
    const graph = term.args[0]!;
    const functor = graph.tag === "app" && graph.args.length === 1 &&
      ["obj", "map"].includes(graph.fn.slice(graph.fn.lastIndexOf(".") + 1)) &&
      options?.functors?.some(item => termEquals(item, graph.args[0]!)) ? graph.args[0]! : undefined;
    const base = formatTerm(functor ?? graph, options);
    // A postfix form applies without parentheses: f′(x) and f⁽ᵏ⁾(A).
    const postfixBase = graph.tag === "app" && termNotation(graph, options)?.fixity === "postfix";
    const renderedBase = /^[\p{L}_][\p{L}\p{M}\p{N}_.]*$/u.test(base) || base.endsWith(")") || postfixBase
      ? base : `(${base})`;
    const argument = term.args[1]!;
    // A graph applied to a pair prints as the two-argument application the
    // statement form uses, f(a, b), the spelling of call2(f, a, b).
    if (argument.tag === "app" && argument.fn.slice(argument.fn.lastIndexOf(".") + 1) === "orderedPair" &&
        argument.args.length === 2) {
      const pair = `${formatTerm(argument.args[0]!, options)}, ${formatTerm(argument.args[1]!, options)}`;
      return options?.reparse ? `${renderedBase}((${pair}))` : `${renderedBase}(${pair})`;
    }
    const index = formatTerm(argument, options);
    const suffix = unicodeSubscript(index);
    // A subscript index reads back only on a plain name: id(C)(j) stays applied.
    return suffix && !renderedBase.endsWith(")") && (/^\d+$/.test(index) || /^[ijkn]$/.test(index))
      ? `${renderedBase}${suffix}` : `${renderedBase}(${index})`;
  }
  if ((leaf === "plus" || leaf === "add") && term.args.length === 2) {
    return `${infixOperand(term.args[0]!, SHAPE_ADD, "left", options)} + ${infixOperand(term.args[1]!, SHAPE_ADD, "right", options)}`;
  }
  if ((leaf === "times" || leaf === "mul") && term.args.length === 2) {
    return `${infixOperand(term.args[0]!, SHAPE_MUL, "left", options)} * ${infixOperand(term.args[1]!, SHAPE_MUL, "right", options)}`;
  }
  // A big operator prints with a bound variable not free in its operands.
  const binder = term.args.length === 2 ? options?.notations?.find(notation => notation.fixity === "binder" &&
    notation.kind === "function" && notation.target === term.fn) : undefined;
  if (binder) {
    const used = freeTermVariables(term);
    const graph = term.args[0]!;
    // A graph declared as a sequence prints by its value at the index.
    const sequence = graph.tag === "app" ? options?.notations?.find(notation => notation.fixity === "sequence" &&
      notation.target === graph.fn && notation.parameters?.length === graph.args.length && notation.template && notation.index) : undefined;
    const index = [...(sequence ? [sequence.index!] : []), "k", "i", "j", "m", "l"].find(name => !used.has(name)) ?? "k";
    let bodyTerm: Term = { tag: "app", fn: "apply", args: [graph, { tag: "var", name: index }] };
    if (sequence && graph.tag === "app") {
      bodyTerm = substituteTerm(sequence.template!, sequence.index!, { tag: "var", name: index });
      sequence.parameters!.forEach((parameter, position) => { bodyTerm = substituteTerm(bodyTerm, parameter, graph.args[position]!); });
    }
    const body = unaryOperand(bodyTerm, { precedence: 60, associativity: "none" }, options);
    // A bound written n + 1 is the inclusive bound ∑ k ≤ n.
    const bound = term.args[1]!;
    const inclusive = bound.tag === "app" && bound.args.length === 2 && leafName(bound.fn) === "add" && naturalValue(bound.args[1]!) === 1n
      ? bound.args[0]! : undefined;
    return inclusive
      ? `${binder.token} ${index} ≤ ${formatTerm(inclusive, options)}, ${body}`
      : `${binder.token} ${index} < ${formatTerm(bound, options)}, ${body}`;
  }
  if (operation) {
    const shape = { precedence: operation.precedence, associativity: operation.associativity };
    // A form whose left operand is the structure itself has no operation
    // argument before its operands.
    const [first, second] = operation.structure ? [term.args[0]!, term.args[1]!] : [term.args[1]!, term.args[2]!];
    return `${infixOperand(first, shape, "left", options)} ${operation.token} ${infixOperand(second, shape, "right", options)}`;
  }
  const notation = termNotation(term, options);
  if (notation) {
    const operands = term.args.slice(notation.leadingArguments?.length ?? 0);
    if (notation.fixity === "numeral") return notation.token === "_" ? String(naturalValue(term.args.at(-1)!)) : notation.token;
    const shape = termShape(term, options)!;
    if (notation.fixity === "prefix") {
      return `${notation.token}${SPACED_PREFIX.has(notation.token) ? " " : ""}${unaryOperand(operands[0]!, shape, options)}`;
    }
    if (notation.fixity === "postfix") {
      // An indexed form writes its index in superscript, f⁽ⁿ⁺¹⁾; an index
      // with no superscript spelling keeps the function's own name.
      if (notation.token.includes("_")) {
        const [open, close] = notation.token.split("_");
        const index = toSuperscript(formatTerm(operands[1]!, options));
        if (index === undefined) return `${displaySymbol(term.fn, options)}(${term.args.map(argument => formatTerm(argument, options)).join(", ")})`;
        return `${unaryOperand(operands[0]!, shape, options)}${open}${index}${close}`;
      }
      // Primes stack: f′′ is f″ and f′′′ is f‴; a prime after an indexed
      // form needs no parentheses, f⁽ᵏ⁾′.
      if (notation.token === "′") {
        let count = 1;
        let base = operands[0]!;
        while (count < 4 && base.tag === "app" && base.args.length === 1 && base.fn === term.fn) { count += 1; base = base.args[0]!; }
        const indexedBase = base.tag === "app" && termNotation(base, options)?.token.includes("_");
        return `${indexedBase ? formatTerm(base, options) : unaryOperand(base, shape, options)}${["′", "″", "‴", "⁗"][count - 1]}`;
      }
      return `${unaryOperand(operands[0]!, shape, options)}${notation.token}`;
    }
    // A word operator brackets an operand that is a sum, whatever the
    // precedences say: 2 * (n + 1) choose (n + 1) reads, 2 * (n + 1) choose n + 1 does not.
    const wordOperator = /^[\p{L}_]/u.test(notation.token);
    const operand = (child: Term, side: "left" | "right"): string => {
      const text = infixOperand(child, shape, side, options);
      const childShape = termShape(child, options);
      return wordOperator && childShape && childShape.precedence <= SHAPE_ADD.precedence && !text.startsWith("(") ? `(${text})` : text;
    };
    // A coerced natural number beside an operand of visible sort prints
    // without the coercion: realNat(n!) * X is n! * X under X : ℝ.
    const leftSort = notation.leftOperandType ?? notation.operandType;
    const rightSort = notation.rightOperandType ?? notation.operandType;
    const first = uncoerced(operands[0]!, leftSort, operands[1]!, rightSort, options);
    const second = uncoerced(operands[1]!, rightSort, operands[0]!, leftSort, options);
    return `${operand(first, "left")} ${notation.token} ${operand(second, "right")}`;
  }
  // Without a declared notation, a variable or constant graph applied to two
  // arguments is call2, printed as the application op(a, b); the text reads
  // back to the same term.
  const head = term.args[0];
  if (leaf === "call2" && term.args.length === 3 && head !== undefined &&
      (head.tag === "var" || (head.tag === "app" && head.args.length === 0) ||
        (head.tag === "app" && head.args.length === 1 && structureMember(head.fn)?.role === "projection"))) {
    return `${formatTerm(head, options)}(${term.args.slice(1).map(argument => formatTerm(argument, options)).join(", ")})`;
  }
  const alias = options?.notations?.find(notation => notation.fixity === "alias" && notation.kind === "function" && notation.target === term.fn);
  const name = alias?.token ?? displaySymbol(term.fn, options);
  if (CARRIER_ARGUMENT_FUNCTIONS.has(leaf)) return `${name}(${term.args.map(argument => formatCarrier(argument, options)).join(", ")})`;
  return term.args.length === 0 ? name : `${name}(${term.args.map(argument => formatTerm(argument, options)).join(", ")})`;
}

const SUBSCRIPT_GLYPHS: Readonly<Record<string, string>> = Object.freeze({
  "0": "₀", "1": "₁", "2": "₂", "3": "₃", "4": "₄",
  "5": "₅", "6": "₆", "7": "₇", "8": "₈", "9": "₉",
  a: "ₐ", e: "ₑ", h: "ₕ", i: "ᵢ", j: "ⱼ", k: "ₖ", l: "ₗ", m: "ₘ",
  n: "ₙ", o: "ₒ", p: "ₚ", r: "ᵣ", s: "ₛ", t: "ₜ", x: "ₓ",
});

function unicodeSubscript(value: string): string | undefined {
  if (!/^\d+$|^[aehijklmnoprstx]$/u.test(value)) return undefined;
  const glyphs = [...value].map(character => SUBSCRIPT_GLYPHS[character]);
  return glyphs.every(Boolean) ? glyphs.join("") : undefined;
}

/** A function form a hypothesis supplies for this term, `ker(f)` for its template at the hypothesis. */
function functionNotation(term: Term, options?: PrettyOptions): string | undefined {
  for (const item of options?.functions ?? []) {
    const bindings = new Map<string, Term>();
    if (!matchTemplate(item.template, term, bindings)) continue;
    const args = item.arguments.map((argument, index) => argument ?? bindings.get(`$argument${index}`));
    if (args.some(argument => argument === undefined)) continue;
    return `${item.token}(${args.map(argument => formatTerm(argument!, options)).join(", ")})`;
  }
  return undefined;
}

/** Match a template whose holes are the variables `$argument…` against a term, binding each hole once. */
function matchTemplate(template: Term, term: Term, bindings: Map<string, Term>): boolean {
  if (template.tag === "var" && template.name.startsWith("$argument")) {
    const bound = bindings.get(template.name);
    if (bound) return termEquals(bound, term);
    bindings.set(template.name, term);
    return true;
  }
  if (template.tag === "var" || term.tag === "var") return template.tag === "var" && term.tag === "var" && template.name === term.name;
  if (template.tag !== "app" || term.tag !== "app") return termEquals(template, term);
  return template.fn === term.fn && template.args.length === term.args.length &&
    template.args.every((argument, index) => matchTemplate(argument, term.args[index]!, bindings));
}

/** The hypothesis-supplied operation applied by this call2 or apply term, if any. */
function operationNotation(term: Extract<Term, { readonly tag: "app" }>, options?: PrettyOptions): OperationNotation | undefined {
  const found = rawOperationNotation(term, options);
  return found && options?.ambiguous?.has(operationIdentity(found)) ? undefined : found;
}

function rawOperationNotation(term: Extract<Term, { readonly tag: "app" }>, options?: PrettyOptions): OperationNotation | undefined {
  if (!options?.operations?.length) return undefined;
  if (term.args.length === 3) {
    return options.operations.find(item => !item.fixity && !item.structure && item.call === term.fn &&
      termEquals(item.operation, term.args[0]!));
  }
  if (term.args.length === 2) {
    return options.operations.find(item => (item.structure || (item.fixity && item.fixity !== "constant")) &&
      item.call === term.fn && termEquals(item.operation, term.args[0]!));
  }
  return undefined;
}

/** The declaration an operation prints under, and the instance of it. */
function operationDeclaration(item: OperationNotation): string {
  return `op|${item.call}|${item.fixity ?? (item.structure ? "structure" : "infix")}`;
}
function operationIdentity(item: OperationNotation): string {
  return `${operationDeclaration(item)}|${termCanonical(item.operation)}`;
}
function notationDeclaration(item: PrettyNotation): string {
  return `nt|${item.target}|${item.fixity ?? "infix"}|${(item.leadingArguments ?? []).map(termCanonical).join(",")}`;
}

/**
 * The notation identities to print by name in these terms: when an
 * operation a hypothesis supplies and another declaration print with one
 * token and fixity, the declaration met first keeps the token and every
 * instance of a later one prints by name, so that x ^ n is never the group
 * power in one place and the matrix power in another; a carrier membership
 * is no syntactic sort, so nothing else would tell them apart. Two typed
 * declarations keep the token, their operand sorts being disjoint, as do
 * two instances of one declaration, whose operands tell them apart, as in
 * f(a * b) = f(a) * f(b). One pass over the terms.
 */
function ambiguousNotations(terms: readonly Term[], options: PrettyOptions): ReadonlySet<string> {
  const first = new Map<string, { readonly declaration: string; readonly operation: boolean }>();
  const ambiguous = new Set<string>();
  const visit = (term: Term): void => {
    if (term.tag !== "app") return;
    const operation = rawOperationNotation(term, options);
    const notation = operation ? undefined : rawTermNotation(term, options);
    const spelling = operation ? `${operation.token}|${operation.fixity ?? "infix"}`
      : notation ? `${notation.token}|${notation.fixity ?? "infix"}` : undefined;
    if (spelling) {
      const declaration = operation ? operationDeclaration(operation) : notationDeclaration(notation!);
      const keeper = first.get(spelling);
      if (keeper === undefined) first.set(spelling, { declaration, operation: operation !== undefined });
      else if (keeper.declaration !== declaration && (keeper.operation || operation !== undefined)) {
        ambiguous.add(operation ? operationIdentity(operation) : declaration);
      }
    }
    term.args.forEach(visit);
  };
  terms.forEach(visit);
  return ambiguous;
}

/** The terms of a formula, outermost first, for the ambiguity pass. */
function formulaTermList(formula: Formula, into: Term[] = []): Term[] {
  switch (formula.tag) {
    case "bottom": return into;
    case "eq": into.push(formula.left, formula.right); return into;
    case "pred": into.push(...formula.args); return into;
    case "imp": case "and": case "or": case "iff": formulaTermList(formula.left, into); return formulaTermList(formula.right, into);
    case "forall": case "exists": return formulaTermList(formula.body, into);
  }
}

function termNotation(term: Extract<Term, { readonly tag: "app" }>, options?: PrettyOptions): PrettyNotation | undefined {
  const found = rawTermNotation(term, options);
  return found && options?.ambiguous?.has(notationDeclaration(found)) ? undefined : found;
}

function rawTermNotation(term: Extract<Term, { readonly tag: "app" }>, options?: PrettyOptions): PrettyNotation | undefined {
  let selected: PrettyNotation | undefined;
  for (const notation of options?.notations ?? []) {
    if (notation.kind !== "function" || notation.target !== term.fn || notation.fixity === "alias" || notation.fixity === "binder" ||
        notation.fixity === "function" || notation.fixity === "sequence" || notation.fixity === "coercion") continue;
    const leading = notation.leadingArguments ?? [];
    if (leading.length > term.args.length ||
        leading.some((argument, index) => !termEquals(argument, term.args[index]!))) continue;
    const operands = term.args.length - leading.length;
    const matches = notation.fixity === "numeral"
      ? (notation.token === "_" ? operands === 1 && naturalValue(term.args.at(-1)!) !== undefined : operands === 0)
      : notation.fixity === "prefix" ? operands === 1
      : notation.fixity === "postfix" ? operands === (notation.token.includes("_") ? 2 : 1) : operands === 2;
    // Prefer a complete numeral value over a less specific operation
    // pattern, and a Unicode token over an ASCII spelling of the same one.
    if (matches && (!selected || leading.length > (selected.leadingArguments?.length ?? 0) ||
        (leading.length === (selected.leadingArguments?.length ?? 0) && !/[^\x00-\x7f]/u.test(selected.token) && /[^\x00-\x7f]/u.test(notation.token)))) selected = notation;
  }
  return selected;
}

function formatPrefixOperand(term: Term, options?: PrettyOptions): string {
  if (term.tag === "var" || naturalValue(term) !== undefined) return formatTerm(term, options);
  const rendered = formatTerm(term, options);
  return rendered.startsWith("(") && rendered.endsWith(")") ? rendered : `(${rendered})`;
}

/** Invert precisely the right-associated elaboration used for finite literals. */
function finiteSetElements(term: Term): readonly Term[] | undefined {
  if (term.tag !== "app") return undefined;
  const leaf = term.fn.slice(term.fn.lastIndexOf(".") + 1);
  if (leaf === "singleton" && term.args.length === 1) return [term.args[0]!];
  // `{a, a}` elaborates to pair(a, a) and prints back as written, so that a
  // printed literal re-parses to the same term; `{a}` alone is singleton(a).
  if (leaf === "pair" && term.args.length === 2) return [term.args[0]!, term.args[1]!];
  if (leaf !== "union2" || term.args.length !== 2) return undefined;
  const head = finiteSetElements(term.args[0]!);
  const tail = finiteSetElements(term.args[1]!);
  return head?.length === 1 && tail && tail.length >= 2 ? [...head, ...tail] : undefined;
}

function listElements(term: Term): readonly Term[] | undefined {
  const elements: Term[] = [];
  let cursor = term;
  for (;;) {
    if (cursor.tag !== "app") return undefined;
    const leaf = cursor.fn.slice(cursor.fn.lastIndexOf(".") + 1);
    if (leaf === "nil" && cursor.fn.includes(".List.") && cursor.args.length === 0) return elements;
    if (leaf !== "cons" || !cursor.fn.includes(".List.") || cursor.args.length !== 2) return undefined;
    elements.push(cursor.args[0]!);
    cursor = cursor.args[1]!;
  }
}

/** The carrier a soft-type predicate ascribes: `Nat(t)` reads as `t : ℕ`. */
const SORT_SYMBOLS: Readonly<Record<string, string>> = Object.freeze({ Nat: "ℕ", Integer: "ℤ", Rational: "ℚ", Real: "ℝ" });
function sortAscription(formula: Formula, variable?: string): { readonly term: Term; readonly symbol: string } | undefined {
  if (formula.tag !== "pred" || formula.args.length !== 1) return undefined;
  const symbol = SORT_SYMBOLS[formula.pred.slice(formula.pred.lastIndexOf(".") + 1)];
  if (!symbol) return undefined;
  const term = formula.args[0]!;
  if (variable !== undefined && (term.tag !== "var" || term.name !== variable)) return undefined;
  return { term, symbol };
}

/** Connective precedences: ¬ 90, ∧ 70, ∨ 60, → 50 (right), ↔ 40, quantifiers and ascriptions lowest. */
function formulaShape(formula: Formula): Shape | undefined {
  switch (formula.tag) {
    case "bottom": case "eq": return undefined;
    case "pred": return undefined;
    case "imp": return formula.right.tag === "bottom" ? { precedence: 90, associativity: "none" } : { precedence: 50, associativity: "right" };
    // A ∧ B ∧ C parses right-nested, so chains print without parentheses.
    case "and": return { precedence: 70, associativity: "right" };
    case "or": return { precedence: 60, associativity: "right" };
    case "iff": return { precedence: 40, associativity: "none" };
    case "forall": case "exists": return { precedence: 10, associativity: "right" };
  }
}

function formulaOperand(formula: Formula, parent: Shape, side: "left" | "right", options?: PrettyOptions): string {
  const text = formatFormulaIn(formula, options, true);
  const shape = formulaShape(formula);
  if (!shape) return text;
  // A quantifier extends to the end, so it needs no parentheses on the right.
  if (shape.precedence === 10 && side === "right") return text;
  const grouped = shape.precedence > parent.precedence ||
    (shape.precedence === parent.precedence && shape.associativity === parent.associativity &&
      (parent.associativity === "left" ? side === "left" : parent.associativity === "right" && side === "right"));
  return grouped ? text : `(${text})`;
}

/**
 * A quantifier prefix with the sort guards of its variables: `∀ m, ∀ n,
 * Nat(m) → Nat(n) → φ` reads as `∀ m n : ℕ, φ`. Variables without a guard
 * keep their plain binder, in order.
 */
function quantifierPrefix(
  formula: Formula, kind: "forall" | "exists", options?: PrettyOptions,
): { readonly text: string; readonly body: Formula; readonly options?: PrettyOptions } | undefined {
  const variables: string[] = [];
  let cursor = formula;
  while (cursor.tag === kind) { variables.push(cursor.variable); cursor = cursor.body; }
  // A sort guard groups as `∀ m n : ℕ,`; a typed guard supplied by a
  // hypothesis, such as `(f : a ⟶ b)`, or by a mixfix form that starts
  // with the colon, such as `(f : ℝ → ℝ)`, groups as a parenthesized binder.
  const guards = new Map<string, { readonly text: string; readonly kind: "sort" | "typed" | "member" }>();
  let scoped = options;
  const guardOf = (body: Formula): { readonly guard: Formula; readonly rest: Formula } | undefined => {
    if (kind === "forall" && body.tag === "imp" && body.right.tag !== "bottom") return { guard: body.left, rest: body.right };
    if (kind === "exists" && body.tag === "and") return { guard: body.left, rest: body.right };
    return undefined;
  };
  for (let split = guardOf(cursor); split; split = guardOf(cursor)) {
    const guard = split.guard;
    const sort = guard.tag === "pred" ? sortAscription(guard) : undefined;
    const typed = !sort && guard.tag === "pred" ? typedGuardAscription(guard, options) ?? mixfixGuardAscription(guard, options) : undefined;
    // A membership guard groups as a bounded binder, `∀ a b ∈ obj(C),`, or
    // as the carrier binder `∀ (a b : G),` when a hypothesis in scope gives
    // `G` that carrier.
    const member = !sort && !typed && guard.tag === "pred" && guard.pred === "in" && guard.args.length === 2 &&
      guard.args[0]!.tag === "var" ? { variable: guard.args[0]!.name, text: formatTerm(guard.args[1]!, options) } : undefined;
    const carrier = member ? (options?.carriers ?? []).find(item => termEquals(item.carrier, (guard as Extract<Formula, { readonly tag: "pred" }>).args[1]!)) : undefined;
    const variable = sort ? (sort.term.tag === "var" ? sort.term.name : undefined) : typed?.variable ?? member?.variable;
    if (variable === undefined || !variables.includes(variable) || guards.has(variable)) break;
    // A bound or ascription that mentions a variable bound later in the
    // prefix is not a binder guard: `∀ x, ∀ A, x ∈ A → φ` keeps its plain
    // binders, while `∀ a b ∈ obj(C), ∀ (f : a ⟶ b), φ` is read as written.
    const later = variables.slice(variables.indexOf(variable) + 1);
    const mentionsLater = (term: Term): boolean => later.some(name => freeTermVariables(term).has(name));
    if ((member && mentionsLater(guard.args[1]!)) || (typed && guard.args.some(mentionsLater))) break;
    guards.set(variable, sort ? { text: sort.symbol, kind: "sort" } : typed ? { text: typed.text, kind: "typed" }
      : carrier ? { text: carrier.term ? formatTerm(carrier.term, options) : carrier.structure, kind: "typed" } : { text: member!.text, kind: "member" });
    scoped = withGuardSorts(scoped, guard);
    cursor = split.rest;
  }
  if (guards.size === 0) return undefined;
  const symbol = kind === "forall" ? "∀" : "∃";
  const groups: string[] = [];
  for (let index = 0; index < variables.length;) {
    const guard = guards.get(variables[index]!);
    let end = index + 1;
    while (end < variables.length && guards.get(variables[end]!)?.text === guard?.text &&
      guards.get(variables[end]!)?.kind === guard?.kind) end += 1;
    const names = variables.slice(index, end).join(" ");
    groups.push(!guard ? `${symbol} ${names},` : guard.kind === "typed" ? `${symbol} (${names} : ${guard.text}),`
      : guard.kind === "member" ? `${symbol} ${names} ∈ ${guard.text},` : `${symbol} ${names} : ${guard.text},`);
    index = end;
  }
  return { text: groups.join(" "), body: cursor, options: scoped };
}

/**
 * A guard written with a mixfix form that starts with the colon, such as
 * `FunctionBetween(f, ℝ, ℝ)` for `_ : _ → _`, read as the ascription of
 * its first placeholder: the variable `f` and the text `ℝ → ℝ`.
 */
function mixfixGuardAscription(
  formula: Extract<Formula, { readonly tag: "pred" }>, options?: PrettyOptions,
): { readonly variable: string; readonly text: string } | undefined {
  const subject = formula.args[0];
  if (!subject || subject.tag !== "var") return undefined;
  const mixfix = (options?.notations ?? []).find(notation => notation.fixity === "mixfix" && notation.kind === "predicate" &&
    notation.target === formula.pred && notation.token.split("_").length - 1 === formula.args.length);
  if (!mixfix) return undefined;
  const literals = mixfix.token.split("_").slice(1, -1).map(piece => piece.trim());
  if (literals[0] !== ":") return undefined;
  const text = formula.args.slice(1).map((argument, index) =>
    index + 1 < literals.length ? `${formatTerm(argument, options)} ${literals[index + 1]} ` : formatTerm(argument, options)).join("");
  return { variable: subject.name, text };
}

/** The carrier sort a set names, `Real` for ℝ, `Nat` for ℕ and ω. */
function carrierSort(term: Term): string | undefined {
  if (term.tag !== "app" || term.args.length !== 0) return undefined;
  return ({ reals: "Real", rationals: "Rational", integers: "Integer", omega: "Nat" } as Readonly<Record<string, string>>)[leafName(term.fn)];
}

/**
 * The options with the sorts a guard shows: `Real(A)` and `A ∈ ℝ` sort the
 * variable, and `FunctionBetween(f, A, ℝ)` gives `f` the codomain sort.
 */
function withGuardSorts(options: PrettyOptions | undefined, guard: Formula): PrettyOptions | undefined {
  if (guard.tag !== "pred") return options;
  const sort = sortAscription(guard);
  if (sort && sort.term.tag === "var") {
    const symbol = Object.entries(SORT_SYMBOLS).find(([, glyph]) => glyph === sort.symbol)?.[0];
    return symbol ? { ...options, sorts: new Map([...(options?.sorts ?? []), [sort.term.name, symbol]]) } : options;
  }
  if (guard.pred === "in" && guard.args.length === 2 && guard.args[0]!.tag === "var") {
    const member = carrierSort(guard.args[1]!);
    return member ? { ...options, sorts: new Map([...(options?.sorts ?? []), [guard.args[0]!.name, member]]) } : options;
  }
  if (leafName(guard.pred) === "FunctionBetween" && guard.args.length === 3 && guard.args[0]!.tag === "var") {
    const codomain = carrierSort(guard.args[2]!);
    return codomain ? { ...options, codomains: new Map([...(options?.codomains ?? []), [guard.args[0]!.name, codomain]]) } : options;
  }
  return options;
}

/**
 * `∀ k, Nat(k) → k ≤ n → φ` reads as `∀ k ≤ n, φ`, and `∃ k, Nat(k) ∧ k < n ∧ φ`
 * as `∃ k < n, φ`, when the bound does not mention the variable.
 */
function orderedQuantifier(
  variable: string, body: Formula, kind: "forall" | "exists",
): { readonly token: string; readonly bound: Term; readonly body: Formula } | undefined {
  const connective = kind === "forall" ? "imp" : "and";
  if (body.tag !== connective || body.left.tag !== "pred" || leafName(body.left.pred) !== "Nat" || body.left.args.length !== 1 ||
      body.left.args[0]!.tag !== "var" || body.left.args[0]!.name !== variable) return undefined;
  const rest = body.right;
  if (rest.tag !== connective || rest.left.tag !== "pred" || rest.left.args.length !== 2 ||
      rest.left.args[0]!.tag !== "var" || rest.left.args[0]!.name !== variable) return undefined;
  const token = leafName(rest.left.pred) === "LessEqual" ? "≤" : leafName(rest.left.pred) === "Less" ? "<" : undefined;
  if (!token || freeTermVariables(rest.left.args[1]!).has(variable)) return undefined;
  if (kind === "forall" && rest.right.tag === "bottom") return undefined;
  return { token, bound: rest.left.args[1]!, body: rest.right };
}

/** The sides of an equation with a coercion dropped where the other side shows its sort. */
function equationSides(left: Term, right: Term, options?: PrettyOptions): readonly [Term, Term] {
  for (const coercion of options?.notations ?? []) {
    if (coercion.fixity !== "coercion" || !coercion.resultType) continue;
    const sort = coercion.resultType;
    const leftOperand = coercedOperand(left, sort, options);
    const rightOperand = coercedOperand(right, sort, options);
    if (leftOperand && !rightOperand && visiblySorted(right, sort, options)) return [leftOperand, right];
    if (rightOperand && !leftOperand && visiblySorted(left, sort, options)) return [left, rightOperand];
  }
  return [left, right];
}

/**
 * A guard supplied by a hypothesis whose pattern starts with a colon, such as
 * `Morphism(C, f, a, b)` under a category, read as the ascription of its
 * first placeholder: the variable `f` and the text `a ⟶ b`.
 */
function typedGuardAscription(
  formula: Extract<Formula, { readonly tag: "pred" }>, options?: PrettyOptions,
): { readonly variable: string; readonly text: string } | undefined {
  const guard = (options?.predicates ?? []).find(item => item.predicate === formula.pred &&
    item.fixed.length === formula.args.length && item.literals[0] === ":" &&
    item.fixed.every((term, index) => term === undefined || termEquals(term, formula.args[index]!)));
  if (!guard) return undefined;
  const placeholders = formula.args.filter((_, index) => guard.fixed[index] === undefined);
  const subject = placeholders[0];
  if (!subject || subject.tag !== "var") return undefined;
  const text = placeholders.slice(1).map((argument, index) =>
    index + 1 < guard.literals.length ? `${formatTerm(argument, options)} ${guard.literals[index + 1]} ` : formatTerm(argument, options)).join("");
  return { variable: subject.name, text };
}

export function formatFormula(formula: Formula, options?: PrettyOptions): string {
  if (options && options.ambiguous === undefined && (options.notations?.length || options.operations?.length)) {
    options = { ...options, ambiguous: ambiguousNotations(formulaTermList(formula), options) };
  }
  return formatFormulaIn(formula, options, false);
}

function formatFormulaIn(formula: Formula, options: PrettyOptions | undefined, nested: boolean): string {
  switch (formula.tag) {
    case "bottom": return "⊥";
    case "eq": {
      const [left, right] = equationSides(formula.left, formula.right, options);
      return `${formatTerm(left, options)} = ${formatTerm(right, options)}`;
    }
    case "pred": {
      if (formula.pred === "in" && formula.args.length === 2) {
        return `${formatTerm(formula.args[0]!, options)} ∈ ${formatCarrier(formula.args[1]!, options)}`;
      }
      // A typed guard supplied by a hypothesis, such as `f : a ⟶ b`, is an
      // ascription on its own and a parenthesized one inside a larger formula.
      const guard = (options?.predicates ?? []).find(item => item.predicate === formula.pred &&
        item.fixed.length === formula.args.length &&
        item.fixed.every((term, index) => term === undefined || termEquals(term, formula.args[index]!)));
      if (guard) {
        const placeholders = formula.args.filter((_, index) => guard.fixed[index] === undefined);
        const text = placeholders.map((argument, index) =>
          index < guard.literals.length ? `${formatTerm(argument, options)} ${guard.literals[index]} ` : formatTerm(argument, options)).join("");
        return nested && !guard.infix ? `(${text})` : text;
      }
      // A sort guard reads as an ascription on its own; inside a larger
      // formula it stays a predicate, as `Nat(x) ∧ P` is clearer than `(x : ℕ) ∧ P`.
      const sort = nested ? undefined : sortAscription(formula);
      if (sort) return `${formatTerm(sort.term, options)} : ${sort.symbol}`;
      // A mixfix notation such as `f : A → B` reads as an ascription on its
      // own; inside a larger formula the predicate spelling stays.
      const mixfix = nested ? undefined : (options?.notations ?? []).find(notation =>
        notation.fixity === "mixfix" && notation.kind === "predicate" && notation.target === formula.pred &&
        notation.token.split("_").length - 1 === formula.args.length);
      if (mixfix) {
        const literals = mixfix.token.split("_").slice(1, -1).map(piece => piece.trim());
        return formula.args.map((argument, index) =>
          index < literals.length ? `${formatTerm(argument, options)} ${literals[index]} ` : formatTerm(argument, options)).join("");
      }
      const structure = formatScopedStructure(formula.pred, formula.args, "predicate", options);
      if (structure) return structure;
      const member = structureMember(formula.pred);
      if (member?.role === "data" && formula.args.length === 1) {
        return `${displaySymbol(member.structure, options)}.Data(${formatTerm(formula.args[0]!, options)})`;
      }
      const notation = predicateNotation(formula, options);
      if (notation) {
        const operands = formula.args.slice(notation.leadingArguments?.length ?? 0);
        // The operands of ⊆ and ⊂ are sets of elements: a carrier prints as its structure.
        const setRelation = ["Subset", "ProperSubset"].includes(notation.target.slice(notation.target.lastIndexOf(".") + 1));
        const render = (term: Term): string => setRelation ? formatCarrier(term, options) : formatTerm(term, options);
        const leftSort = notation.leftOperandType ?? notation.operandType;
        const rightSort = notation.rightOperandType ?? notation.operandType;
        const first = uncoerced(operands[0]!, leftSort, operands[1]!, rightSort, options);
        const second = uncoerced(operands[1]!, rightSort, operands[0]!, leftSort, options);
        return `${render(first)} ${notation.token} ${render(second)}`;
      }
      const leaf = formula.pred.slice(formula.pred.lastIndexOf(".") + 1);
      if (leaf === "LessEqual" && formula.args.length === 2) {
        return `${formatTerm(formula.args[0]!, options)} ≤ ${formatTerm(formula.args[1]!, options)}`;
      }
      if (leaf === "Less" && formula.args.length === 2) {
        return `${formatTerm(formula.args[0]!, options)} < ${formatTerm(formula.args[1]!, options)}`;
      }
      if (leaf === "Subset" && formula.args.length === 2) {
        return `${formatCarrier(formula.args[0]!, options)} ⊆ ${formatCarrier(formula.args[1]!, options)}`;
      }
      if (leaf === "ProperSubset" && formula.args.length === 2) {
        return `${formatCarrier(formula.args[0]!, options)} ⊂ ${formatCarrier(formula.args[1]!, options)}`;
      }
      if (leaf === "Finite" && formula.args.length === 1) {
        return `${displaySymbol(formula.pred, options)}(${formatCarrier(formula.args[0]!, options)})`;
      }
      if (options?.classPredicate?.(formula.pred) && formula.args.length >= 1) {
        const name = displaySymbol(formula.pred, options);
        const classExpression = formula.args.length === 1 ? name
          : `${name}(${formula.args.slice(1).map(argument => formatTerm(argument, options)).join(", ")})`;
        return `${formatTerm(formula.args[0]!, options)} ∈ ${classExpression}`;
      }
      return `${displaySymbol(formula.pred, options)}(${formula.args.map(argument => formatTerm(argument, options)).join(", ")})`;
    }
    case "imp": {
      if (formula.right.tag === "bottom") {
        if (formula.left.tag === "eq") {
          const [left, right] = equationSides(formula.left.left, formula.left.right, options);
          return `${formatTerm(left, options)} ≠ ${formatTerm(right, options)}`;
        }
        if (formula.left.tag === "pred" && formula.left.pred === "in" && formula.left.args.length === 2) {
          return `${formatTerm(formula.left.args[0]!, options)} ∉ ${formatTerm(formula.left.args[1]!, options)}`;
        }
        return `¬${wrapNegatedFormula(formula.left, options)}`;
      }
      const shape = formulaShape(formula)!;
      // A guard as an antecedent sorts its variable for the consequent.
      return `${formulaOperand(formula.left, shape, "left", options)} → ${formulaOperand(formula.right, shape, "right", withGuardSorts(options, formula.left))}`;
    }
    case "forall": {
      const ordered = orderedQuantifier(formula.variable, formula.body, "forall");
      if (ordered) {
        const inner = withGuardSorts(options, { tag: "pred", pred: "Nat", args: [{ tag: "var", name: formula.variable }] });
        return `∀ ${formula.variable} ${ordered.token} ${formatTerm(ordered.bound, options)}, ${formatFormulaIn(ordered.body, inner, false)}`;
      }
      const bounded = boundedQuantifier(formula.variable, formula.body, "forall");
      if (bounded) {
        const inner = withGuardSorts(options, { tag: "pred", pred: "in", args: [{ tag: "var", name: formula.variable }, bounded.bound] });
        return `∀ ${formula.variable} ∈ ${formatTerm(bounded.bound, options)}, ${formatFormulaIn(bounded.body, inner, false)}`;
      }
      const prefix = quantifierPrefix(formula, "forall", options);
      if (prefix) return `${prefix.text} ${formatFormulaIn(prefix.body, prefix.options, false)}`;
      return `∀ ${formula.variable}, ${formatFormulaIn(formula.body, options, false)}`;
    }
    case "exists": {
      const ordered = orderedQuantifier(formula.variable, formula.body, "exists");
      if (ordered) {
        const inner = withGuardSorts(options, { tag: "pred", pred: "Nat", args: [{ tag: "var", name: formula.variable }] });
        return `∃ ${formula.variable} ${ordered.token} ${formatTerm(ordered.bound, options)}, ${formatFormulaIn(ordered.body, inner, false)}`;
      }
      const bounded = boundedQuantifier(formula.variable, formula.body, "exists");
      if (bounded) {
        const inner = withGuardSorts(options, { tag: "pred", pred: "in", args: [{ tag: "var", name: formula.variable }, bounded.bound] });
        return `∃ ${formula.variable} ∈ ${formatTerm(bounded.bound, options)}, ${formatFormulaIn(bounded.body, inner, false)}`;
      }
      const prefix = quantifierPrefix(formula, "exists", options);
      if (prefix) return `${prefix.text} ${formatFormulaIn(prefix.body, prefix.options, false)}`;
      return `∃ ${formula.variable}, ${formatFormulaIn(formula.body, options, false)}`;
    }
    case "and": case "or": case "iff": {
      const shape = formulaShape(formula)!;
      const token = formula.tag === "and" ? "∧" : formula.tag === "or" ? "∨" : "↔";
      return `${formulaOperand(formula.left, shape, "left", options)} ${token} ${formulaOperand(formula.right, shape, "right", options)}`;
    }
  }
}

/** Among notations for one target, the Unicode spelling is printed. */
function preferUnicode<T extends { readonly token: string }>(candidates: readonly T[]): T | undefined {
  return candidates.find(item => /[^\x00-\x7f]/u.test(item.token)) ?? candidates[0];
}

function predicateNotation(
  formula: Extract<Formula, { readonly tag: "pred" }>, options?: PrettyOptions,
): PrettyNotation | undefined {
  return preferUnicode((options?.notations ?? []).filter(notation => {
    if (notation.kind !== "predicate" || notation.target !== formula.pred || notation.fixity) return false;
    const leading = notation.leadingArguments ?? [];
    if (leading.some((argument, index) => !termEquals(argument, formula.args[index]!))) return false;
    return formula.args.length - leading.length === 2;
  }));
}

function boundedQuantifier(
  variable: string, body: Formula, kind: "forall" | "exists",
): { readonly bound: Term; readonly body: Formula } | undefined {
  const connective = kind === "forall" ? "imp" : "and";
  if (body.tag !== connective || body.left.tag !== "pred" || body.left.pred !== "in" ||
      body.left.args.length !== 2 || body.left.args[0]!.tag !== "var" ||
      body.left.args[0]!.name !== variable) return undefined;
  // `∀ x, x ∈ A → ⊥` reads as `∀ x, x ∉ A`, not as a bounded quantifier over ⊥.
  if (kind === "forall" && body.right.tag === "bottom") return undefined;
  return { bound: body.left.args[1]!, body: body.right };
}

function wrapNegatedFormula(formula: Formula, options?: PrettyOptions): string {
  return formula.tag === "eq" || formula.tag === "pred" || formula.tag === "bottom"
    ? formatFormula(formula, options) : `(${formatFormula(formula, options)})`;
}

