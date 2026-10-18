import {
  and, andElimLeft, andElimRight, andIntro, app, assume, axiom, bind, bottom,
  congr, createZfgKernel, ctor, definition, dne, eq, eqElim, exists, existsElim,
  existsIntro, falseElim, forall, forallElim, forallIntro, iff, iffElimLeft,
  iffElimRight, iffIntro, imp, impElim, impIntro, induction, or, orElim,
  orIntroLeft, orIntroRight, pred, refl, symm, theorem, trans, v, nat, not,
  foralls, rationalClassCompute,
  wellFoundedInduction,
  type Formula, type Kernel, type Proof,
} from "../src/index.ts";

export interface ConformanceCase {
  readonly opcode: number;
  readonly rule: string;
  readonly theorem: string;
}

export interface ConformanceFixture {
  readonly kernel: Kernel;
  readonly cases: readonly ConformanceCase[];
  readonly securitySeeds: Readonly<{
    forallFreshness: string;
    inductionFreshness: string;
  }>;
}

/** Build the fixed logical environment shared by every G17M conformance vector. */
export function buildConformanceFixture(): ConformanceFixture {
  const kernel = createZfgKernel();
  const cases: ConformanceCase[] = [];
  const empty = app("empty");
  const omega = app("omega");
  const truth = eq(empty, empty);
  const omegaTruth = eq(omega, omega);
  const add = (opcode: number, rule: string, statement: Formula, proof: Proof): void => {
    const name = `conformance.op${String(opcode).padStart(2, "0")}.${rule}`;
    kernel.addTheorem(name, statement, proof);
    cases.push({ opcode, rule, theorem: name });
  };

  kernel.addAxiom("conformance.truth", truth);
  kernel.addAxiom("conformance.absurd", bottom);
  kernel.addTheorem("conformance.base", truth, refl(empty));
  kernel.defineFunction("conformance.identity", ["x"], v("x"));
  kernel.defineStructuralFunction({
    name: "conformance.plus",
    parameters: ["x", "y"],
    datatype: "Naturals",
    decreasingParameter: 0,
    equations: [
      { patterns: [ctor("zero"), bind("y")], body: v("y") },
      { patterns: [ctor("succ", bind("x")), bind("y")], body: app("succ", app("conformance.plus", v("x"), v("y"))) },
    ],
  });

  add(0, "assumption", imp(truth, truth), impIntro(truth, assume(truth)));
  add(1, "axiom", truth, axiom("conformance.truth"));
  add(2, "theorem", truth, theorem("conformance.base"));
  add(3, "definition", forall("x", eq(app("conformance.identity", v("x")), v("x"))), definition("conformance.identity"));
  add(4, "reflexivity", truth, refl(empty));
  add(5, "symmetry", truth, symm(refl(empty)));
  add(6, "transitivity", truth, trans(refl(empty), refl(empty)));
  add(7, "congruence", eq(app("singleton", empty), app("singleton", empty)), congr("singleton", refl(empty)));
  add(8, "implication-introduction", imp(truth, truth), impIntro(truth, assume(truth)));
  add(9, "implication-elimination", truth, impElim(impIntro(truth, assume(truth)), refl(empty)));
  add(10, "universal-introduction", forall("x", eq(v("x"), v("x"))), forallIntro("x", refl(v("x"))));
  add(11, "universal-elimination", truth, forallElim(forallIntro("x", refl(v("x"))), empty));
  const natMotive = eq(v("n"), v("n"));
  add(12, "datatype-induction", forall("n", imp(pred("Nat", v("n")), natMotive)), induction(
    "Naturals", "n", natMotive, [
      { constructor: "zero", fields: [], proof: refl(app("zero")) },
      { constructor: "succ", fields: ["k"], proof: refl(app("succ", v("k"))) },
    ],
  ));
  add(13, "equality-elimination", truth, eqElim(refl(empty), "z", eq(v("z"), empty), refl(empty)));
  add(14, "conjunction-introduction", and(truth, omegaTruth), andIntro(refl(empty), refl(omega)));
  add(15, "conjunction-left", truth, andElimLeft(andIntro(refl(empty), refl(omega))));
  add(16, "conjunction-right", omegaTruth, andElimRight(andIntro(refl(empty), refl(omega))));
  add(17, "disjunction-left", or(truth, omegaTruth), orIntroLeft(refl(empty), omegaTruth));
  add(18, "disjunction-right", or(truth, omegaTruth), orIntroRight(truth, refl(omega)));
  add(19, "disjunction-elimination", truth, orElim(
    orIntroLeft(refl(empty), omegaTruth), assume(truth), refl(empty),
  ));
  const identity = impIntro(truth, assume(truth));
  add(20, "equivalence-introduction", iff(truth, truth), iffIntro(identity, identity));
  add(21, "equivalence-forward", imp(truth, truth), iffElimLeft(iffIntro(identity, identity)));
  add(22, "equivalence-backward", imp(truth, truth), iffElimRight(iffIntro(identity, identity)));
  add(23, "existential-introduction", exists("x", eq(v("x"), v("x"))),
    existsIntro("x", eq(v("x"), v("x")), empty, refl(empty)));
  const existential = existsIntro("x", eq(v("x"), v("x")), empty, refl(empty));
  add(24, "existential-elimination", truth, existsElim(existential, "w", refl(empty)));
  add(25, "false-elimination", truth, falseElim(truth, axiom("conformance.absurd")));
  const notTruth = imp(truth, bottom);
  add(26, "double-negation-elimination", truth,
    dne(truth, impIntro(notTruth, impElim(assume(notTruth), refl(empty)))));

  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  const wfMotive = eq(v("x"), v("x"));
  const ih = forall("y", imp(and(
    pred("in", v("y"), domain), pred("relates", relation, v("y"), v("x")),
  ), eq(v("y"), v("y"))));
  const wfStep = forall("x", imp(pred("in", v("x"), domain), imp(ih, wfMotive)));
  kernel.addAxiom("conformance.well-founded", pred("wellFoundedOn", relation, domain));
  kernel.addAxiom("conformance.well-founded-step", wfStep);
  add(27, "well-founded-induction", forall("x", imp(pred("in", v("x"), domain), wfMotive)),
    wellFoundedInduction(relation, domain, "x", "y", wfMotive,
      axiom("conformance.well-founded"), axiom("conformance.well-founded-step")));

  const two = app("succ", app("succ", app("zero")));
  const three = app("succ", two);
  const five = app("succ", app("succ", three));
  const computation = eq(app("conformance.plus", two, three), five);
  add(28, "ground-computation", computation,
    kernel.proveComputation(app("conformance.plus", two, three), five));

  // The conformance fixture's inconsistent axiom is confined to protocol tests.
  // The production library derives this criterion from the quotient construction.
  const natAdd = "Grace.Core.Nat.Rec.add";
  const natMul = "Grace.Core.Nat.Rec.mul";
  const rationalClass = "Grace.Cumulus.Rat.Operations.rationalClass";
  kernel.defineStructuralFunction({ name: natAdd, parameters: ["x", "y"], datatype: "Naturals",
    decreasingParameter: 0, equations: [
      { patterns: [ctor("zero"), bind("y")], body: v("y") },
      { patterns: [ctor("succ", bind("x")), bind("y")], body: app("succ", app(natAdd, v("x"), v("y"))) },
    ] });
  kernel.defineStructuralFunction({ name: natMul, parameters: ["x", "y"], datatype: "Naturals",
    decreasingParameter: 0, equations: [
      { patterns: [ctor("zero"), bind("y")], body: app("zero") },
      { patterns: [ctor("succ", bind("x")), bind("y")], body: app(natAdd, v("y"), app(natMul, v("x"), v("y"))) },
    ] });
  kernel.declareFunction(rationalClass, 3);
  const [a, b, m, c, d, n] = ["a", "b", "m", "c", "d", "n"].map(v);
  const mul = (x: ReturnType<typeof v>, y: ReturnType<typeof v>) => app(natMul, x, y);
  const plus = (x: ReturnType<typeof v>, y: ReturnType<typeof v>) => app(natAdd, x, y);
  const criterion = foralls(["a", "b", "m", "c", "d", "n"],
    [a, b, m, c, d, n].map(x => pred("Nat", x)).concat([
      not(eq(m, nat(0))), not(eq(n, nat(0))),
      eq(plus(mul(n, a), mul(m, d)), plus(mul(m, c), mul(n, b))),
    ]).reduceRight<Formula>((body, premise) => imp(premise, body),
      eq(app(rationalClass, a, b, m), app(rationalClass, c, d, n))));
  kernel.addTheorem(`${rationalClass}.eq`, criterion,
    falseElim(criterion, axiom("conformance.absurd")));
  const leftClass = app(rationalClass, nat(8), nat(0), nat(3));
  const rightClass = app(rationalClass, nat(16), nat(0), nat(6));
  add(29, "rational-class-computation", eq(leftClass, rightClass),
    rationalClassCompute(leftClass, rightClass));

  const hidden = and(pred("in", v("x"), omega), forall("x", eq(v("x"), v("x"))));
  const forallFreshness = "conformance.security.forall-freshness";
  kernel.addTheorem(forallFreshness, forall("x", imp(hidden, forall("z", truth))),
    forallIntro("x", impIntro(hidden, forallIntro("z", refl(empty)))));

  kernel.declareDatatype({
    name: "ConformanceBoxFamily",
    predicate: "ConformanceBox",
    parameters: ["Carrier"],
    constructors: [{ name: "conformance.box", arity: 1, recursiveFields: [] }],
  });
  const inductionFreshness = "conformance.security.induction-freshness";
  const constantMotive = eq(v("A"), v("A"));
  const inductionProof = induction("ConformanceBoxFamily", "item", constantMotive, [{
    constructor: "conformance.box", fields: ["field"], proof: refl(v("A")),
  }], [v("Carrier")]);
  kernel.addTheorem(inductionFreshness,
    forall("A", forall("Carrier", forall("item", imp(
      pred("ConformanceBox", v("Carrier"), v("item")), constantMotive,
    )))), forallIntro("A", forallIntro("Carrier", inductionProof)));

  return { kernel, cases, securitySeeds: { forallFreshness, inductionFreshness } };
}
