// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import test from "node:test";
import assert from "node:assert/strict";
import {
  KernelError, and, andElimLeft, andIntro, app, assume, axiom, bind, createZfKernel,
  createZfcKernel, createZfgKernel,
  ctor, definition, eq, exists, existsElim, existsIntro, forall, forallElim, formulaEquals,
  forallIntro, freeFormulaVariables, iff, iffElimLeft, iffIntro, imp, impElim, impIntro, induction,
  or, orElim, orIntroLeft, orIntroRight, pred, refl,
  substituteFormula, v, cantor, certifyE0Less, checkE0LessCertificate, compareE0,
  formatE0, omega, omegaPow, ordinalNat,
  wellFoundedInduction,
} from "../src/index.ts";

test("proves universally quantified reflexivity", () => {
  const kernel = createZfgKernel();
  const statement = forall("x", eq(v("x"), v("x")));
  kernel.addTheorem("refl", statement, forallIntro("x", refl(v("x"))));
  assert.deepEqual(kernel.theorems.get("refl"), statement);
});

test("checks implication introduction against the active context", () => {
  const kernel = createZfgKernel();
  const member = pred("in", v("x"), app("omega"));
  kernel.addTheorem("id", forall("x", imp(member, member)),
    forallIntro("x", impIntro(member, assume(member))));
  assert.throws(() => kernel.checkProof(assume(member)), KernelError);
});

test("free variables survive sibling quantifiers with shadowing names", () => {
  const formula = and(
    pred("in", v("x"), v("A")),
    forall("x", exists("A", pred("in", v("x"), v("A")))),
  );
  assert.deepEqual([...freeFormulaVariables(formula)].sort(), ["A", "x"]);

  const seeded = new Set(["already"]);
  assert.equal(freeFormulaVariables(formula, seeded), seeded);
  assert.deepEqual([...seeded].sort(), ["A", "already", "x"]);
});

test("universal introduction rejects a variable hidden by a sibling quantifier", () => {
  const kernel = createZfgKernel();
  const hiddenFreeX = and(
    pred("in", v("x"), app("omega")),
    forall("x", eq(v("x"), v("x"))),
  );
  const invalid = forallIntro("x", impIntro(
    hiddenFreeX,
    forallIntro("x", andElimLeft(assume(hiddenFreeX))),
  ));
  assert.throws(() => kernel.checkProof(invalid), /Cannot generalize x/);
});

test("closedness and definition guards see variables hidden by sibling quantifiers", () => {
  const kernel = createZfgKernel();
  const hiddenFreeX = and(
    pred("in", v("x"), app("omega")),
    forall("x", eq(v("x"), v("x"))),
  );
  const identity = impIntro(hiddenFreeX, assume(hiddenFreeX));
  assert.throws(() => kernel.addAxiom("open.axiom", hiddenFreeX), /free variables: x/);
  assert.throws(() => kernel.addTheorem("open.theorem", imp(hiddenFreeX, hiddenFreeX), identity), /free variables: x/);
  assert.throws(() => kernel.definePredicate("openPredicate", [], hiddenFreeX), /undeclared variables: x/);
  assert.throws(() => kernel.defineSubset(
    "openSubset", [], "element", app("omega"), hiddenFreeX,
  ), /undeclared variables: x/);
});

test("checks primitive conjunction, disjunction, equivalence, and existence rules", () => {
  const kernel = createZfgKernel();
  const p = eq(app("empty"), app("empty"));
  const q = eq(app("omega"), app("omega"));
  assert.deepEqual(kernel.checkProof(andIntro(refl(app("empty")), refl(app("omega")))), and(p, q));
  assert.deepEqual(kernel.checkProof(andElimLeft(andIntro(refl(app("empty")), refl(app("omega"))))), p);
  assert.deepEqual(kernel.checkProof(orIntroLeft(refl(app("empty")), q)), or(p, q));

  const disjunction = orIntroLeft(refl(app("empty")), q);
  const joined = orElim(
    disjunction,
    orIntroLeft(assume(p), q),
    orIntroRight(p, assume(q)),
  );
  assert.deepEqual(kernel.checkProof(joined), or(p, q));

  const equivalence = iffIntro(impIntro(p, assume(p)), impIntro(p, assume(p)));
  assert.deepEqual(kernel.checkProof(equivalence), iff(p, p));
  assert.deepEqual(kernel.checkProof(impElim(iffElimLeft(equivalence), refl(app("empty")))), p);

  const body = eq(v("z"), v("z"));
  const existential = existsIntro("z", body, app("empty"), refl(app("empty")));
  assert.deepEqual(kernel.checkProof(existential), exists("z", body));
  assert.deepEqual(kernel.checkProof(existsElim(existential, "w", refl(app("omega")))), q);
  assert.throws(() => kernel.checkProof(existsElim(existential, "w", refl(v("w")))), /escapes/);
  kernel.addAxiom("universal.reflexivity", forall("w", eq(v("w"), v("w"))));
  const hiddenEscape = andIntro(
    assume(eq(v("w"), v("w"))),
    axiom("universal.reflexivity"),
  );
  assert.throws(() => kernel.checkProof(existsElim(existential, "w", hiddenEscape)), /escapes/);
  assert.throws(() => kernel.checkProof(andElimLeft(refl(app("empty")))), /conjunction/);
});

test("rejects forged theorem conclusions", () => {
  const kernel = createZfgKernel();
  assert.throws(() => kernel.addTheorem(
    "forged",
    forall("x", eq(v("x"), app("empty"))),
    forallIntro("x", refl(v("x"))),
  ), /expected/);
});

test("conservative function definitions generate equations", () => {
  const kernel = createZfgKernel();
  kernel.defineFunction("diag", ["x"], app("pair", v("x"), v("x")));
  const equation = forall("x", eq(app("diag", v("x")), app("pair", v("x"), v("x"))));
  assert.deepEqual(kernel.checkProof(definition("diag")), equation);
});

test("unique description and set-well-founded recursion are guarded conservative events", () => {
  const kernel = createZfgKernel();
  const relation = eq(v("value"), v("x"));
  const uniquenessPremise = eq(v("other"), v("x"));
  const existsUnique = forallIntro("x", existsIntro("value", and(
    relation,
    forall("other", imp(substituteFormula(relation, "value", v("other")), eq(v("other"), v("value")))),
  ), v("x"), andIntro(
    refl(v("x")),
    forallIntro("other", impIntro(uniquenessPremise, assume(uniquenessPremise))),
  )));
  const selected = kernel.defineUniqueFunction({
    name: "selected", parameters: ["x"], value: "value", relation, existsUnique,
  });
  assert.equal(selected.kind, "unique-choice");

  const domainSubset = forall("member", imp(pred("in", v("member"), v("subset")), pred("in", v("member"), v("A"))));
  const wellFounded = forallIntro("A", forallIntro("subset", impIntro(domainSubset,
    forallElim(axiom("set.foundation"), v("subset")))));
  const recursive = kernel.defineWellFoundedSetFunction({
    name: "rankOn", parameters: ["A"], variable: "x", predecessor: "y", history: "h",
    domain: v("A"), precedes: pred("in", v("y"), v("x")), step: app("powerset", v("h")), wellFounded,
  });
  assert.equal(recursive.kind, "well-founded-set-recursive");
  assert.ok(recursive.properties.has("history.membership"));
  assert.ok(recursive.properties.has("equation.direct"));
  assert.equal(kernel.recursiveFunctions.has("rankOn"), false);
  assert.deepEqual(kernel.foundationReport().schemaInstances.uniqueChoice, ["selected"]);
  assert.deepEqual(kernel.foundationReport().schemaInstances.wellFoundedRecursion, ["rankOn"]);
});

test("ordinary definitions reject recursion without a certificate", () => {
  const kernel = createZfgKernel();
  assert.throws(
    () => kernel.defineFunction("bad", ["x"], app("bad", v("x"))),
    /well-founded recursion certificate/,
  );
  assert.equal(kernel.functions.has("bad"), false);
});

test("fast execution unfolds admitted definitions without constructing proofs", () => {
  const kernel = createZfgKernel();
  kernel.defineFunction("wrap", ["x"], app("pair", v("x"), v("x")));
  const input = app("wrap", app("empty"));
  const fast = kernel.evaluateFastWithStats(input);
  const certified = kernel.evaluateCertified(input);
  assert.deepEqual(fast.value, certified.value);
  assert.equal(fast.stats.reductions, 1);
  assert.deepEqual(fast.value, app("pair", app("empty"), app("empty")));
  assert.deepEqual(kernel.checkProof(certified.proof), eq(input, fast.value));
});

test("Separation definitions produce membership characterizations", () => {
  const kernel = createZfgKernel();
  kernel.defineSubset(
    "diagonalMembers",
    ["A"],
    "x",
    v("A"),
    eq(v("x"), app("pair", v("x"), v("x"))),
  );
  assert.equal(kernel.definitions.get("diagonalMembers")?.kind, "separation");
  assert.equal(kernel.checkProof(definition("diagonalMembers", "membership")).tag, "forall");
});

test("Replacement reifies an executable operation and exposes its bridge", () => {
  const kernel = createZfgKernel();
  kernel.defineFunction("embed", ["x"], app("singleton", v("x")));
  const closure = forall("x", imp(
    pred("in", v("x"), app("omega")),
    pred("in", app("embed", v("x")), app("powerset", app("omega"))),
  ));
  kernel.addAxiom("embed.closure", closure);
  kernel.reifyUnaryOperation({
    name: "Embed",
    operation: "embed",
    domain: app("omega"),
    codomain: app("powerset", app("omega")),
    variable: "x",
    closure: axiom("embed.closure"),
  });
  const bridge = kernel.checkProof(definition("Embed", "application"));
  assert.equal(bridge.tag, "forall");
  const membership = kernel.checkProof(definition("Embed", "membership"));
  assert.equal(membership.tag, "forall");
});

test("Replacement rejects an unrelated closure proof", () => {
  const kernel = createZfgKernel();
  kernel.defineFunction("embed", ["x"], app("singleton", v("x")));
  assert.throws(() => kernel.reifyUnaryOperation({
    name: "Embed",
    operation: "embed",
    domain: app("omega"),
    codomain: app("powerset", app("omega")),
    variable: "x",
    closure: axiom("set.empty"),
  }), /wrong conclusion/);
});

test("ZF, ZFC, and ZFG expose distinct audited foundation profiles", () => {
  const zf = createZfKernel();
  const zfc = createZfcKernel();
  const zfg = createZfgKernel();
  assert.equal(zf.capabilities.setTheory, "ZF");
  assert.equal(zfc.capabilities.setTheory, "ZFC");
  assert.equal(zfg.capabilities.setTheory, "ZFG");
  assert.equal(zf.axioms.has("set.choice"), false);
  assert.equal(zfc.axioms.has("set.choice"), true);
  assert.equal(zfc.axioms.has("set.globalChoice"), false);
  assert.equal(zfg.axioms.has("set.globalChoice"), true);
  for (const name of ["set.extensionality", "set.pairing", "set.union", "set.powerset", "set.infinity", "set.foundation"]) {
    assert.equal(zf.axioms.has(name), true, `missing ${name}`);
  }
  assert.notEqual(zf.digest(), zfc.digest());
  const report = zfg.foundationReport();
  assert.equal(report.profile, "ZFG");
  assert.deepEqual(report.schemaInstances.datatype, ["Naturals"]);
  assert.equal(report.axioms.includes("set.globalChoice"), true);
});

test("general Replacement accepts a proved functional relation with parameters", () => {
  const kernel = createZfKernel();
  const relation = eq(v("y"), app("pair", v("x"), v("tag")));
  const functionality = forall("tag", forall("x", imp(
    pred("in", v("x"), app("omega")),
    exists("y", and(
      relation,
      forall("y_other", imp(
        eq(v("y_other"), app("pair", v("x"), v("tag"))), eq(v("y_other"), v("y")),
      )),
    )),
  )));
  kernel.addAxiom("tagged.functional", functionality);
  const image = kernel.defineReplacement({
    name: "taggedImage",
    parameters: ["tag"],
    domain: app("omega"),
    input: "x",
    output: "y",
    relation,
    functionality: axiom("tagged.functional"),
  });
  assert.equal(image.kind, "replacement");
  assert.equal(kernel.functions.get("taggedImage"), 1);
  assert.equal(kernel.checkProof(definition("taggedImage", "membership")).tag, "forall");
});

test("capture-avoiding substitution renames binders", () => {
  const formula = forall("y", eq(v("x"), v("y")));
  const result = substituteFormula(formula, "x", v("y"));
  assert.equal(result.tag, "forall");
  assert.notEqual(result.variable, "y");
});

test("capture-avoiding substitution accounts for free names beside shadowing quantifiers", () => {
  const formula = forall("x", and(
    pred("in", v("z"), v("x")),
    and(
      pred("in", v("x_1"), v("x")),
      forall("x_1", eq(v("x_1"), v("x_1"))),
    ),
  ));
  const result = substituteFormula(formula, "z", v("x"));
  assert.equal(result.tag, "forall");
  assert.equal(result.variable, "x_2");
  assert.deepEqual([...freeFormulaVariables(result)].sort(), ["x", "x_1"]);
});

test("formula comparison respects alpha-equivalence", () => {
  const kernel = createZfgKernel();
  const statement = forall("z", eq(v("z"), v("z")));
  kernel.addTheorem("alpha", statement, forallIntro("x", refl(v("x"))));
  assert.deepEqual(kernel.theorems.get("alpha"), statement);
  assert.equal(formulaEquals(
    forall("x", eq(v("x"), v("z"))),
    forall("y", eq(v("y"), v("z"))),
  ), true);
  assert.equal(formulaEquals(
    forall("x", eq(v("x"), v("z"))),
    forall("z", eq(v("z"), v("z"))),
  ), false);
  assert.equal(formulaEquals(
    forall("x", forall("x", eq(v("x"), v("x")))),
    forall("a", forall("b", eq(v("b"), v("b")))),
  ), true);
  assert.equal(formulaEquals(
    forall("x", forall("x", eq(v("x"), v("x")))),
    forall("a", forall("b", eq(v("a"), v("a")))),
  ), false);
});

test("kernel snapshots have deterministic digests", () => {
  assert.equal(createZfgKernel().digest(), createZfgKernel().digest());
});

test("cached kernel digests are invalidated by environment changes and isolated across forks", () => {
  const kernel = createZfgKernel();
  const initial = kernel.digest();
  assert.equal(kernel.digest(), initial);

  kernel.declareFunction("freshDigestWitness", 0);
  const extended = kernel.digest();
  assert.notEqual(extended, initial);

  const fork = kernel.fork();
  assert.equal(fork.digest(), extended);
  fork.declarePredicate("forkOnlyDigestWitness", 0);
  assert.notEqual(fork.digest(), extended);
  assert.equal(kernel.digest(), extended);
});

test("admits structurally recursive functions and evaluates them", () => {
  const kernel = createZfgKernel();
  kernel.defineStructuralFunction({
    name: "plus",
    parameters: ["x", "y"],
    datatype: "Naturals",
    decreasingParameter: 0,
    equations: [
      { patterns: [ctor("zero"), bind("y")], body: v("y") },
      {
        patterns: [ctor("succ", bind("x")), bind("y")],
        body: app("succ", app("plus", v("x"), v("y"))),
      },
    ],
  });
  const zero = app("zero");
  const one = app("succ", zero);
  const two = app("succ", one);
  const three = app("succ", two);
  assert.deepEqual(kernel.evaluate(app("plus", two, one)), three);
  const certified = kernel.evaluateCertified(app("plus", two, one));
  assert.deepEqual(kernel.checkProof(certified.proof), eq(app("plus", two, one), three));
  assert.equal(kernel.definitions.get("plus")?.kind, "recursive");
});

test("rejects recursive calls that do not structurally decrease", () => {
  const kernel = createZfgKernel();
  assert.throws(() => kernel.defineStructuralFunction({
    name: "loop",
    parameters: ["x"],
    datatype: "Naturals",
    decreasingParameter: 0,
    equations: [
      { patterns: [ctor("zero")], body: app("zero") },
      { patterns: [ctor("succ", bind("x"))], body: app("loop", app("succ", v("x"))) },
    ],
  }), /structurally smaller/);
  assert.equal(kernel.functions.has("loop"), false);
});

test("checks structural induction over an inductive set", () => {
  const kernel = createZfgKernel();
  const motive = eq(v("n"), v("n"));
  const statement = forall("n", imp(pred("Nat", v("n")), motive));
  kernel.addTheorem("nat.reflexive.by_induction", statement, induction(
    "Naturals",
    "n",
    motive,
    [
      { constructor: "zero", fields: [], proof: refl(app("zero")) },
      { constructor: "succ", fields: ["k"], proof: refl(app("succ", v("k"))) },
    ],
  ));
  assert.deepEqual(kernel.theorems.get("nat.reflexive.by_induction"), statement);
});

test("structural induction requires constructor fields fresh from parameters and motives", () => {
  const kernel = createZfgKernel();
  kernel.declareDatatype({
    name: "BoxFamily",
    predicate: "Box",
    parameters: ["Carrier"],
    constructors: [{
      name: "box",
      arity: 1,
      recursiveFields: [],
      parameterFields: [{ field: 0, parameter: 0 }],
    }],
  });
  const motive = eq(v("item"), app("box", v("A")));
  const invalid = induction("BoxFamily", "item", motive, [{
    constructor: "box",
    fields: ["A"],
    proof: refl(app("box", v("A"))),
  }], [v("A")]);
  assert.throws(() => kernel.checkProof(invalid), /fresh.*parameter.*motive/i);
});

test("executes and independently checks epsilon_0 comparisons", () => {
  const w = omega();
  const w2 = cantor(ordinalNat(1), 2, ordinalNat(3));
  const ww = omegaPow(w);
  assert.equal(compareE0(ordinalNat(17), w), -1);
  assert.equal(compareE0(w, w2), -1);
  assert.equal(compareE0(w2, ww), -1);
  assert.equal(formatE0(w2), "w*2 + 3");
  const certificate = certifyE0Less(w2, ww);
  assert.equal(checkE0LessCertificate(certificate), true);
  assert.equal(checkE0LessCertificate({ ...certificate, digest: "forged" }), false);
  const cyclic = { terms: [] as unknown[], finite: 0n };
  cyclic.terms.push({ exponent: cyclic, coefficient: 1n });
  assert.throws(() => compareE0(cyclic as never, w), /Cyclic/);
});

test("admits recursion from exact well-founded measure certificates", () => {
  const kernel = createZfgKernel();
  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  kernel.addAxiom("e0.well_founded", pred("wellFoundedOn", relation, domain));
  kernel.addAxiom("nat.in_e0", forall("x", pred("in", v("x"), domain)));
  kernel.addAxiom("nat.predecessor_descends", forall("n",
    pred("relates", relation, v("n"), app("succ", v("n"))),
  ));
  kernel.defineWellFoundedFunction({
    name: "countdown",
    parameters: ["x"],
    coverageDatatype: "Naturals",
    coverageParameter: 0,
    relation,
    domain,
    measure: v("x"),
    wellFounded: axiom("e0.well_founded"),
    measureInDomain: axiom("nat.in_e0"),
    decreases: [axiom("nat.predecessor_descends")],
    equations: [
      { patterns: [ctor("zero")], body: app("zero") },
      { patterns: [ctor("succ", bind("n"))], body: app("countdown", v("n")) },
    ],
  });
  const three = app("succ", app("succ", app("succ", app("zero"))));
  const certified = kernel.evaluateCertified(app("countdown", three));
  assert.deepEqual(certified.value, app("zero"));
  assert.deepEqual(kernel.checkProof(certified.proof), eq(app("countdown", three), app("zero")));
  assert.equal(kernel.definitions.get("countdown")?.kind, "well-founded-recursive");
});

test("rejects a forged ordinal decrease certificate", () => {
  const kernel = createZfgKernel();
  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  kernel.addAxiom("e0.well_founded", pred("wellFoundedOn", relation, domain));
  kernel.addAxiom("nat.in_e0", forall("x", pred("in", v("x"), domain)));
  assert.throws(() => kernel.defineWellFoundedFunction({
    name: "loopByClaim",
    parameters: ["x"],
    coverageDatatype: "Naturals",
    coverageParameter: 0,
    relation,
    domain,
    measure: v("x"),
    wellFounded: axiom("e0.well_founded"),
    measureInDomain: axiom("nat.in_e0"),
    decreases: [axiom("nat.in_e0")],
    equations: [
      { patterns: [ctor("zero")], body: app("zero") },
      { patterns: [ctor("succ", bind("n"))], body: app("loopByClaim", app("succ", v("n"))) },
    ],
  }), /Decrease proof 0/);
  assert.equal(kernel.functions.has("loopByClaim"), false);
});

test("checks induction over a certified well-founded relation", () => {
  const kernel = createZfgKernel();
  const relation = app("epsilon0.less");
  const domain = app("epsilon0");
  const wf = pred("wellFoundedOn", relation, domain);
  kernel.addAxiom("e0.well_founded", wf);
  const motive = eq(v("a"), v("a"));
  const ih = forall("b", imp(
    and(pred("in", v("b"), domain), pred("relates", relation, v("b"), v("a"))),
    eq(v("b"), v("b")),
  ));
  const step = forallIntro("a", impIntro(
    pred("in", v("a"), domain),
    impIntro(ih, refl(v("a"))),
  ));
  const statement = forall("a", imp(pred("in", v("a"), domain), motive));
  kernel.addTheorem("e0.reflexive.by_induction", statement, wellFoundedInduction(
    relation, domain, "a", "b", motive, axiom("e0.well_founded"), step,
  ));
  assert.deepEqual(kernel.theorems.get("e0.reflexive.by_induction"), statement);
});
