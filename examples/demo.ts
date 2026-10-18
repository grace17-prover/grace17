import {
  app, assume, bind, createZfgKernel, ctor, definition, eq, forall, forallElim,
  forallIntro, imp, impIntro, pred, refl, v, cantor, certifyE0Less,
  checkE0LessCertificate, formatE0, omega, omegaPow, ordinalNat,
} from "../src/index.ts";

const kernel = createZfgKernel();

kernel.addTheorem(
  "equality.reflexive",
  forall("x", eq(v("x"), v("x"))),
  forallIntro("x", refl(v("x"))),
);

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

const numeral = (n: number) => {
  let result = app("zero");
  for (let index = 0; index < n; index += 1) result = app("succ", result);
  return result;
};
const sum = kernel.evaluate(app("plus", numeral(2), numeral(3)));

const ordinalMeasure = cantor(ordinalNat(1), 2, ordinalNat(17));
const ordinalBound = omegaPow(omega());
const ordinalCertificate = certifyE0Less(ordinalMeasure, ordinalBound);

const p = pred("in", v("x"), app("omega"));
kernel.addTheorem(
  "implication.identity",
  forall("x", imp(p, p)),
  forallIntro("x", impIntro(p, assume(p))),
);

kernel.defineFunction("twice", ["x"], app("pair", v("x"), v("x")));

const closure = forall("x", imp(
  pred("in", v("x"), app("omega")),
  pred("in", app("twice", v("x")), app("powerset", app("powerset", app("omega")))),
));
kernel.addAxiom("demo.twice.closure", closure);
kernel.reifyUnaryOperation({
  name: "Twice",
  operation: "twice",
  domain: app("omega"),
  codomain: app("powerset", app("powerset", app("omega"))),
  variable: "x",
  closure: { rule: "axiom", name: "demo.twice.closure" },
});

const bridge = definition("Twice", "application");
kernel.addTheorem(
  "Twice.at_zero",
  imp(
    pred("in", app("empty"), app("omega")),
    eq(app("apply", app("Twice"), app("empty")), app("twice", app("empty"))),
  ),
  forallElim(bridge, app("empty")),
);

console.log("GRACE17 seed kernel");
console.log(`  functions:   ${kernel.functions.size}`);
console.log(`  predicates:  ${kernel.predicates.size}`);
console.log(`  axioms:      ${kernel.axioms.size}`);
console.log(`  definitions: ${kernel.definitions.size}`);
console.log(`  theorems:    ${kernel.theorems.size}`);
console.log(`  2 + 3:       ${JSON.stringify(sum)}`);
console.log(`  ordinal:     ${formatE0(ordinalMeasure)} < ${formatE0(ordinalBound)}`);
console.log(`  certificate: ${checkE0LessCertificate(ordinalCertificate) ? "checked" : "rejected"}`);
console.log(`  digest:      ${kernel.digest()}`);
