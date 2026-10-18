import { performance } from "node:perf_hooks";
import {
  all, app, assume, at, axiom, bind, createZfgKernel, ctor, definition, eq,
  foralls, given, imp, impElim, induction, pred, settle, v, type Formula,
  type Kernel, type Proof, type Term,
} from "../src/index.ts";

export interface CheckedExample {
  readonly name: string;
  readonly statement: Formula;
  readonly proof: Proof;
  readonly checkMilliseconds: number;
}

export interface ProofSuite {
  readonly kernel: Kernel;
  readonly examples: readonly CheckedExample[];
}

/** Three proofs used as an ergonomics and performance acceptance suite. */
export function buildProofSuite(): ProofSuite {
  const kernel = createZfgKernel();
  const examples: CheckedExample[] = [];
  const zero = app("zero");

  kernel.defineStructuralFunction({
    name: "plus",
    parameters: ["x", "y"],
    datatype: "Naturals",
    decreasingParameter: 0,
    equations: [
      { patterns: [ctor("zero"), bind("y")], body: v("y") },
      { patterns: [ctor("succ", bind("x")), bind("y")], body: app("succ", app("plus", v("x"), v("y"))) },
    ],
  });

  const check = (name: string, statement: Formula, proof: Proof): void => {
    const start = performance.now();
    kernel.addTheorem(name, statement, proof);
    examples.push({ name, statement, proof, checkMilliseconds: performance.now() - start });
  };

  // 1. Right identity is not a defining equation because plus recurses on its
  // first argument. It therefore exercises induction and rewriting.
  const rightUnitMotive = eq(app("plus", v("n"), zero), v("n"));
  const rightUnit = induction("Naturals", "n", rightUnitMotive, [
    {
      constructor: "zero",
      fields: [],
      proof: settle(kernel, eq(app("plus", zero, zero), zero), {
        using: [definition("plus", "equation.0")],
      }),
    },
    {
      constructor: "succ",
      fields: ["k"],
      proof: settle(kernel,
        eq(app("plus", app("succ", v("k")), zero), app("succ", v("k"))), {
          using: [
            definition("plus", "equation.1"),
            assume(eq(app("plus", v("k"), zero), v("k"))),
          ],
          assumptions: [eq(app("plus", v("k"), zero), v("k"))],
        }),
    },
  ]);
  check(
    "plus.right_unit",
    foralls(["n"], imp(pred("Nat", v("n")), rightUnitMotive)),
    rightUnit,
  );

  // 2. Associativity exposes the main equational-proof experience. `calc`
  // chains checked equalities; `equation` specializes defining clauses.
  const associativityAt = (n: Term): Formula => eq(
    app("plus", app("plus", n, v("y")), v("z")),
    app("plus", n, app("plus", v("y"), v("z"))),
  );
  const assocMotive = associativityAt(v("n"));
  const assoc = all(["y", "z"], induction("Naturals", "n", assocMotive, [
    {
      constructor: "zero",
      fields: [],
      proof: settle(kernel, associativityAt(zero), {
        using: [definition("plus", "equation.0")],
      }),
    },
    {
      constructor: "succ",
      fields: ["k"],
      proof: settle(kernel, associativityAt(app("succ", v("k"))), {
        using: [definition("plus", "equation.1"), assume(associativityAt(v("k")))],
        assumptions: [associativityAt(v("k"))],
      }),
    },
  ]));
  check(
    "plus.associative",
    foralls(["y", "z", "n"], imp(pred("Nat", v("n")), assocMotive)),
    assoc,
  );

  // 3. A Replacement graph computes exactly like its native operation. This
  // crosses the bridge between computation and set theory.
  kernel.defineFunction("doubleton", ["x"], app("pair", v("x"), v("x")));
  const closure = foralls(["x"], imp(
    pred("in", v("x"), app("omega")),
    pred("in", app("doubleton", v("x")), app("powerset", app("powerset", app("omega")))),
  ));
  kernel.addAxiom("doubleton.closure", closure);
  kernel.reifyUnaryOperation({
    name: "Doubleton",
    operation: "doubleton",
    domain: app("omega"),
    codomain: app("powerset", app("powerset", app("omega"))),
    variable: "x",
    closure: axiom("doubleton.closure"),
  });
  const member = pred("in", v("x"), app("omega"));
  const graphGoal = eq(app("apply", app("Doubleton"), v("x")), app("pair", v("x"), v("x")));
  const graphStatement = foralls(["x"], imp(member, graphGoal));
  const graphProof = all(["x"], given([member], settle(kernel, graphGoal, {
    using: [
      impElim(at(definition("Doubleton", "application"), v("x")), assume(member)),
      definition("doubleton"),
    ],
    assumptions: [member],
  })));
  check("Doubleton.computes", graphStatement, graphProof);

  return { kernel, examples };
}
