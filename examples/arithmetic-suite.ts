import { performance } from "node:perf_hooks";
import {
  all, app, assume, at, bind, calc, congr, ctor, definition, eq, eqElim,
  foralls, given, imp, impElim, induction, pred, refl, settle, symm, theorem, v,
  type Formula, type Proof, type Term,
} from "../src/index.ts";
import { buildProofSuite, type CheckedExample, type ProofSuite } from "./proof-suite.ts";

const zero = app("zero");
const succ = (x: Term): Term => app("succ", x);
const plus = (x: Term, y: Term): Term => app("plus", x, y);
const times = (x: Term, y: Term): Term => app("times", x, y);
const nat = (x: Term): Formula => pred("Nat", x);

export function buildArithmeticSuite(): ProofSuite {
  const base = buildProofSuite();
  const kernel = base.kernel;
  const examples: CheckedExample[] = [...base.examples];
  const admit = (name: string, statement: Formula, proof: Proof): void => {
    const start = performance.now();
    kernel.addTheorem(name, statement, proof);
    examples.push({ name, statement, proof, checkMilliseconds: performance.now() - start });
  };

  const plusSuccAt = (n: Term, m: Term): Formula => eq(plus(n, succ(m)), succ(plus(n, m)));
  admit(
    "plus.succ_right",
    foralls(["m", "n"], imp(nat(v("n")), plusSuccAt(v("n"), v("m")))),
    all(["m"], induction("Naturals", "n", plusSuccAt(v("n"), v("m")), [
      {
        constructor: "zero",
        fields: [],
        proof: settle(kernel, plusSuccAt(zero, v("m")), {
          using: [definition("plus", "equation.0")],
        }),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: settle(kernel, plusSuccAt(succ(v("k")), v("m")), {
          using: [definition("plus", "equation.1"), assume(plusSuccAt(v("k"), v("m")))],
          assumptions: [plusSuccAt(v("k"), v("m"))],
        }),
      },
    ])),
  );

  const plusCommAt = (n: Term, y: Term): Formula => eq(plus(n, y), plus(y, n));
  const natY = nat(v("y"));
  const plusCommMotive = imp(natY, plusCommAt(v("n"), v("y")));
  admit(
    "plus.commutative",
    foralls(["y", "n"], imp(nat(v("n")), plusCommMotive)),
    all(["y"], induction("Naturals", "n", plusCommMotive, [
      {
        constructor: "zero",
        fields: [],
        proof: given([natY], settle(kernel, plusCommAt(zero, v("y")), {
          using: [definition("plus", "equation.0"), theorem("plus.right_unit")],
          assumptions: [natY],
        })),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: given([natY], settle(kernel, plusCommAt(succ(v("k")), v("y")), {
          using: [
            definition("plus", "equation.1"),
            theorem("plus.succ_right"),
            impElim(assume(plusCommMotiveAt(v("k"), v("y"))), assume(natY)),
          ],
          assumptions: [nat(v("k")), plusCommMotiveAt(v("k"), v("y")), natY],
        })),
      },
    ])),
  );

  // A useful AC permutation lemma. The ordered-rewrite discipline in settle
  // prevents this (and commutativity) from looping.
  const swapAt = (a: Term, b: Term, c: Term): Formula => eq(plus(a, plus(b, c)), plus(b, plus(a, c)));
  const natA = nat(v("a"));
  const natB = nat(v("b"));
  admit(
    "plus.swap",
    foralls(["a", "b", "c"], imp(natA, imp(natB, swapAt(v("a"), v("b"), v("c"))))),
    all(["a", "b", "c"], given([natA, natB], calc(
      symm(usePlusAssociative(v("a"), v("b"), v("c"), assume(natA))),
      congr("plus", usePlusCommutative(v("a"), v("b"), assume(natA), assume(natB)), refl(v("c"))),
      usePlusAssociative(v("b"), v("a"), v("c"), assume(natB)),
    ))),
  );

  kernel.defineStructuralFunction({
    name: "times",
    parameters: ["x", "y"],
    datatype: "Naturals",
    decreasingParameter: 0,
    equations: [
      { patterns: [ctor("zero"), bind("y")], body: zero },
      { patterns: [ctor("succ", bind("x")), bind("y")], body: plus(v("y"), times(v("x"), v("y"))) },
    ],
  });

  const timesZeroAt = (n: Term): Formula => eq(times(n, zero), zero);
  admit(
    "times.right_zero",
    foralls(["n"], imp(nat(v("n")), timesZeroAt(v("n")))),
    induction("Naturals", "n", timesZeroAt(v("n")), [
      { constructor: "zero", fields: [], proof: settle(kernel, timesZeroAt(zero), { using: [definition("times", "equation.0")] }) },
      {
        constructor: "succ",
        fields: ["k"],
        proof: settle(kernel, timesZeroAt(succ(v("k"))), {
          using: [definition("times", "equation.1"), definition("plus", "equation.0"), assume(timesZeroAt(v("k")))],
          assumptions: [timesZeroAt(v("k"))],
        }),
      },
    ]),
  );

  const timesSuccAt = (n: Term, y: Term): Formula => eq(times(n, succ(y)), plus(n, times(n, y)));
  const timesSuccMotive = imp(natY, timesSuccAt(v("n"), v("y")));
  admit(
    "times.succ_right",
    foralls(["y", "n"], imp(nat(v("n")), timesSuccMotive)),
    all(["y"], induction("Naturals", "n", timesSuccMotive, [
      {
        constructor: "zero",
        fields: [],
        proof: given([natY], settle(kernel, timesSuccAt(zero, v("y")), {
          using: [definition("times", "equation.0"), definition("plus", "equation.0")],
          assumptions: [natY],
        })),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: given([natY], settle(kernel, timesSuccAt(succ(v("k")), v("y")), {
          using: [
            definition("times", "equation.1"),
            definition("plus", "equation.1"),
            theorem("plus.swap"),
            impElim(assume(timesSuccMotiveAt(v("k"), v("y"))), assume(natY)),
          ],
          assumptions: [nat(v("k")), timesSuccMotiveAt(v("k"), v("y")), natY],
        })),
      },
    ])),
  );

  const timesCommAt = (n: Term, y: Term): Formula => eq(times(n, y), times(y, n));
  const timesCommMotive = imp(natY, timesCommAt(v("n"), v("y")));
  admit(
    "times.commutative",
    foralls(["y", "n"], imp(nat(v("n")), timesCommMotive)),
    all(["y"], induction("Naturals", "n", timesCommMotive, [
      {
        constructor: "zero",
        fields: [],
        proof: given([natY], settle(kernel, timesCommAt(zero, v("y")), {
          using: [definition("times", "equation.0"), theorem("times.right_zero")],
          assumptions: [natY],
        })),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: given([natY], settle(kernel, timesCommAt(succ(v("k")), v("y")), {
          using: [
            definition("times", "equation.1"),
            theorem("times.succ_right"),
            impElim(assume(timesCommMotiveAt(v("k"), v("y"))), assume(natY)),
          ],
          assumptions: [nat(v("k")), timesCommMotiveAt(v("k"), v("y")), natY],
        })),
      },
    ])),
  );

  const plusClosedAt = (n: Term, y: Term): Formula => imp(nat(y), nat(plus(n, y)));
  admit(
    "Nat.plus_closed",
    foralls(["y", "n"], imp(nat(v("n")), plusClosedAt(v("n"), v("y")))),
    all(["y"], induction("Naturals", "n", plusClosedAt(v("n"), v("y")), [
      {
        constructor: "zero",
        fields: [],
        proof: given([natY], eqElim(
          at(definition("plus", "equation.0"), v("y")),
          "q",
          nat(v("q")),
          assume(natY),
          true,
        )),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: given([natY], eqElim(
          at(definition("plus", "equation.1"), v("k"), v("y")),
          "q",
          nat(v("q")),
          impElim(
            at(theorem("Naturals.constructor.succ"), plus(v("k"), v("y"))),
            impElim(assume(plusClosedAt(v("k"), v("y"))), assume(natY)),
          ),
          true,
        )),
      },
    ])),
  );

  const distributeRightAt = (n: Term, y: Term, z: Term): Formula => eq(
    times(plus(n, y), z),
    plus(times(n, z), times(y, z)),
  );
  const natZ = nat(v("z"));
  const distributeMotive = imp(natZ, distributeRightAt(v("n"), v("y"), v("z")));
  admit(
    "times.distributes_right",
    foralls(["y", "z", "n"], imp(nat(v("n")), distributeMotive)),
    all(["y", "z"], induction("Naturals", "n", distributeMotive, [
      {
        constructor: "zero",
        fields: [],
        proof: given([natZ], settle(kernel, distributeRightAt(zero, v("y"), v("z")), {
          using: [definition("plus", "equation.0"), definition("times", "equation.0")],
          assumptions: [natZ],
        })),
      },
      {
        constructor: "succ",
        fields: ["k"],
        proof: given([natZ], settle(kernel, distributeRightAt(succ(v("k")), v("y"), v("z")), {
          using: [
            definition("plus", "equation.1"),
            definition("times", "equation.1"),
            theorem("plus.associative"),
            impElim(assume(distributeMotiveAt(v("k"), v("y"), v("z"))), assume(natZ)),
          ],
          assumptions: [nat(v("k")), distributeMotiveAt(v("k"), v("y"), v("z")), natZ],
        })),
      },
    ])),
  );

  const distributeLeftAt = (x: Term, y: Term, z: Term): Formula => eq(
    times(x, plus(y, z)),
    plus(times(x, y), times(x, z)),
  );
  const natX = nat(v("x"));
  admit(
    "times.distributes_left",
    foralls(["x", "y", "z"], imp(natX, imp(natY, imp(natZ, distributeLeftAt(v("x"), v("y"), v("z")))))),
    all(["x", "y", "z"], given([natX, natY, natZ], (() => {
      const natYZ = usePlusClosed(v("y"), v("z"), assume(natY), assume(natZ));
      return calc(
        useTimesCommutative(v("x"), plus(v("y"), v("z")), assume(natX), natYZ),
        useDistributesRight(v("y"), v("z"), v("x"), assume(natY), assume(natX)),
        congr(
          "plus",
          useTimesCommutative(v("y"), v("x"), assume(natY), assume(natX)),
          useTimesCommutative(v("z"), v("x"), assume(natZ), assume(natX)),
        ),
      );
    })())),
  );

  // A nontrivial rewrite client: the binary distributivity lemma is applied
  // recursively to expand a three-term sum. Derived typing facts discharge its
  // conditional side goals; no arithmetic-specific kernel rule is involved.
  const distributeThreeAt = (a: Term, b: Term, c: Term, d: Term): Formula => eq(
    times(plus(plus(a, b), c), d),
    plus(plus(times(a, d), times(b, d)), times(c, d)),
  );
  const natC = nat(v("c"));
  const natD = nat(v("d"));
  admit(
    "times.distributes_three",
    foralls(["a", "b", "c", "d"], imp(natA, imp(natB, imp(natC, imp(natD,
      distributeThreeAt(v("a"), v("b"), v("c"), v("d"))))))),
    all(["a", "b", "c", "d"], given([natA, natB, natC, natD], (() => {
      const natAB = usePlusClosed(v("a"), v("b"), assume(natA), assume(natB));
      const natABC = usePlusClosed(plus(v("a"), v("b")), v("c"), natAB, assume(natC));
      return settle(kernel, distributeThreeAt(v("a"), v("b"), v("c"), v("d")), {
        using: [theorem("times.distributes_right")],
        assumptions: [natA, natB, natC, natD],
        facts: [natAB, natABC],
      });
    })())),
  );

  return { kernel, examples };
}

function plusCommMotiveAt(n: Term, y: Term): Formula {
  return imp(nat(y), eq(plus(n, y), plus(y, n)));
}

function timesSuccMotiveAt(n: Term, y: Term): Formula {
  return imp(nat(y), eq(times(n, succ(y)), plus(n, times(n, y))));
}

function timesCommMotiveAt(n: Term, y: Term): Formula {
  return imp(nat(y), eq(times(n, y), times(y, n)));
}

function distributeMotiveAt(n: Term, y: Term, z: Term): Formula {
  return imp(nat(z), eq(times(plus(n, y), z), plus(times(n, z), times(y, z))));
}

function discharge(proof: Proof, ...evidence: readonly Proof[]): Proof {
  return evidence.reduce<Proof>((result, item) => impElim(result, item), proof);
}

function usePlusAssociative(n: Term, y: Term, z: Term, natN: Proof): Proof {
  return discharge(at(theorem("plus.associative"), y, z, n), natN);
}

function usePlusCommutative(n: Term, y: Term, natN: Proof, natY: Proof): Proof {
  return discharge(at(theorem("plus.commutative"), y, n), natN, natY);
}

function usePlusClosed(n: Term, y: Term, natN: Proof, natY: Proof): Proof {
  return discharge(at(theorem("Nat.plus_closed"), y, n), natN, natY);
}

function useTimesCommutative(n: Term, y: Term, natN: Proof, natY: Proof): Proof {
  return discharge(at(theorem("times.commutative"), y, n), natN, natY);
}

function useDistributesRight(n: Term, y: Term, z: Term, natN: Proof, natZ: Proof): Proof {
  return discharge(at(theorem("times.distributes_right"), y, z, n), natN, natZ);
}
