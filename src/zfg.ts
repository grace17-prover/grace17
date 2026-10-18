// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

import { readFileSync } from "node:fs";
import { sha256Hex } from "./hash.ts";
import { join } from "node:path";
import { projectRoot } from "./project-root.ts";
import { and, app, eq, exists, forall, iff, imp, not, or, pred, v, type Formula } from "./ast.ts";
import { Kernel, type SetTheoryProfile } from "./kernel.ts";
import { elaborateModule } from "./surface.ts";

export interface SetTheoryOptions {
  readonly profile?: Exclude<SetTheoryProfile, "none">;
}

/** Install the axiomatic/schema foundation, before the checked convenience prelude. */
export function createSetTheoryFoundationKernel(options: SetTheoryOptions = {}): Kernel {
  return buildSetTheoryKernel(options, false);
}

/** Install the foundation plus the small proof-checked bootstrap prelude. */
export function createSetTheoryKernel(options: SetTheoryOptions = {}): Kernel {
  return buildSetTheoryKernel(options, true);
}

/**
 * A kernel whose foundation is replayed from an image instead of elaborated
 * from the bootstrap sources: `install` receives the bare axiomatic kernel
 * and must bring it to the foundation, which is then sealed as usual.
 */
export function createSetTheoryKernelFromImage(options: SetTheoryOptions, install: (kernel: Kernel) => void): Kernel {
  const kernel = buildSetTheoryKernel(options, false, false);
  install(kernel);
  kernel.recordFoundationBoundary();
  return kernel;
}

/** The bare axiomatic kernel before the prelude, with its boundary left open for an image. */
export function createSetTheoryBareKernel(options: SetTheoryOptions = {}): Kernel {
  return buildSetTheoryKernel(options, false, false);
}

/** Digest of the bootstrap prelude's sources, which a foundation image records. */
export function bootstrapSourceDigest(): string {
  return sha256Hex(SET_THEORY_BOOTSTRAP_FILES.map(name => readFileSync(join(projectRoot, "lib", name), "utf8")).join("\u0000"));
}

function buildSetTheoryKernel(options: SetTheoryOptions, includeBootstrap: boolean, seal = true): Kernel {
  const profile = options.profile ?? "ZFG";
  const kernel = new Kernel({ separation: true, replacement: true, inductiveDefinitions: true, setTheory: profile });

  for (const [name, arity] of [["empty", 0], ["pair", 2], ["union", 1], ["powerset", 1],
    ["omega", 0], ["apply", 2], ["epsilon0", 0]] as const) {
    kernel.declareFunction(name, arity);
  }
  kernel.declarePredicate("in", 2);

  const x = v("x");
  const y = v("y");
  const z = v("z");
  const emptyMembership = forall("x", not(pred("in", x, app("empty"))));
  kernel.addAxiom("set.empty", emptyMembership);

  const pairMembership = forall("x", forall("y", forall("z",
    iff(pred("in", z, app("pair", x, y)), or(eq(z, x), eq(z, y))),
  )));
  kernel.addAxiom("set.pairing", pairMembership);

  const extensionality = forall("x", forall("y", imp(
    forall("z", iff(pred("in", z, x), pred("in", z, y))), eq(x, y),
  )));
  kernel.addAxiom("set.extensionality", extensionality);

  kernel.definePredicate("subset", ["x", "y"], forall("z", imp(pred("in", z, x), pred("in", z, y))));
  kernel.addAxiom("set.union", forall("A", forall("x", iff(
    pred("in", v("x"), app("union", v("A"))),
    exists("y", and(pred("in", v("y"), v("A")), pred("in", v("x"), v("y")))),
  ))));
  const powersetMembership = forall("x", forall("y", iff(
    pred("in", x, app("powerset", y)),
    forall("z", imp(pred("in", v("z"), x), pred("in", v("z"), y))),
  )));
  kernel.addAxiom("set.powerset", powersetMembership);

  kernel.defineFunction("singleton", ["x"], app("pair", x, x));
  kernel.defineFunction("union2", ["x", "y"], app("union", app("pair", x, y)));
  // Mathematical pairs are Kuratowski pairs. A runtime may still store them as
  // two pointers once its representation theorem has been checked.
  kernel.defineFunction("orderedPair", ["x", "y"], app("pair", app("pair", x, x), app("pair", x, y)));
  kernel.defineFunction("cons", ["x", "y"], app("orderedPair", x, y));
  // Naturals retain their compact runtime representation, but their logical
  // meaning is the transparent von Neumann set interface.
  kernel.defineFunction("zero", [], app("empty"));
  kernel.defineFunction("succ", ["n"], app("union", app("pair", v("n"), app("pair", v("n"), v("n")))));
  kernel.definePredicate("Nat", ["n"], pred("in", v("n"), app("omega")));

  kernel.definePredicate("relates", ["r", "x", "y"], pred("in", app("orderedPair", v("x"), v("y")), v("r")));
  kernel.definePredicate("functionOn", ["f", "A", "B"], and(
    forall("x", imp(pred("in", v("x"), v("A")), exists("y", and(
      pred("in", v("y"), v("B")),
      and(pred("relates", v("f"), v("x"), v("y")), forall("z", imp(
        pred("relates", v("f"), v("x"), v("z")), eq(v("z"), v("y")),
      ))),
    )))),
    forall("p", imp(pred("in", v("p"), v("f")), exists("x", exists("y", and(
      pred("in", v("x"), v("A")),
      and(pred("in", v("y"), v("B")), eq(v("p"), app("orderedPair", v("x"), v("y")))),
    ))))),
  ));
  kernel.addAxiom("function.apply", forall("f", forall("A", forall("B", forall("x", forall("y", imp(
    and(pred("functionOn", v("f"), v("A"), v("B")), and(
      pred("in", v("x"), v("A")), pred("relates", v("f"), v("x"), v("y")),
    )), eq(app("apply", v("f"), v("x")), v("y")),
  )))))));

  kernel.addAxiom("set.infinity", and(
    pred("in", app("empty"), app("omega")),
    forall("n", imp(pred("in", v("n"), app("omega")),
      pred("in", app("union", app("pair", v("n"), app("pair", v("n"), v("n")))), app("omega")))),
  ));
  kernel.addAxiom("set.infinity.minimal", forall("A", imp(and(
    pred("in", app("empty"), v("A")),
    forall("n", imp(pred("in", v("n"), v("A")), pred("in",
      app("union", app("pair", v("n"), app("pair", v("n"), v("n")))), v("A")))),
  ), forall("n", imp(pred("in", v("n"), app("omega")), pred("in", v("n"), v("A")))))));

  const foundation: Formula = forall("x", imp(
    not(eq(v("x"), app("empty"))),
    exists("y", and(pred("in", v("y"), v("x")), forall("z", imp(
      pred("in", v("z"), v("y")), not(pred("in", v("z"), v("x"))),
    )))),
  ));
  kernel.addAxiom("set.foundation", foundation);

  kernel.definePredicate("wellFoundedOn", ["r", "A"], forall("s", imp(
    and(pred("subset", v("s"), v("A")), not(eq(v("s"), app("empty")))),
    exists("m", and(pred("in", v("m"), v("s")), forall("y", imp(
      pred("in", v("y"), v("s")), not(pred("relates", v("r"), v("y"), v("m"))),
    )))),
  )));
  kernel.definePredicate("E0Ordinal", ["x"], pred("in", v("x"), app("epsilon0")));

  if (profile === "ZFC" || profile === "ZFG") {
    kernel.addAxiom("set.choice", forall("A", imp(
      forall("x", imp(pred("in", v("x"), v("A")), exists("y", pred("in", v("y"), v("x"))))),
      exists("f", and(
        pred("functionOn", v("f"), v("A"), app("union", v("A"))),
        forall("x", imp(pred("in", v("x"), v("A")), pred("in", app("apply", v("f"), v("x")), v("x")))),
      )),
    )));
  }
  if (profile === "ZFG") {
    kernel.declareFunction("choose", 1);
    kernel.addAxiom("set.globalChoice", forall("A", imp(
      not(eq(v("A"), app("empty"))), pred("in", app("choose", v("A")), v("A")),
    )));
  }

  kernel.registerNaturalDatatype();
  if (includeBootstrap) installSetTheoryBootstrap(kernel);
  if (seal) kernel.recordFoundationBoundary();
  return kernel;
}

/** Ordered source of every proof-derived declaration installed before Core. */
export const SET_THEORY_BOOTSTRAP_FILES = [
  "Grace/Bootstrap/Aliases.g17",
  "Grace/Bootstrap/Nat.g17",
  "Grace/Bootstrap/OrderedPair.g17",
  "Grace/Bootstrap/Epsilon0.g17",
] as const;

/**
 * Elaborate the visible, ordered bootstrap sources. Surface elaboration is
 * untrusted: each definition and theorem is admitted only through Kernel's
 * checked operations, and the resulting event stream can be replayed by an
 * independent checker.
 */
export function installSetTheoryBootstrap(kernel: Kernel): void {
  for (const name of SET_THEORY_BOOTSTRAP_FILES) {
    const file = join(projectRoot, "lib", name);
    elaborateModule(kernel, readFileSync(file, "utf8"));
  }
}

export const createZfKernel = (): Kernel => createSetTheoryKernel({ profile: "ZF" });
export const createZfcKernel = (): Kernel => createSetTheoryKernel({ profile: "ZFC" });
export const createZfgKernel = (): Kernel => createSetTheoryKernel({ profile: "ZFG" });
export const createZfFoundationKernel = (): Kernel => createSetTheoryFoundationKernel({ profile: "ZF" });
export const createZfcFoundationKernel = (): Kernel => createSetTheoryFoundationKernel({ profile: "ZFC" });
export const createZfgFoundationKernel = (): Kernel => createSetTheoryFoundationKernel({ profile: "ZFG" });
