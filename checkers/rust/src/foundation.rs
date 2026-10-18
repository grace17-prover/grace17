// The normative construction of the ZF, ZFC, and ZFG foundations.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::admissions::{self, FunctionDefinition, PredicateDefinition};
use crate::ast::{and, app, eq, exists, forall, foralls, iff, imp, neg, or, pred, v};
use crate::environment::Environment;
use crate::support::{fail, is_digest, parse_json, read_text, Result};
use serde_json::Value;

/// Construct the foundation of a profile; trusted maps are never read.
pub fn construct_foundation(profile: &str) -> Result<Environment> {
    let mut env = Environment::empty_foundation(profile)?;
    for (name, arity) in [("empty", 0), ("pair", 2), ("union", 1), ("powerset", 1), ("omega", 0), ("apply", 2), ("epsilon0", 0)] {
        env.fresh_name(name)?;
        env.functions.insert(name.to_string(), arity);
    }
    env.fresh_name("in")?;
    env.predicates.insert("in".to_string(), 2);

    let (x, y, z) = (v("x"), v("y"), v("z"));
    env.add_axiom("set.empty", forall("x", neg(pred("in", vec![x.clone(), app("empty", vec![])]))))?;
    env.add_axiom(
        "set.pairing",
        forall(
            "x",
            forall(
                "y",
                forall(
                    "z",
                    iff(pred("in", vec![z.clone(), app("pair", vec![x.clone(), y.clone()])]), or(eq(z.clone(), x.clone()), eq(z.clone(), y.clone()))),
                ),
            ),
        ),
    )?;
    env.add_axiom(
        "set.extensionality",
        forall(
            "x",
            forall(
                "y",
                imp(forall("z", iff(pred("in", vec![z.clone(), x.clone()]), pred("in", vec![z.clone(), y.clone()]))), eq(x.clone(), y.clone())),
            ),
        ),
    )?;
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition {
            name: "subset".into(),
            parameters: vec!["x".into(), "y".into()],
            body: forall("z", imp(pred("in", vec![v("z"), v("x")]), pred("in", vec![v("z"), v("y")]))),
        },
    )?;
    env.add_axiom(
        "set.union",
        forall(
            "A",
            forall(
                "x",
                iff(
                    pred("in", vec![v("x"), app("union", vec![v("A")])]),
                    exists("y", and(pred("in", vec![v("y"), v("A")]), pred("in", vec![v("x"), v("y")]))),
                ),
            ),
        ),
    )?;
    env.add_axiom(
        "set.powerset",
        forall(
            "x",
            forall(
                "y",
                iff(
                    pred("in", vec![x.clone(), app("powerset", vec![y.clone()])]),
                    forall("z", imp(pred("in", vec![v("z"), x.clone()]), pred("in", vec![v("z"), y.clone()]))),
                ),
            ),
        ),
    )?;

    let define = |env: &mut Environment, name: &str, parameters: &[&str], body| -> Result<()> {
        admissions::define_function(
            env,
            &FunctionDefinition { name: name.into(), parameters: parameters.iter().map(|p| p.to_string()).collect(), body },
        )
    };
    define(&mut env, "singleton", &["x"], app("pair", vec![v("x"), v("x")]))?;
    define(&mut env, "union2", &["x", "y"], app("union", vec![app("pair", vec![v("x"), v("y")])]))?;
    define(&mut env, "orderedPair", &["x", "y"], app("pair", vec![app("pair", vec![v("x"), v("x")]), app("pair", vec![v("x"), v("y")])]))?;
    define(&mut env, "cons", &["x", "y"], app("orderedPair", vec![v("x"), v("y")]))?;
    define(&mut env, "zero", &[], app("empty", vec![]))?;
    define(&mut env, "succ", &["n"], app("union", vec![app("pair", vec![v("n"), app("pair", vec![v("n"), v("n")])])]))?;
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition { name: "Nat".into(), parameters: vec!["n".into()], body: pred("in", vec![v("n"), app("omega", vec![])]) },
    )?;
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition {
            name: "relates".into(),
            parameters: vec!["r".into(), "x".into(), "y".into()],
            body: pred("in", vec![app("orderedPair", vec![v("x"), v("y")]), v("r")]),
        },
    )?;

    let function_on = and(
        forall(
            "x",
            imp(
                pred("in", vec![v("x"), v("A")]),
                exists(
                    "y",
                    and(
                        pred("in", vec![v("y"), v("B")]),
                        and(
                            pred("relates", vec![v("f"), v("x"), v("y")]),
                            forall("z", imp(pred("relates", vec![v("f"), v("x"), v("z")]), eq(v("z"), v("y")))),
                        ),
                    ),
                ),
            ),
        ),
        forall(
            "p",
            imp(
                pred("in", vec![v("p"), v("f")]),
                exists(
                    "x",
                    exists(
                        "y",
                        and(
                            pred("in", vec![v("x"), v("A")]),
                            and(pred("in", vec![v("y"), v("B")]), eq(v("p"), app("orderedPair", vec![v("x"), v("y")]))),
                        ),
                    ),
                ),
            ),
        ),
    );
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition { name: "functionOn".into(), parameters: vec!["f".into(), "A".into(), "B".into()], body: function_on },
    )?;
    env.add_axiom(
        "function.apply",
        foralls(
            &["f".to_string(), "A".to_string(), "B".to_string(), "x".to_string(), "y".to_string()],
            imp(
                and(
                    pred("functionOn", vec![v("f"), v("A"), v("B")]),
                    and(pred("in", vec![v("x"), v("A")]), pred("relates", vec![v("f"), v("x"), v("y")])),
                ),
                eq(app("apply", vec![v("f"), v("x")]), v("y")),
            ),
        ),
    )?;

    let successor_set = |n: &str| app("union", vec![app("pair", vec![v(n), app("pair", vec![v(n), v(n)])])]);
    env.add_axiom(
        "set.infinity",
        and(
            pred("in", vec![app("empty", vec![]), app("omega", vec![])]),
            forall("n", imp(pred("in", vec![v("n"), app("omega", vec![])]), pred("in", vec![successor_set("n"), app("omega", vec![])]))),
        ),
    )?;
    env.add_axiom(
        "set.infinity.minimal",
        forall(
            "A",
            imp(
                and(
                    pred("in", vec![app("empty", vec![]), v("A")]),
                    forall("n", imp(pred("in", vec![v("n"), v("A")]), pred("in", vec![successor_set("n"), v("A")]))),
                ),
                forall("n", imp(pred("in", vec![v("n"), app("omega", vec![])]), pred("in", vec![v("n"), v("A")]))),
            ),
        ),
    )?;
    env.add_axiom(
        "set.foundation",
        forall(
            "x",
            imp(
                neg(eq(v("x"), app("empty", vec![]))),
                exists(
                    "y",
                    and(
                        pred("in", vec![v("y"), v("x")]),
                        forall("z", imp(pred("in", vec![v("z"), v("y")]), neg(pred("in", vec![v("z"), v("x")])))),
                    ),
                ),
            ),
        ),
    )?;
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition {
            name: "wellFoundedOn".into(),
            parameters: vec!["r".into(), "A".into()],
            body: forall(
                "s",
                imp(
                    and(pred("subset", vec![v("s"), v("A")]), neg(eq(v("s"), app("empty", vec![])))),
                    exists(
                        "m",
                        and(
                            pred("in", vec![v("m"), v("s")]),
                            forall("y", imp(pred("in", vec![v("y"), v("s")]), neg(pred("relates", vec![v("r"), v("y"), v("m")])))),
                        ),
                    ),
                ),
            ),
        },
    )?;
    admissions::define_predicate(
        &mut env,
        &PredicateDefinition { name: "E0Ordinal".into(), parameters: vec!["x".into()], body: pred("in", vec![v("x"), app("epsilon0", vec![])]) },
    )?;

    if profile == "ZFC" || profile == "ZFG" {
        env.add_axiom(
            "set.choice",
            forall(
                "A",
                imp(
                    forall("x", imp(pred("in", vec![v("x"), v("A")]), exists("y", pred("in", vec![v("y"), v("x")])))),
                    exists(
                        "f",
                        and(
                            pred("functionOn", vec![v("f"), v("A"), app("union", vec![v("A")])]),
                            forall("x", imp(pred("in", vec![v("x"), v("A")]), pred("in", vec![app("apply", vec![v("f"), v("x")]), v("x")]))),
                        ),
                    ),
                ),
            ),
        )?;
    }
    if profile == "ZFG" {
        env.fresh_name("choose")?;
        env.functions.insert("choose".to_string(), 1);
        env.add_axiom(
            "set.globalChoice",
            forall("A", imp(neg(eq(v("A"), app("empty", vec![]))), pred("in", vec![app("choose", vec![v("A")]), v("A")]))),
        )?;
    }
    admissions::register_natural_datatype(&mut env)?;
    env.refresh_digest()?;
    Ok(env)
}

/// A profile name constructs the foundation; a tiny `.g17f` receipt names
/// the profile and the digest the construction must reach.
pub fn load_foundation(value: &str) -> Result<Environment> {
    if matches!(value, "ZF" | "ZFC" | "ZFG") {
        return construct_foundation(value);
    }
    let document = parse_json(&read_text(value)?)?;
    if document.get("format") == Some(&Value::String("grace17.foundation".into())) {
        let keys: std::collections::BTreeSet<&str> = match &document {
            Value::Object(map) => map.keys().map(String::as_str).collect(),
            _ => return fail("malformed foundation bootstrap"),
        };
        let expected: std::collections::BTreeSet<&str> = ["format", "version", "profile", "environment"].into_iter().collect();
        let profile = document.get("profile").and_then(Value::as_str);
        let environment = document.get("environment").and_then(Value::as_str);
        if keys != expected
            || document.get("version") != Some(&Value::Number(1.into()))
            || !matches!(profile, Some("ZF" | "ZFC" | "ZFG"))
            || !environment.map(is_digest).unwrap_or(false)
        {
            return fail("malformed foundation bootstrap");
        }
        let env = construct_foundation(profile.expect("checked"))?;
        if env.digest != environment.expect("checked") {
            return fail("foundation bootstrap produced the wrong environment");
        }
        return Ok(env);
    }
    fail("G17C foundations must be checker-constructed; trusted .g17env snapshots are not accepted")
}
