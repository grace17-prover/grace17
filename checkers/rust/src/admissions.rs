// Compiled-module replay: the admission events that extend an environment,
// the named-rule proofs inside them, and the module procedure.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::ast::{
    and, app, binary, eq, exists, forall, foralls, free_formula, free_term, fresh, functions_in_term, iff, imp, nat, neg, or,
    pattern_bindings, pattern_term, pred, quantify, same_formula, same_term, substitute_formula, substitute_many, substitute_simultaneous,
    substitute_term, symbols_in_formula, v, Formula, Pattern, Term,
};
use crate::compute;
use crate::environment::{parse_datatype, parse_recursive, Body, Datatype, Environment};
use crate::machine;
use crate::support::{canonical, fail, is_digest, natural_int, sha256_hex, CheckError, Result};
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, BTreeSet};

pub struct FunctionDefinition {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Term,
}

pub struct PredicateDefinition {
    pub name: String,
    pub parameters: Vec<String>,
    pub body: Formula,
}

// JSON field access for event payloads.

fn get<'a>(value: &'a Value, key: &str) -> Result<&'a Value> {
    value.get(key).ok_or_else(|| CheckError(format!("malformed G17C payload: missing {key}")))
}

fn get_str(value: &Value, key: &str) -> Result<String> {
    match get(value, key)? {
        Value::String(text) => Ok(text.clone()),
        _ => fail(format!("malformed G17C payload: {key} is not a string")),
    }
}

fn get_strings(value: &Value, key: &str) -> Result<Vec<String>> {
    match get(value, key)? {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::String(text) => Ok(text.clone()),
                _ => fail(format!("malformed G17C payload: {key} is not a string list")),
            })
            .collect(),
        _ => fail(format!("malformed G17C payload: {key} is not a list")),
    }
}

fn get_term(value: &Value, key: &str) -> Result<Term> {
    Term::from_json(get(value, key)?)
}

fn get_formula(value: &Value, key: &str) -> Result<Formula> {
    Formula::from_json(get(value, key)?)
}

fn get_usize(value: &Value, key: &str) -> Result<usize> {
    natural_int(get(value, key)?).ok_or_else(|| CheckError(format!("malformed G17C payload: {key} is not a natural")))
}

fn params(env: &Environment, parameters: &[String]) -> Result<()> {
    env.check_parameters(parameters)
}

fn vars(names: &[String]) -> Vec<Term> {
    names.iter().map(|name| v(name)).collect()
}

fn set_of(names: &[String]) -> BTreeSet<String> {
    names.iter().cloned().collect()
}

fn subset(left: &BTreeSet<String>, right: &BTreeSet<String>) -> bool {
    left.is_subset(right)
}

// Explicit definitions.

pub fn define_function(env: &mut Environment, definition: &FunctionDefinition) -> Result<()> {
    let FunctionDefinition { name, parameters, body } = definition;
    params(env, parameters)?;
    env.fresh_name(name)?;
    env.check_term(body)?;
    let mut used = BTreeSet::new();
    functions_in_term(body, &mut used);
    if used.contains(name) || !subset(&free_term(body), &set_of(parameters)) {
        return fail("bad function definition");
    }
    env.functions.insert(name.clone(), parameters.len());
    env.bodies.insert(name.clone(), Body { parameters: parameters.clone(), body: body.clone() });
    let equation = foralls(parameters, eq(app(name, vars(parameters)), body.clone()));
    env.record_definition(name, "function", parameters, vec![("equation".into(), equation)])
}

pub fn define_predicate(env: &mut Environment, definition: &PredicateDefinition) -> Result<()> {
    let PredicateDefinition { name, parameters, body } = definition;
    params(env, parameters)?;
    env.fresh_name(name)?;
    env.check_formula(body)?;
    let mut used = BTreeSet::new();
    symbols_in_formula(body, &mut used);
    if used.contains(name) || !subset(&free_formula(body), &set_of(parameters)) {
        return fail("bad predicate definition");
    }
    env.predicates.insert(name.clone(), parameters.len());
    let equation = foralls(parameters, iff(pred(name, vars(parameters)), body.clone()));
    env.record_definition(name, "predicate", parameters, vec![("equation".into(), equation)])
}

fn define_subset(env: &mut Environment, payload: &Value) -> Result<()> {
    if !env.capability("separation") {
        return fail("foundation does not enable Separation");
    }
    let name = get_str(payload, "name")?;
    let parameters = get_strings(payload, "parameters")?;
    let element = get_str(payload, "element")?;
    let bound = get_term(payload, "bound")?;
    let condition = get_formula(payload, "condition")?;
    params(env, &parameters)?;
    env.fresh_name(&name)?;
    env.check_term(&bound)?;
    env.check_formula(&condition)?;
    let mut allowed = set_of(&parameters);
    allowed.insert(element.clone());
    if element.is_empty() || parameters.contains(&element) || !subset(&free_term(&bound), &set_of(&parameters)) || !subset(&free_formula(&condition), &allowed) {
        return fail("malformed Separation instance");
    }
    env.functions.insert(name.clone(), parameters.len());
    let mut binders = parameters.clone();
    binders.push(element.clone());
    let membership = foralls(
        &binders,
        iff(pred("in", vec![v(&element), app(&name, vars(&parameters))]), and(pred("in", vec![v(&element), bound]), condition)),
    );
    env.record_definition(&name, "separation", &parameters, vec![("membership".into(), membership)])
}

// Datatypes.

fn combine(tag: &str, items: Vec<Formula>) -> Result<Formula> {
    let mut iterator = items.into_iter();
    let mut result = match iterator.next() {
        Some(first) => first,
        None => return fail("empty datatype connective"),
    };
    for item in iterator {
        result = binary(tag, result, item);
    }
    Ok(result)
}

fn sequence(items: Vec<Term>) -> Term {
    let mut result = app("empty", vec![]);
    for item in items.into_iter().rev() {
        result = app("orderedPair", vec![item, result]);
    }
    result
}

fn local_name(name: &str) -> &str {
    name.rsplit('.').next().unwrap_or(name)
}

fn declare_datatype(env: &mut Environment, spec: &Value) -> Result<()> {
    if !env.capability("inductiveDefinitions") {
        return fail("foundation does not enable inductive definitions");
    }
    let encoding = match spec.get("setTheoreticEncoding") {
        Some(Value::Bool(flag)) => *flag,
        _ => return fail("malformed datatype"),
    };
    let datatype = match (spec.get("name"), parse_datatype(spec)) {
        (Some(Value::String(name)), Ok(datatype)) if !name.is_empty() => (name.clone(), datatype),
        _ => return fail("malformed datatype"),
    };
    let (name, datatype) = datatype;
    let Datatype { predicate, parameters, constructors, .. } = &datatype;
    params(env, parameters)?;
    env.fresh_name(&name)?;
    env.fresh_name(predicate)?;
    if encoding && (env.functions.get("orderedPair") != Some(&2) || env.functions.get("empty") != Some(&0) || !env.datatypes.contains_key("Naturals")) {
        return fail("set-theoretic datatype prerequisites are absent");
    }
    if env.datatypes.contains_key(&name) {
        return fail("duplicate datatype");
    }
    let mut seen = BTreeSet::new();
    for ctor in constructors {
        env.fresh_name(&ctor.name)?;
        if !seen.insert(ctor.name.clone()) {
            return fail("malformed constructor");
        }
        let distinct: BTreeSet<usize> = ctor.recursive_fields.iter().copied().collect();
        if distinct.len() != ctor.recursive_fields.len() || ctor.recursive_fields.iter().any(|field| *field >= ctor.arity) {
            return fail("bad recursive fields");
        }
        let fields: BTreeSet<usize> = ctor.parameter_fields.iter().map(|(field, _)| *field).collect();
        if fields.len() != ctor.parameter_fields.len()
            || ctor.parameter_fields.iter().any(|(field, parameter)| *field >= ctor.arity || *parameter >= parameters.len() || distinct.contains(field))
        {
            return fail("bad parameter fields");
        }
    }
    env.predicates.insert(predicate.clone(), parameters.len() + 1);
    for ctor in constructors {
        env.functions.insert(ctor.name.clone(), ctor.arity);
    }
    let names = |prefix: &str, count: usize| -> Vec<String> {
        let mut used: BTreeSet<String> = set_of(parameters);
        let mut result = Vec::with_capacity(count);
        for index in 0..count {
            let mut candidate = format!("{prefix}{index}");
            while used.contains(&candidate) {
                candidate = format!("_{candidate}");
            }
            used.insert(candidate.clone());
            result.push(candidate);
        }
        result
    };
    let mut properties: Vec<(String, Formula)> = Vec::new();
    for ctor in constructors {
        let local = local_name(&ctor.name);
        let fields: Vec<String> = (0..ctor.arity).map(|index| format!("field{index}")).collect();
        let mut closure = pred(predicate, [vars(parameters), vec![app(&ctor.name, vars(&fields))]].concat());
        for index in (0..fields.len()).rev() {
            if ctor.recursive_fields.contains(&index) {
                closure = imp(pred(predicate, [vars(parameters), vec![v(&fields[index])]].concat()), closure);
            } else if let Some((_, parameter)) = ctor.parameter_fields.iter().find(|(field, _)| *field == index) {
                closure = imp(pred("in", vec![v(&fields[index]), v(&parameters[*parameter])]), closure);
            }
        }
        let binders = [parameters.clone(), fields.clone()].concat();
        properties.push((format!("constructor.{local}"), foralls(&binders, closure)));
        if encoding {
            let tag = sequence(format!("{name}.{}", ctor.name).chars().map(|character| nat(u64::from(u32::from(character)))).collect());
            let representation = eq(app(&ctor.name, vars(&fields)), app("orderedPair", vec![tag, sequence(vars(&fields))]));
            properties.push((format!("representation.{local}"), foralls(&binders, representation)));
        }
    }
    for ctor in constructors {
        if ctor.arity == 0 {
            continue;
        }
        let local = local_name(&ctor.name);
        let left = names("left", ctor.arity);
        let right = names("right", ctor.arity);
        let equalities: Vec<Formula> = left.iter().zip(&right).map(|(l, r)| eq(v(l), v(r))).collect();
        let injective = imp(eq(app(&ctor.name, vars(&left)), app(&ctor.name, vars(&right))), combine("and", equalities)?);
        properties.push((format!("injective.{local}"), foralls(&[left, right].concat(), injective)));
    }
    for (left_index, left_ctor) in constructors.iter().enumerate() {
        for right_ctor in &constructors[left_index + 1..] {
            let left = names("left", left_ctor.arity);
            let right = names("right", right_ctor.arity);
            let disjoint = neg(eq(app(&left_ctor.name, vars(&left)), app(&right_ctor.name, vars(&right))));
            properties.push((
                format!("disjoint.{}.{}", local_name(&left_ctor.name), local_name(&right_ctor.name)),
                foralls(&[left, right].concat(), disjoint),
            ));
        }
    }
    let element = if parameters.iter().any(|p| p == "value") { "_value" } else { "value" };
    let mut alternatives = Vec::with_capacity(constructors.len());
    for (ctor_index, ctor) in constructors.iter().enumerate() {
        let fields = names(&format!("case{ctor_index}_field"), ctor.arity);
        let mut guards = Vec::new();
        for (field_index, field) in fields.iter().enumerate() {
            if ctor.recursive_fields.contains(&field_index) {
                guards.push(pred(predicate, [vars(parameters), vec![v(field)]].concat()));
            } else if let Some((_, parameter)) = ctor.parameter_fields.iter().find(|(f, _)| *f == field_index) {
                guards.push(pred("in", vec![v(field), v(&parameters[*parameter])]));
            }
        }
        guards.push(eq(v(element), app(&ctor.name, vars(&fields))));
        let mut alternative = combine("and", guards)?;
        for field in fields.iter().rev() {
            alternative = exists(field, alternative);
        }
        alternatives.push(alternative);
    }
    let cases = imp(pred(predicate, [vars(parameters), vec![v(element)]].concat()), combine("or", alternatives)?);
    properties.push(("cases".into(), foralls(&[parameters.clone(), vec![element.to_string()]].concat(), cases)));
    env.datatypes.insert(name.clone(), datatype.clone());
    env.record_definition(&name, "datatype", &[], properties)
}

/// Register the computational naturals only after checking the canonical
/// von Neumann interface.
pub fn register_natural_datatype(env: &mut Environment) -> Result<()> {
    if env.datatypes.contains_key("Naturals") {
        return fail("Naturals datatype is already registered");
    }
    let expected_successor = app("union", vec![app("pair", vec![v("n"), app("pair", vec![v("n"), v("n")])])]);
    let expected_natural = forall("n", iff(pred("Nat", vec![v("n")]), pred("in", vec![v("n"), app("omega", vec![])])));
    let minimality = forall(
        "A",
        imp(
            and(
                pred("in", vec![app("empty", vec![]), v("A")]),
                forall("n", imp(pred("in", vec![v("n"), v("A")]), pred("in", vec![expected_successor.clone(), v("A")]))),
            ),
            forall("n", imp(pred("in", vec![v("n"), app("omega", vec![])]), pred("in", vec![v("n"), v("A")]))),
        ),
    );
    let zero_ok = matches!(env.bodies.get("zero"), Some(body) if body.parameters.is_empty() && body.body == app("empty", vec![]));
    let successor_ok = matches!(env.bodies.get("succ"), Some(body) if body.parameters == ["n".to_string()] && body.body == expected_successor);
    let natural_ok = matches!(env.property("Nat", "equation"), Some(formula) if same_formula(formula, &expected_natural));
    let minimal_ok = matches!(env.axioms.get("set.infinity.minimal"), Some(formula) if same_formula(formula, &minimality));
    if !zero_ok || !successor_ok || !natural_ok || !minimal_ok {
        return fail("Natural datatype registration requires the canonical von Neumann interface");
    }
    let raw = json!({
        "name": "Naturals", "predicate": "Nat",
        "constructors": [
            {"name": "zero", "arity": 0, "recursiveFields": []},
            {"name": "succ", "arity": 1, "recursiveFields": [0]},
        ],
    });
    env.datatypes.insert("Naturals".into(), parse_datatype(&raw)?);
    Ok(())
}

// Recursion.

fn check_pattern(env: &Environment, pattern: &Pattern) -> Result<()> {
    match pattern {
        Pattern::Bind(name) => {
            if name.is_empty() {
                return fail("empty pattern variable");
            }
            Ok(())
        }
        Pattern::Ctor(name, args) => {
            match env.constructor(name) {
                Some(ctor) if ctor.arity == args.len() => {}
                _ => return fail("bad constructor pattern"),
            }
            for child in args {
                check_pattern(env, child)?;
            }
            Ok(())
        }
    }
}

fn check_recursive_body(env: &Environment, term: &Term, name: &str, arity: usize, position: usize, smaller: &BTreeSet<String>) -> Result<()> {
    match term {
        Term::Var(_) | Term::Nat(_) => env.check_term(term),
        Term::App(fn_name, args) => {
            if fn_name == name {
                let ok = args.len() == arity && matches!(&args[position], Term::Var(variable) if smaller.contains(variable));
                if !ok {
                    return fail("recursive call is not structurally smaller");
                }
            } else if env.functions.get(fn_name) != Some(&args.len()) {
                return fail("unknown function in recursive body");
            }
            for argument in args {
                check_recursive_body(env, argument, name, arity, position, smaller)?;
            }
            Ok(())
        }
    }
}

fn collect_calls<'a>(term: &'a Term, name: &str, arity: usize, env: &Environment, result: &mut Vec<&'a Term>) -> Result<()> {
    match term {
        Term::Var(_) | Term::Nat(_) => Ok(()),
        Term::App(fn_name, args) => {
            if fn_name == name {
                if args.len() != arity {
                    return fail("bad recursive call arity");
                }
                result.push(term);
            } else if env.functions.get(fn_name) != Some(&args.len()) {
                return fail("unknown function in recursive clause");
            }
            for argument in args {
                collect_calls(argument, name, arity, env, result)?;
            }
            Ok(())
        }
    }
}

struct Equations {
    raw: Value,
    parsed: Vec<(Vec<Pattern>, Term)>,
}

fn parse_equations(options: &Value) -> Result<Equations> {
    let raw = get(options, "equations")?.clone();
    let parsed = match &raw {
        Value::Array(items) => items
            .iter()
            .map(|item| {
                let patterns = match item.get("patterns") {
                    Some(Value::Array(patterns)) => patterns.iter().map(Pattern::from_json).collect::<Result<Vec<_>>>()?,
                    _ => return fail("malformed recursive equation"),
                };
                Ok((patterns, get_term(item, "body")?))
            })
            .collect::<Result<Vec<_>>>()?,
        _ => return fail("malformed recursive equations"),
    };
    Ok(Equations { raw, parsed })
}

fn define_structural(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let datatype_name = get_str(options, "datatype")?;
    let position = get_usize(options, "decreasingParameter")?;
    let equations = parse_equations(options)?;
    env.fresh_name(&name)?;
    params(env, &parameters)?;
    let datatype = match env.datatypes.get(&datatype_name) {
        Some(datatype) if position < parameters.len() && equations.parsed.len() == datatype.constructors.len() => datatype.clone(),
        _ => return fail("malformed structural recursion"),
    };
    let mut seen = BTreeSet::new();
    let mut properties = Vec::new();
    for (equation_index, (patterns, body)) in equations.parsed.iter().enumerate() {
        if patterns.len() != parameters.len() || patterns.iter().enumerate().any(|(index, pattern)| index != position && !matches!(pattern, Pattern::Bind(_))) {
            return fail("malformed recursive equation");
        }
        let (root_name, root_args) = match &patterns[position] {
            Pattern::Ctor(root_name, root_args) => (root_name, root_args),
            _ => return fail("bad constructor coverage"),
        };
        let ctor = match datatype.constructors.iter().find(|item| &item.name == root_name) {
            Some(ctor) if root_args.len() == ctor.arity && !seen.contains(root_name) => ctor,
            _ => return fail("bad constructor coverage"),
        };
        for pattern in patterns {
            check_pattern(env, pattern)?;
        }
        seen.insert(root_name.clone());
        let mut bindings = Vec::new();
        pattern_bindings(patterns, &mut bindings);
        let distinct: BTreeSet<String> = bindings.iter().cloned().collect();
        if distinct.len() != bindings.len() || !subset(&free_term(body), &distinct) {
            return fail("bad recursive bindings");
        }
        let mut smaller = BTreeSet::new();
        for field in &ctor.recursive_fields {
            let mut names = Vec::new();
            pattern_bindings(std::slice::from_ref(&root_args[*field]), &mut names);
            smaller.extend(names);
        }
        check_recursive_body(env, body, &name, parameters.len(), position, &smaller)?;
        let lhs = app(&name, patterns.iter().map(pattern_term).collect());
        properties.push((format!("equation.{equation_index}"), foralls(&bindings, eq(lhs, body.clone()))));
    }
    if seen.len() != datatype.constructors.len() {
        return fail("nonexhaustive recursion");
    }
    env.functions.insert(name.clone(), parameters.len());
    let raw = json!({
        "name": name, "parameters": parameters, "datatype": datatype_name,
        "decreasingParameter": position, "equations": equations.raw, "admission": "structural",
    });
    env.recursive.insert(name.clone(), parse_recursive(&raw)?);
    env.record_definition(&name, "recursive", &parameters, properties)
}

/// Recursion along a proved well-founded relation on a measure.
fn define_well_founded(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let datatype_name = get_str(options, "coverageDatatype")?;
    let position = get_usize(options, "coverageParameter")?;
    let equations = parse_equations(options)?;
    let relation = get_term(options, "relation")?;
    let domain = get_term(options, "domain")?;
    let measure = get_term(options, "measure")?;
    env.fresh_name(&name)?;
    params(env, &parameters)?;
    env.check_term(&relation)?;
    env.check_term(&domain)?;
    env.check_term(&measure)?;
    if !free_term(&relation).is_empty() || !free_term(&domain).is_empty() || !subset(&free_term(&measure), &set_of(&parameters)) {
        return fail("undeclared variable in termination data");
    }
    let datatype = match env.datatypes.get(&datatype_name) {
        Some(datatype) if position < parameters.len() && equations.parsed.len() == datatype.constructors.len() => datatype.clone(),
        _ => return fail("malformed well-founded recursion"),
    };
    let expected_well_founded = pred("wellFoundedOn", vec![relation.clone(), domain.clone()]);
    if !same_formula(&check_proof_value(env, get(options, "wellFounded")?)?, &expected_well_founded) {
        return fail("wrong well-foundedness proof");
    }
    let expected_measure = foralls(&parameters, pred("in", vec![measure.clone(), domain.clone()]));
    if !same_formula(&check_proof_value(env, get(options, "measureInDomain")?)?, &expected_measure) {
        return fail("wrong measure-domain proof");
    }
    let mut seen = BTreeSet::new();
    let mut properties = Vec::new();
    let mut obligations = Vec::new();
    for (equation_index, (patterns, body)) in equations.parsed.iter().enumerate() {
        if patterns.len() != parameters.len() || patterns.iter().enumerate().any(|(index, pattern)| index != position && !matches!(pattern, Pattern::Bind(_))) {
            return fail("malformed recursive equation");
        }
        let (root_name, root_args) = match &patterns[position] {
            Pattern::Ctor(root_name, root_args) => (root_name, root_args),
            _ => return fail("bad constructor coverage"),
        };
        match datatype.constructors.iter().find(|item| &item.name == root_name) {
            Some(ctor) if root_args.len() == ctor.arity && !seen.contains(root_name) => {}
            _ => return fail("bad constructor coverage"),
        }
        for pattern in patterns {
            check_pattern(env, pattern)?;
        }
        seen.insert(root_name.clone());
        let mut bindings = Vec::new();
        pattern_bindings(patterns, &mut bindings);
        let distinct: BTreeSet<String> = bindings.iter().cloned().collect();
        if distinct.len() != bindings.len() || !subset(&free_term(body), &distinct) {
            return fail("bad recursive bindings");
        }
        let mut calls = Vec::new();
        collect_calls(body, &name, parameters.len(), env, &mut calls)?;
        let current: Vec<Term> = patterns.iter().map(pattern_term).collect();
        let current_measure = substitute_simultaneous(&measure, &parameters.iter().cloned().zip(current.iter().cloned()).collect());
        for call in calls {
            if let Term::App(_, args) = call {
                let next_measure = substitute_simultaneous(&measure, &parameters.iter().cloned().zip(args.iter().cloned()).collect());
                obligations.push(foralls(&bindings, pred("relates", vec![relation.clone(), next_measure, current_measure.clone()])));
            }
        }
        properties.push((format!("equation.{equation_index}"), foralls(&bindings, eq(app(&name, current), body.clone()))));
    }
    if seen.len() != datatype.constructors.len() {
        return fail("nonexhaustive recursion");
    }
    let decreases = match get(options, "decreases")? {
        Value::Array(items) => items,
        _ => return fail("malformed decrease proofs"),
    };
    if decreases.len() != obligations.len() {
        return fail("wrong number of decrease proofs");
    }
    for (index, expected) in obligations.iter().enumerate() {
        if !same_formula(&check_proof_value(env, &decreases[index])?, expected) {
            return fail("wrong decrease proof");
        }
        properties.push((format!("termination.decrease.{index}"), expected.clone()));
    }
    env.functions.insert(name.clone(), parameters.len());
    let raw = json!({
        "name": name, "parameters": parameters, "datatype": datatype_name,
        "decreasingParameter": position, "equations": equations.raw, "admission": "well-founded",
        "termination": {"relation": relation.to_json(), "domain": domain.to_json(), "measure": measure.to_json()},
    });
    env.recursive.insert(name.clone(), parse_recursive(&raw)?);
    properties.push(("termination.wellFounded".into(), expected_well_founded));
    properties.push(("termination.measure".into(), expected_measure));
    env.record_definition(&name, "well-founded-recursive", &parameters, properties)
}

// Replacement, reified operations, and unique descriptions.

fn define_replacement(env: &mut Environment, options: &Value) -> Result<()> {
    if !env.capability("replacement") {
        return fail("foundation does not enable Replacement");
    }
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let domain = get_term(options, "domain")?;
    let input = get_str(options, "input")?;
    let output = get_str(options, "output")?;
    let relation = get_formula(options, "relation")?;
    params(env, &parameters)?;
    env.fresh_name(&name)?;
    env.check_term(&domain)?;
    env.check_formula(&relation)?;
    let mut domain_functions = BTreeSet::new();
    functions_in_term(&domain, &mut domain_functions);
    let mut relation_symbols = BTreeSet::new();
    symbols_in_formula(&relation, &mut relation_symbols);
    if input == output || parameters.contains(&input) || parameters.contains(&output) || domain_functions.contains(&name) || relation_symbols.contains(&name) {
        return fail("malformed Replacement instance");
    }
    let mut allowed = set_of(&parameters);
    allowed.insert(input.clone());
    allowed.insert(output.clone());
    if !subset(&free_term(&domain), &set_of(&parameters)) || !subset(&free_formula(&relation), &allowed) {
        return fail("undeclared Replacement variable");
    }
    let mut forbidden = allowed.clone();
    forbidden.extend(free_formula(&relation));
    let unique = fresh(&format!("{output}_other"), &forbidden);
    let at_unique = substitute_formula(&relation, &output, &v(&unique));
    let expected = foralls(
        &parameters,
        forall(
            &input,
            imp(
                pred("in", vec![v(&input), domain.clone()]),
                exists(&output, and(relation.clone(), forall(&unique, imp(at_unique, eq(v(&unique), v(&output)))))),
            ),
        ),
    );
    if !same_formula(&check_proof_value(env, get(options, "functionality")?)?, &expected) {
        return fail("wrong Replacement functionality proof");
    }
    env.functions.insert(name.clone(), parameters.len());
    let member = fresh("member", &forbidden);
    let at_member = substitute_formula(&relation, &output, &v(&member));
    let membership = foralls(
        &[parameters.clone(), vec![member.clone()]].concat(),
        iff(pred("in", vec![v(&member), app(&name, vars(&parameters))]), exists(&input, and(pred("in", vec![v(&input), domain]), at_member))),
    );
    env.record_definition(&name, "replacement", &parameters, vec![("functionality".into(), expected), ("membership".into(), membership)])
}

fn reify_unary_operation(env: &mut Environment, options: &Value) -> Result<()> {
    if !env.capability("replacement") {
        return fail("foundation does not enable Replacement");
    }
    let name = get_str(options, "name")?;
    let operation = get_str(options, "operation")?;
    let variable = get_str(options, "variable")?;
    let domain = get_term(options, "domain")?;
    let codomain = get_term(options, "codomain")?;
    env.fresh_name(&name)?;
    if env.functions.get(&operation) != Some(&1) {
        return fail("reified operation is not a declared unary function");
    }
    env.check_term(&domain)?;
    env.check_term(&codomain)?;
    if !free_term(&domain).is_empty() || !free_term(&codomain).is_empty() || variable.is_empty() {
        return fail("malformed reified operation");
    }
    let expected = forall(&variable, imp(pred("in", vec![v(&variable), domain.clone()]), pred("in", vec![app(&operation, vec![v(&variable)]), codomain.clone()])));
    if !same_formula(&check_proof_value(env, get(options, "closure")?)?, &expected) {
        return fail("wrong closure proof");
    }
    env.functions.insert(name.clone(), 0);
    let graph = app(&name, vec![]);
    let pair_variable = if variable == "p" { "pair_" } else { "p" };
    let membership = forall(
        pair_variable,
        iff(
            pred("in", vec![v(pair_variable), graph.clone()]),
            exists(
                &variable,
                and(
                    pred("in", vec![v(&variable), domain.clone()]),
                    eq(v(pair_variable), app("orderedPair", vec![v(&variable), app(&operation, vec![v(&variable)])])),
                ),
            ),
        ),
    );
    let function_on = pred("functionOn", vec![graph.clone(), domain.clone(), codomain]);
    let application = forall(
        &variable,
        imp(pred("in", vec![v(&variable), domain]), eq(app("apply", vec![graph, v(&variable)]), app(&operation, vec![v(&variable)]))),
    );
    env.record_definition(
        &name,
        "replacement",
        &[],
        vec![("membership".into(), membership), ("functionOn".into(), function_on), ("application".into(), application)],
    )
}

fn define_unique(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let value = get_str(options, "value")?;
    let relation = get_formula(options, "relation")?;
    env.fresh_name(&name)?;
    params(env, &parameters)?;
    env.check_formula(&relation)?;
    let mut allowed = set_of(&parameters);
    allowed.insert(value.clone());
    if value.is_empty() || parameters.contains(&value) || !subset(&free_formula(&relation), &allowed) {
        return fail("malformed unique description");
    }
    let mut forbidden = allowed.clone();
    forbidden.extend(free_formula(&relation));
    let other = fresh(&format!("{value}_other"), &forbidden);
    let other_relation = substitute_formula(&relation, &value, &v(&other));
    let expected = foralls(&parameters, exists(&value, and(relation.clone(), forall(&other, imp(other_relation, eq(v(&other), v(&value)))))));
    if !same_formula(&check_proof_value(env, get(options, "existsUnique")?)?, &expected) {
        return fail("wrong unique-existence proof");
    }
    env.functions.insert(name.clone(), parameters.len());
    let characterization = foralls(&parameters, substitute_formula(&relation, &value, &app(&name, vars(&parameters))));
    env.record_definition(&name, "unique-choice", &parameters, vec![("existsUnique".into(), expected), ("characterization".into(), characterization)])
}

// Set-recursion events.

fn recursion_capabilities(env: &Environment, what: &str) -> Result<()> {
    if !env.capability("separation") || !env.capability("replacement") || !env.axioms.contains_key("set.foundation") {
        return fail(format!("foundation does not enable {what}"));
    }
    Ok(())
}

fn distinct_variables(parameters: &[String], extra: &[&String]) -> bool {
    let mut all: Vec<&String> = parameters.iter().collect();
    all.extend(extra.iter().copied());
    let distinct: BTreeSet<&String> = all.iter().copied().collect();
    extra.iter().all(|name| !name.is_empty()) && distinct.len() == all.len()
}

fn define_membership_recursion(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let variable = get_str(options, "variable")?;
    let predecessor = get_str(options, "predecessor")?;
    let history = get_str(options, "history")?;
    let step = get_term(options, "step")?;
    recursion_capabilities(env, "membership recursion")?;
    let history_name = format!("{name}.history");
    env.fresh_name(&name)?;
    env.fresh_name(&history_name)?;
    params(env, &parameters)?;
    if !distinct_variables(&parameters, &[&variable, &predecessor, &history]) {
        return fail("bad membership recursion variables");
    }
    env.check_term(&step)?;
    let mut allowed = set_of(&parameters);
    allowed.insert(variable.clone());
    allowed.insert(history.clone());
    if !subset(&free_term(&step), &allowed) {
        return fail("bad membership recursion step");
    }
    let arity = parameters.len() + 1;
    env.functions.insert(name.clone(), arity);
    env.functions.insert(history_name.clone(), arity);
    let mut forbidden = set_of(&parameters);
    forbidden.extend([variable.clone(), predecessor.clone(), history.clone()]);
    let pair_name = fresh("pair", &forbidden);
    let history_term = app(&history_name, [vars(&parameters), vec![v(&variable)]].concat());
    let value_at_predecessor = app(&name, [vars(&parameters), vec![v(&predecessor)]].concat());
    let membership = foralls(
        &[parameters.clone(), vec![variable.clone(), pair_name.clone()]].concat(),
        iff(
            pred("in", vec![v(&pair_name), history_term.clone()]),
            exists(
                &predecessor,
                and(pred("in", vec![v(&predecessor), v(&variable)]), eq(v(&pair_name), app("orderedPair", vec![v(&predecessor), value_at_predecessor]))),
            ),
        ),
    );
    let value = app(&name, [vars(&parameters), vec![v(&variable)]].concat());
    let equation = foralls(&[parameters.clone(), vec![variable.clone()]].concat(), eq(value, substitute_term(&step, &history, &history_term)));
    env.record_definition(
        &name,
        "membership-recursive",
        &[parameters.clone(), vec![variable]].concat(),
        vec![("history.membership".into(), membership), ("equation".into(), equation)],
    )
}

fn define_well_founded_set_function(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let variable = get_str(options, "variable")?;
    let predecessor = get_str(options, "predecessor")?;
    let history = get_str(options, "history")?;
    let domain = get_term(options, "domain")?;
    let precedes = get_formula(options, "precedes")?;
    let step = get_term(options, "step")?;
    recursion_capabilities(env, "set well-founded recursion")?;
    let solution_name = format!("{name}.Solution");
    let history_name = format!("{name}.history");
    env.fresh_name(&name)?;
    env.fresh_name(&solution_name)?;
    env.fresh_name(&history_name)?;
    params(env, &parameters)?;
    if !distinct_variables(&parameters, &[&variable, &predecessor, &history]) {
        return fail("bad set-recursion variables");
    }
    env.check_term(&domain)?;
    env.check_formula(&precedes)?;
    env.check_term(&step)?;
    let mut precedes_allowed = set_of(&parameters);
    precedes_allowed.extend([predecessor.clone(), variable.clone()]);
    let mut step_allowed = set_of(&parameters);
    step_allowed.extend([variable.clone(), history.clone()]);
    if !subset(&free_term(&domain), &set_of(&parameters)) || !subset(&free_formula(&precedes), &precedes_allowed) || !subset(&free_term(&step), &step_allowed) {
        return fail("undeclared set-recursion variable");
    }
    let mut forbidden = set_of(&parameters);
    forbidden.extend([variable.clone(), predecessor.clone(), history.clone()]);
    forbidden.extend(free_term(&domain));
    forbidden.extend(free_formula(&precedes));
    forbidden.extend(free_term(&step));
    let take = |base: &str, forbidden: &mut BTreeSet<String>| {
        let name = fresh(base, forbidden);
        forbidden.insert(name.clone());
        name
    };
    let subset_name = take("subset", &mut forbidden);
    let minimum = take("minimum", &mut forbidden);
    let member = take("member", &mut forbidden);
    let graph = take("graph", &mut forbidden);
    let other_graph = take("otherGraph", &mut forbidden);
    let output = take("output", &mut forbidden);
    let other_output = take("otherOutput", &mut forbidden);
    let at_relation = |earlier: &Term, later: &Term| substitute_formula(&substitute_formula(&precedes, &predecessor, earlier), &variable, later);
    let domain_subset = forall(&member, imp(pred("in", vec![v(&member), v(&subset_name)]), pred("in", vec![v(&member), domain.clone()])));
    let minimal = exists(
        &minimum,
        and(
            pred("in", vec![v(&minimum), v(&subset_name)]),
            forall(&predecessor, imp(at_relation(&v(&predecessor), &v(&minimum)), neg(pred("in", vec![v(&predecessor), v(&subset_name)])))),
        ),
    );
    let expected_well_founded = foralls(
        &parameters,
        forall(&subset_name, imp(domain_subset, imp(neg(eq(v(&subset_name), app("empty", vec![]))), minimal))),
    );
    if !same_formula(&check_proof_value(env, get(options, "wellFounded")?)?, &expected_well_founded) {
        return fail("wrong set-well-foundedness proof");
    }
    let history_formula = |graph_term: &Term, point: &Term, history_term: &Term| -> Formula {
        let pair_value = fresh("pairValue", &forbidden);
        let mut forbidden_earlier = forbidden.clone();
        forbidden_earlier.insert(pair_value.clone());
        let earlier = fresh("earlier", &forbidden_earlier);
        forbidden_earlier.insert(earlier.clone());
        let earlier_value = fresh("earlierValue", &forbidden_earlier);
        let prior_pair = exists(
            &earlier,
            exists(
                &earlier_value,
                and(
                    pred("in", vec![v(&earlier), domain.clone()]),
                    and(at_relation(&v(&earlier), point), eq(v(&pair_value), app("orderedPair", vec![v(&earlier), v(&earlier_value)]))),
                ),
            ),
        );
        forall(
            &pair_value,
            iff(pred("in", vec![v(&pair_value), history_term.clone()]), and(pred("in", vec![v(&pair_value), graph_term.clone()]), prior_pair)),
        )
    };
    let graph_shape = and(
        forall(
            &member,
            imp(
                pred("in", vec![v(&member), v(&graph)]),
                exists(
                    &variable,
                    exists(
                        &output,
                        and(pred("in", vec![v(&variable), domain.clone()]), eq(v(&member), app("orderedPair", vec![v(&variable), v(&output)]))),
                    ),
                ),
            ),
        ),
        and(
            forall(
                &variable,
                imp(
                    pred("in", vec![v(&variable), domain.clone()]),
                    exists(&output, pred("in", vec![app("orderedPair", vec![v(&variable), v(&output)]), v(&graph)])),
                ),
            ),
            forall(
                &variable,
                imp(
                    pred("in", vec![v(&variable), domain.clone()]),
                    forall(
                        &output,
                        forall(
                            &other_output,
                            imp(
                                and(
                                    pred("in", vec![app("orderedPair", vec![v(&variable), v(&output)]), v(&graph)]),
                                    pred("in", vec![app("orderedPair", vec![v(&variable), v(&other_output)]), v(&graph)]),
                                ),
                                eq(v(&output), v(&other_output)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    );
    let instantiated_step = substitute_many(&step, &[(variable.clone(), v(&variable)), (history.clone(), v(&history))]);
    let solution_body = and(
        graph_shape,
        forall(
            &variable,
            imp(
                pred("in", vec![v(&variable), domain.clone()]),
                exists(
                    &history,
                    exists(
                        &output,
                        and(
                            history_formula(&v(&graph), &v(&variable), &v(&history)),
                            and(pred("in", vec![app("orderedPair", vec![v(&variable), v(&output)]), v(&graph)]), eq(v(&output), instantiated_step.clone())),
                        ),
                    ),
                ),
            ),
        ),
    );
    env.predicates.insert(solution_name.clone(), parameters.len() + 1);
    let solution_at = |graph_term: Term| pred(&solution_name, [vars(&parameters), vec![graph_term]].concat());
    let solution_equation = foralls(&[parameters.clone(), vec![graph.clone()]].concat(), iff(solution_at(v(&graph)), solution_body));
    env.record_definition(&solution_name, "predicate", &[parameters.clone(), vec![graph.clone()]].concat(), vec![("equation".into(), solution_equation)])?;
    let existence_unique = foralls(
        &parameters,
        exists(&graph, and(solution_at(v(&graph)), forall(&other_graph, imp(solution_at(v(&other_graph)), eq(v(&other_graph), v(&graph)))))),
    );
    let arity = parameters.len() + 1;
    env.functions.insert(name.clone(), arity);
    env.functions.insert(history_name.clone(), arity);
    let value_term = app(&name, [vars(&parameters), vec![v(&variable)]].concat());
    let history_term = app(&history_name, [vars(&parameters), vec![v(&variable)]].concat());
    let value_at_predecessor = app(&name, [vars(&parameters), vec![v(&predecessor)]].concat());
    let history_member = fresh("historyMember", &forbidden);
    let history_membership = foralls(
        &[parameters.clone(), vec![variable.clone(), history_member.clone()]].concat(),
        iff(
            pred("in", vec![v(&history_member), history_term.clone()]),
            exists(
                &predecessor,
                and(
                    pred("in", vec![v(&predecessor), domain.clone()]),
                    and(
                        at_relation(&v(&predecessor), &v(&variable)),
                        eq(v(&history_member), app("orderedPair", vec![v(&predecessor), value_at_predecessor])),
                    ),
                ),
            ),
        ),
    );
    let binders = [parameters.clone(), vec![variable.clone()]].concat();
    let value_property = foralls(
        &binders,
        imp(
            pred("in", vec![v(&variable), domain.clone()]),
            exists(&graph, and(solution_at(v(&graph)), pred("in", vec![app("orderedPair", vec![v(&variable), value_term.clone()]), v(&graph)]))),
        ),
    );
    let equation_property = foralls(
        &binders,
        imp(
            pred("in", vec![v(&variable), domain.clone()]),
            exists(
                &graph,
                exists(
                    &history,
                    and(solution_at(v(&graph)), and(history_formula(&v(&graph), &v(&variable), &v(&history)), eq(value_term.clone(), instantiated_step))),
                ),
            ),
        ),
    );
    let direct_step = substitute_many(&step, &[(variable.clone(), v(&variable)), (history.clone(), history_term)]);
    let direct_equation = foralls(&binders, imp(pred("in", vec![v(&variable), domain.clone()]), eq(value_term.clone(), direct_step)));
    let outside = foralls(&binders, imp(neg(pred("in", vec![v(&variable), domain])), eq(value_term, app("empty", vec![]))));
    env.record_definition(
        &name,
        "well-founded-set-recursive",
        &binders,
        vec![
            ("wellFounded".into(), expected_well_founded),
            ("solution.existsUnique".into(), existence_unique),
            ("history.membership".into(), history_membership),
            ("value".into(), value_property),
            ("equation".into(), equation_property),
            ("equation.direct".into(), direct_equation),
            ("outside".into(), outside),
        ],
    )
}

fn normalize_term(env: &Environment, term: &Term, fuel: u32) -> Result<Term> {
    if fuel < 1 {
        return fail("definitional normalization exhausted");
    }
    let (fn_name, args) = match term {
        Term::App(fn_name, args) => (fn_name, args),
        _ => return Ok(term.clone()),
    };
    let normalized: Vec<Term> = args.iter().map(|arg| normalize_term(env, arg, fuel - 1)).collect::<Result<Vec<_>>>()?;
    if !env.is_constructor(fn_name) {
        if let Some(body) = env.bodies.get(fn_name) {
            let substitutions: Vec<(String, Term)> = body.parameters.iter().cloned().zip(normalized.iter().cloned()).collect();
            let instance = substitute_many(&body.body, &substitutions);
            return normalize_term(env, &instance, fuel - 1);
        }
    }
    Ok(Term::App(fn_name.clone(), normalized))
}

fn expand_formula(env: &Environment, formula: &Formula, fuel: u32) -> Result<Formula> {
    if fuel < 1 {
        return fail("definitional expansion exhausted");
    }
    match formula {
        Formula::Bottom => Ok(Formula::Bottom),
        Formula::Eq(left, right) => Ok(eq(normalize_term(env, left, 10_000)?, normalize_term(env, right, 10_000)?)),
        Formula::Pred(name, args) => {
            let equation = env
                .definitions
                .get(name)
                .filter(|definition| definition.kind == "predicate")
                .and_then(|_| env.property(name, "equation"));
            if let Some(equation) = equation {
                let mut parameters = Vec::new();
                let mut body = equation;
                while let Formula::Forall(variable, inner) = body {
                    parameters.push(variable.clone());
                    body = inner;
                }
                if let Formula::Iff(left, right) = body {
                    if parameters.len() == args.len() {
                        let instance = match (&**left, &**right) {
                            (Formula::Pred(head, _), _) if head == name => Some((**right).clone()),
                            (_, Formula::Pred(head, _)) if head == name => Some((**left).clone()),
                            _ => None,
                        };
                        if let Some(mut instance) = instance {
                            for (parameter, argument) in parameters.iter().zip(args) {
                                instance = substitute_formula(&instance, parameter, argument);
                            }
                            return expand_formula(env, &instance, fuel - 1);
                        }
                    }
                }
            }
            Ok(Formula::Pred(name.clone(), args.iter().map(|arg| normalize_term(env, arg, 10_000)).collect::<Result<Vec<_>>>()?))
        }
        Formula::Imp(left, right) | Formula::And(left, right) | Formula::Or(left, right) | Formula::Iff(left, right) => {
            Ok(binary(formula.tag(), expand_formula(env, left, fuel - 1)?, expand_formula(env, right, fuel - 1)?))
        }
        Formula::Forall(variable, body) | Formula::Exists(variable, body) => Ok(quantify(formula.tag(), variable, expand_formula(env, body, fuel - 1)?)),
    }
}

fn von_neumann_transitive(term: &Term) -> Formula {
    let member = fresh("member", &free_term(term));
    let mut forbidden = free_term(term);
    forbidden.insert(member.clone());
    let element = fresh("element", &forbidden);
    forall(
        &member,
        imp(
            pred("in", vec![v(&member), term.clone()]),
            forall(&element, imp(pred("in", vec![v(&element), v(&member)]), pred("in", vec![v(&element), term.clone()]))),
        ),
    )
}

fn von_neumann_ordinal(term: &Term) -> Formula {
    let member = fresh("ordinalMember", &free_term(term));
    and(von_neumann_transitive(term), forall(&member, imp(pred("in", vec![v(&member), term.clone()]), von_neumann_transitive(&v(&member)))))
}

fn von_neumann_limit(term: &Term, successor: &dyn Fn(Term) -> Term) -> Formula {
    let member = fresh("limitMember", &free_term(term));
    and(
        von_neumann_ordinal(term),
        and(
            neg(eq(term.clone(), app("empty", vec![]))),
            forall(&member, imp(pred("in", vec![v(&member), term.clone()]), pred("in", vec![successor(v(&member)), term.clone()]))),
        ),
    )
}

fn define_transfinite(env: &mut Environment, options: &Value) -> Result<()> {
    let name = get_str(options, "name")?;
    let parameters = get_strings(options, "parameters")?;
    let ordinal = get_str(options, "ordinal")?;
    let predecessor = get_str(options, "predecessor")?;
    let history = get_str(options, "history")?;
    let zero = get_term(options, "zero")?;
    let successor = get_term(options, "successor")?;
    let limit = get_term(options, "limit")?;
    recursion_capabilities(env, "transfinite recursion")?;
    let history_name = format!("{name}.history");
    env.fresh_name(&name)?;
    env.fresh_name(&history_name)?;
    params(env, &parameters)?;
    if !distinct_variables(&parameters, &[&ordinal, &predecessor, &history]) {
        return fail("bad transfinite recursion variables");
    }
    let arity = parameters.len() + 1;
    env.functions.insert(name.clone(), arity);
    env.check_term(&zero)?;
    env.check_term(&successor)?;
    env.check_term(&limit)?;
    let mut successor_allowed = set_of(&parameters);
    successor_allowed.insert(predecessor.clone());
    let mut limit_allowed = set_of(&parameters);
    limit_allowed.extend([ordinal.clone(), history.clone()]);
    if !subset(&free_term(&zero), &set_of(&parameters)) || !subset(&free_term(&successor), &successor_allowed) || !subset(&free_term(&limit), &limit_allowed) {
        return fail("bad transfinite clause variables");
    }
    let mut zero_calls = Vec::new();
    collect_calls(&zero, &name, arity, env, &mut zero_calls)?;
    let mut limit_calls = Vec::new();
    collect_calls(&limit, &name, arity, env, &mut limit_calls)?;
    if !zero_calls.is_empty() || !limit_calls.is_empty() {
        return fail("recursion outside successor clause");
    }
    let expected_call: Vec<Term> = [vars(&parameters), vec![v(&predecessor)]].concat();
    let mut successor_calls = Vec::new();
    collect_calls(&successor, &name, arity, env, &mut successor_calls)?;
    for call in successor_calls {
        if let Term::App(_, args) = call {
            if args.len() != expected_call.len() || args.iter().zip(&expected_call).any(|(actual, expected)| !same_term(actual, expected)) {
                return fail("transfinite recursion does not call immediate predecessor");
            }
        }
    }
    let successor_index = match options.get("successorIndex") {
        Some(Value::String(text)) if !text.is_empty() => Some(text.clone()),
        _ => None,
    };
    let mut probe_forbidden = set_of(&parameters);
    probe_forbidden.extend([ordinal.clone(), predecessor.clone(), history.clone()]);
    if let Some(index) = &successor_index {
        if env.functions.get(index) != Some(&1) {
            return fail("bad ordinal successor");
        }
        let probe = v(&fresh("ordinalProbe", &probe_forbidden));
        let canonical_successor = app("union2", vec![probe.clone(), app("singleton", vec![probe.clone()])]);
        if !same_term(&normalize_term(env, &app(index, vec![probe]), 10_000)?, &normalize_term(env, &canonical_successor, 10_000)?) {
            return fail("noncanonical ordinal successor");
        }
    }
    let next_term = |term: Term| -> Term {
        match &successor_index {
            Some(index) => app(index, vec![term]),
            None => app("union2", vec![term.clone(), app("singleton", vec![term])]),
        }
    };
    let canonical_ordinal = von_neumann_ordinal(&v(&ordinal));
    let canonical_limit = von_neumann_limit(&v(&ordinal), &next_term);
    let ordinal_condition = match options.get("ordinalCondition") {
        Some(Value::Null) | None => None,
        Some(value) => Some(Formula::from_json(value)?),
    };
    let limit_condition = match options.get("limitCondition") {
        Some(Value::Null) | None => None,
        Some(value) => Some(Formula::from_json(value)?),
    };
    let only_ordinal: BTreeSet<String> = [ordinal.clone()].into_iter().collect();
    if let Some(condition) = &ordinal_condition {
        if !subset(&free_formula(condition), &only_ordinal) || !same_formula(&expand_formula(env, condition, 10_000)?, &expand_formula(env, &canonical_ordinal, 10_000)?) {
            return fail("noncanonical ordinal interface");
        }
    }
    if let Some(condition) = &limit_condition {
        if !subset(&free_formula(condition), &only_ordinal) || !same_formula(&expand_formula(env, condition, 10_000)?, &expand_formula(env, &canonical_limit, 10_000)?) {
            return fail("noncanonical limit interface");
        }
    }
    let ordinal_at = |term: &Term| match &ordinal_condition {
        Some(condition) => substitute_formula(condition, &ordinal, term),
        None => von_neumann_ordinal(term),
    };
    let limit_at = |term: &Term| match &limit_condition {
        Some(condition) => substitute_formula(condition, &ordinal, term),
        None => von_neumann_limit(term, &next_term),
    };
    env.functions.insert(history_name.clone(), arity);
    let pair_name = fresh("pair", &probe_forbidden);
    let mut earlier_forbidden = probe_forbidden.clone();
    earlier_forbidden.insert(pair_name.clone());
    let earlier = fresh("earlier", &earlier_forbidden);
    let history_term = app(&history_name, [vars(&parameters), vec![v(&ordinal)]].concat());
    let value = |index: Term| app(&name, [vars(&parameters), vec![index]].concat());
    let history_membership = foralls(
        &[parameters.clone(), vec![ordinal.clone(), pair_name.clone()]].concat(),
        iff(
            pred("in", vec![v(&pair_name), history_term.clone()]),
            exists(
                &earlier,
                and(pred("in", vec![v(&earlier), v(&ordinal)]), eq(v(&pair_name), app("orderedPair", vec![v(&earlier), value(v(&earlier))]))),
            ),
        ),
    );
    let properties = vec![
        ("history.membership".to_string(), history_membership),
        ("equation.zero".to_string(), foralls(&parameters, eq(value(nat(0)), zero))),
        (
            "equation.successor".to_string(),
            foralls(
                &[parameters.clone(), vec![predecessor.clone()]].concat(),
                imp(ordinal_at(&v(&predecessor)), eq(value(next_term(v(&predecessor))), successor)),
            ),
        ),
        (
            "equation.limit".to_string(),
            foralls(
                &[parameters.clone(), vec![ordinal.clone()]].concat(),
                imp(limit_at(&v(&ordinal)), eq(value(v(&ordinal)), substitute_term(&limit, &history, &history_term))),
            ),
        ),
        (
            "outside".to_string(),
            foralls(&[parameters.clone(), vec![ordinal.clone()]].concat(), imp(neg(ordinal_at(&v(&ordinal))), eq(value(v(&ordinal)), app("empty", vec![])))),
        ),
    ];
    env.record_definition(&name, "transfinite-recursive", &[parameters, vec![ordinal]].concat(), properties)
}

// Authenticated proof DAGs and named-rule proof checking.

pub struct ProofDag {
    nodes: Vec<Value>,
    root: usize,
}

fn references_backward(item: &Value, current: usize) -> bool {
    match item {
        Value::Object(map) if map.len() == 1 && map.contains_key("$proof") => match natural_int(&map["$proof"]) {
            Some(reference) => reference < current,
            None => false,
        },
        Value::Object(map) => map.values().all(|child| references_backward(child, current)),
        Value::Array(items) => items.iter().all(|child| references_backward(child, current)),
        _ => true,
    }
}

pub fn decode_proof_dag(wrapper: &Value) -> Result<ProofDag> {
    let dag = match wrapper {
        Value::Object(map) if map.len() == 1 && map.contains_key("$grace17ProofDag") => &map["$grace17ProofDag"],
        _ => return fail("malformed encoded proof"),
    };
    let mut body = Map::new();
    body.insert("version".into(), dag.get("version").cloned().unwrap_or(Value::Null));
    body.insert("nodes".into(), dag.get("nodes").cloned().unwrap_or(Value::Null));
    body.insert("root".into(), dag.get("root").cloned().unwrap_or(Value::Null));
    let digest = sha256_hex(canonical(&Value::Object(body))?.as_bytes());
    if dag.get("version") != Some(&Value::Number(1.into())) || dag.get("digest") != Some(&Value::String(digest)) {
        return fail("malformed or corrupted proof DAG");
    }
    let nodes = match dag.get("nodes") {
        Some(Value::Array(nodes)) => nodes,
        _ => return fail("malformed proof DAG"),
    };
    let root = match dag.get("root").and_then(natural_int) {
        Some(root) if root < nodes.len() => root,
        _ => return fail("malformed proof DAG"),
    };
    let mut decoded = Vec::with_capacity(nodes.len());
    for (index, node) in nodes.iter().enumerate() {
        let payload = match node {
            Value::Object(map) if map.len() == 1 && map.contains_key("payload") => &map["payload"],
            _ => return fail("malformed proof DAG node"),
        };
        if !references_backward(payload, index) {
            return fail("forward proof DAG reference");
        }
        match payload.get("rule") {
            Some(Value::String(_)) => {}
            _ => return fail("malformed proof DAG proof"),
        }
        decoded.push(payload.clone());
    }
    Ok(ProofDag { nodes: decoded, root })
}

impl ProofDag {
    fn resolve<'a>(&'a self, value: &'a Value) -> Result<&'a Value> {
        match value {
            Value::Object(map) if map.len() == 1 && map.contains_key("$proof") => match natural_int(&map["$proof"]) {
                Some(reference) if reference < self.nodes.len() => Ok(&self.nodes[reference]),
                _ => fail("malformed proof DAG reference"),
            },
            _ => Ok(value),
        }
    }

    fn proof<'a>(&'a self, node: &'a Value, key: &str) -> Result<&'a Value> {
        self.resolve(get(node, key)?)
    }
}

/// Check an admission proof wrapped as an authenticated DAG.
pub fn check_proof_value(env: &Environment, wrapper: &Value) -> Result<Formula> {
    let dag = decode_proof_dag(wrapper)?;
    let root = &dag.nodes[dag.root];
    check_proof(env, &dag, root, &[])
}

fn with_assumption(assumptions: &[Formula], extra: Formula) -> Vec<Formula> {
    let mut result = assumptions.to_vec();
    result.push(extra);
    result
}

pub fn check_proof(env: &Environment, dag: &ProofDag, proof: &Value, assumptions: &[Formula]) -> Result<Formula> {
    let rule = get_str(proof, "rule")?;
    match rule.as_str() {
        "assumption" => {
            let formula = get_formula(proof, "formula")?;
            env.check_formula(&formula)?;
            if !assumptions.iter().any(|item| same_formula(&formula, item)) {
                return fail("inactive assumption");
            }
            Ok(formula)
        }
        "axiom" => match env.axioms.get(&get_str(proof, "name")?) {
            Some(formula) => Ok(formula.clone()),
            None => fail("unknown axiom"),
        },
        "theorem" => match env.theorems.get(&get_str(proof, "name")?) {
            Some(formula) => Ok(formula.clone()),
            None => fail("unknown theorem"),
        },
        "definition" => {
            let property = match proof.get("property") {
                Some(Value::String(text)) => text.clone(),
                _ => "equation".to_string(),
            };
            match env.property(&get_str(proof, "name")?, &property) {
                Some(formula) => Ok(formula.clone()),
                None => fail("unknown definition property"),
            }
        }
        "refl" => {
            let term = get_term(proof, "term")?;
            env.check_term(&term)?;
            Ok(eq(term.clone(), term))
        }
        "compute" => {
            let left = get_term(proof, "left")?;
            let right = get_term(proof, "right")?;
            env.check_term(&left)?;
            env.check_term(&right)?;
            let definitions = get_strings(proof, "definitions")?;
            compute::check_computation(env, &left, &right, &definitions, false)?;
            Ok(eq(left, right))
        }
        "rationalClassCompute" => {
            let left = get_term(proof, "left")?;
            let right = get_term(proof, "right")?;
            env.check_term(&left)?;
            env.check_term(&right)?;
            compute::check_rational_class_equality(env, &left, &right)?;
            Ok(eq(left, right))
        }
        "symm" => match check_proof(env, dag, dag.proof(proof, "proof")?, assumptions)? {
            Formula::Eq(left, right) => Ok(eq(*right, *left)),
            _ => fail("symmetry needs equality"),
        },
        "trans" => {
            let left = check_proof(env, dag, dag.proof(proof, "left")?, assumptions)?;
            let right = check_proof(env, dag, dag.proof(proof, "right")?, assumptions)?;
            match (left, right) {
                (Formula::Eq(a, b), Formula::Eq(c, d)) if same_term(&b, &c) => Ok(eq(*a, *d)),
                _ => fail("bad transitivity"),
            }
        }
        "congr" => {
            let fn_name = get_str(proof, "fn")?;
            let proofs = match get(proof, "proofs")? {
                Value::Array(items) => items,
                _ => return fail("bad congruence"),
            };
            let mut lefts = Vec::with_capacity(proofs.len());
            let mut rights = Vec::with_capacity(proofs.len());
            for item in proofs {
                match check_proof(env, dag, dag.resolve(item)?, assumptions)? {
                    Formula::Eq(left, right) => {
                        lefts.push(*left);
                        rights.push(*right);
                    }
                    _ => return fail("bad congruence"),
                }
            }
            if env.functions.get(&fn_name) != Some(&proofs.len()) {
                return fail("bad congruence");
            }
            Ok(eq(app(&fn_name, lefts), app(&fn_name, rights)))
        }
        "impIntro" => {
            let assumption = get_formula(proof, "assumption")?;
            env.check_formula(&assumption)?;
            let body = check_proof(env, dag, dag.proof(proof, "body")?, &with_assumption(assumptions, assumption.clone()))?;
            Ok(imp(assumption, body))
        }
        "impElim" => {
            let implication = check_proof(env, dag, dag.proof(proof, "implication")?, assumptions)?;
            let argument = check_proof(env, dag, dag.proof(proof, "argument")?, assumptions)?;
            match implication {
                Formula::Imp(left, right) if same_formula(&left, &argument) => Ok(*right),
                _ => fail("bad implication elimination"),
            }
        }
        "forallIntro" => {
            let variable = get_str(proof, "variable")?;
            if assumptions.iter().any(|item| free_formula(item).contains(&variable)) {
                return fail("generalized variable is free in assumptions");
            }
            let body = check_proof(env, dag, dag.proof(proof, "body")?, assumptions)?;
            Ok(forall(&variable, body))
        }
        "forallElim" => {
            let universal = check_proof(env, dag, dag.proof(proof, "universal")?, assumptions)?;
            let term = get_term(proof, "term")?;
            env.check_term(&term)?;
            match universal {
                Formula::Forall(variable, body) => Ok(substitute_formula(&body, &variable, &term)),
                _ => fail("universal elimination needs a universal"),
            }
        }
        "eqElim" => {
            let equality = check_proof(env, dag, dag.proof(proof, "equality")?, assumptions)?;
            let evidence = check_proof(env, dag, dag.proof(proof, "evidence")?, assumptions)?;
            let motive = get_formula(proof, "motive")?;
            let variable = get_str(proof, "variable")?;
            let reverse = proof.get("reverse") == Some(&Value::Bool(true));
            let (source, target) = match equality {
                Formula::Eq(left, right) => {
                    if reverse {
                        (*right, *left)
                    } else {
                        (*left, *right)
                    }
                }
                _ => return fail("equality elimination needs equality"),
            };
            if !same_formula(&evidence, &substitute_formula(&motive, &variable, &source)) {
                return fail("bad equality evidence");
            }
            Ok(substitute_formula(&motive, &variable, &target))
        }
        "andIntro" => Ok(and(
            check_proof(env, dag, dag.proof(proof, "left")?, assumptions)?,
            check_proof(env, dag, dag.proof(proof, "right")?, assumptions)?,
        )),
        "andElimLeft" | "andElimRight" => match check_proof(env, dag, dag.proof(proof, "conjunction")?, assumptions)? {
            Formula::And(left, right) => Ok(if rule == "andElimLeft" { *left } else { *right }),
            _ => fail("conjunction elimination needs conjunction"),
        },
        "orIntroLeft" => {
            let right = get_formula(proof, "right")?;
            env.check_formula(&right)?;
            Ok(or(check_proof(env, dag, dag.proof(proof, "proof")?, assumptions)?, right))
        }
        "orIntroRight" => {
            let left = get_formula(proof, "left")?;
            env.check_formula(&left)?;
            Ok(or(left, check_proof(env, dag, dag.proof(proof, "proof")?, assumptions)?))
        }
        "orElim" => {
            let (left_case, right_case) = match check_proof(env, dag, dag.proof(proof, "disjunction")?, assumptions)? {
                Formula::Or(left, right) => (*left, *right),
                _ => return fail("or elimination needs disjunction"),
            };
            let left = check_proof(env, dag, dag.proof(proof, "left")?, &with_assumption(assumptions, left_case))?;
            let right = check_proof(env, dag, dag.proof(proof, "right")?, &with_assumption(assumptions, right_case))?;
            if !same_formula(&left, &right) {
                return fail("or branches disagree");
            }
            Ok(left)
        }
        "iffIntro" => {
            let forward = check_proof(env, dag, dag.proof(proof, "forward")?, assumptions)?;
            let backward = check_proof(env, dag, dag.proof(proof, "backward")?, assumptions)?;
            match (forward, backward) {
                (Formula::Imp(a, b), Formula::Imp(c, d)) if same_formula(&a, &d) && same_formula(&b, &c) => Ok(iff(*a, *b)),
                _ => fail("bad iff introduction"),
            }
        }
        "iffElimLeft" | "iffElimRight" => match check_proof(env, dag, dag.proof(proof, "equivalence")?, assumptions)? {
            Formula::Iff(left, right) => Ok(if rule == "iffElimLeft" { imp(*left, *right) } else { imp(*right, *left) }),
            _ => fail("iff elimination needs equivalence"),
        },
        "existsIntro" => {
            let body = get_formula(proof, "body")?;
            let witness = get_term(proof, "witness")?;
            let variable = get_str(proof, "variable")?;
            env.check_formula(&body)?;
            env.check_term(&witness)?;
            let expected = substitute_formula(&body, &variable, &witness);
            if !same_formula(&check_proof(env, dag, dag.proof(proof, "evidence")?, assumptions)?, &expected) {
                return fail("bad existential witness");
            }
            Ok(exists(&variable, body))
        }
        "existsElim" => {
            let existential = check_proof(env, dag, dag.proof(proof, "existential")?, assumptions)?;
            let (variable, body) = match &existential {
                Formula::Exists(variable, body) => (variable.clone(), (**body).clone()),
                _ => return fail("existential elimination needs existential"),
            };
            let witness = get_str(proof, "witness")?;
            let instance = substitute_formula(&body, &variable, &v(&witness));
            let result = check_proof(env, dag, dag.proof(proof, "body")?, &with_assumption(assumptions, instance))?;
            if free_formula(&result).contains(&witness)
                || assumptions.iter().any(|item| free_formula(item).contains(&witness))
                || free_formula(&existential).contains(&witness)
            {
                return fail("existential witness escapes");
            }
            Ok(result)
        }
        "falseElim" => {
            match check_proof(env, dag, dag.proof(proof, "absurdity")?, assumptions)? {
                Formula::Bottom => {}
                _ => return fail("false elimination needs bottom"),
            }
            let conclusion = get_formula(proof, "conclusion")?;
            env.check_formula(&conclusion)?;
            Ok(conclusion)
        }
        "dne" => {
            let proposition = get_formula(proof, "proposition")?;
            env.check_formula(&proposition)?;
            let expected = neg(neg(proposition.clone()));
            if !same_formula(&check_proof(env, dag, dag.proof(proof, "proof")?, assumptions)?, &expected) {
                return fail("bad DNE");
            }
            Ok(proposition)
        }
        other => fail(format!("unsupported proof DAG rule: {other}")),
    }
}

// Modules.

pub fn validate_module(value: &Value) -> Result<()> {
    let map = match value {
        Value::Object(map) if value.get("format") == Some(&Value::String("grace17.compiled-module".into())) && value.get("version") == Some(&Value::Number(3.into())) => map,
        _ => return fail("unsupported G17C module"),
    };
    let digest = match map.get("digest") {
        Some(Value::String(digest)) if is_digest(digest) => digest.clone(),
        _ => return fail("malformed G17C digest"),
    };
    let mut body = Map::new();
    for (key, item) in map {
        if key != "digest" {
            body.insert(key.clone(), item.clone());
        }
    }
    if sha256_hex(canonical(&Value::Object(body))?.as_bytes()) != digest {
        return fail("corrupted G17C module digest");
    }
    let module_ok = matches!(map.get("module"), Some(Value::String(name)) if !name.is_empty());
    let events_ok = matches!(map.get("events"), Some(Value::Array(_)));
    let source_ok = matches!(map.get("source"), Some(Value::String(source)) if source.is_empty() || is_digest(source));
    let base_ok = matches!(map.get("baseEnvironment"), Some(Value::String(text)) if is_digest(text));
    let result_ok = matches!(map.get("resultEnvironment"), Some(Value::String(text)) if is_digest(text));
    if !module_ok || !events_ok || !source_ok || !base_ok || !result_ok {
        return fail("malformed G17C envelope");
    }
    let dependencies = match map.get("dependencies") {
        Some(Value::Array(items)) => items,
        _ => return fail("malformed G17C dependencies"),
    };
    let mut names = BTreeSet::new();
    for item in dependencies {
        let module = item.get("module").and_then(Value::as_str);
        let digest = item.get("digest").and_then(Value::as_str);
        match (module, digest) {
            (Some(module), Some(digest)) if !module.is_empty() && is_digest(digest) && names.insert(module.to_string()) => {}
            _ => return fail("malformed G17C dependencies"),
        }
    }
    Ok(())
}

fn replay_admission(env: &mut Environment, event: &Value) -> Result<()> {
    let operation = event.get("operation").and_then(Value::as_str).unwrap_or("");
    let payload = match event.get("payload") {
        Some(payload @ Value::Object(_)) => payload,
        _ => return fail("malformed G17C admission"),
    };
    let options = || get(payload, "options");
    match operation {
        "declareFunction" => {
            let name = get_str(payload, "name")?;
            env.fresh_name(&name)?;
            let arity = get_usize(payload, "arity").map_err(|_| CheckError("bad function arity".into()))?;
            env.functions.insert(name, arity);
            Ok(())
        }
        "declarePredicate" => {
            let name = get_str(payload, "name")?;
            env.fresh_name(&name)?;
            let arity = get_usize(payload, "arity").map_err(|_| CheckError("bad predicate arity".into()))?;
            env.predicates.insert(name, arity);
            Ok(())
        }
        "defineFunction" => define_function(
            env,
            &FunctionDefinition { name: get_str(payload, "name")?, parameters: get_strings(payload, "parameters")?, body: get_term(payload, "body")? },
        ),
        "definePredicate" => define_predicate(
            env,
            &PredicateDefinition { name: get_str(payload, "name")?, parameters: get_strings(payload, "parameters")?, body: get_formula(payload, "body")? },
        ),
        "defineSubset" => define_subset(env, payload),
        "declareDatatype" => declare_datatype(env, get(payload, "spec")?),
        "registerNaturalDatatype" => register_natural_datatype(env),
        "defineStructuralFunction" => define_structural(env, options()?),
        "defineReplacement" => define_replacement(env, options()?),
        "defineWellFoundedFunction" => define_well_founded(env, options()?),
        "reifyUnaryOperation" => reify_unary_operation(env, options()?),
        "defineUniqueFunction" => define_unique(env, options()?),
        "defineMembershipRecursiveFunction" => define_membership_recursion(env, options()?),
        "defineWellFoundedSetFunction" => define_well_founded_set_function(env, options()?),
        "defineTransfiniteFunction" => define_transfinite(env, options()?),
        other => fail(format!("unsupported G17C admission operation: {other}")),
    }
}

/// Replay one validated module over the environment: dependency receipts,
/// the base digest, every event, and the result digest.
pub fn replay_module(env: &mut Environment, document: &Value, foundation_digest: &str) -> Result<()> {
    validate_module(document)?;
    let foundation = document.get("foundation");
    let profile_ok = foundation.and_then(|item| item.get("profile")).and_then(Value::as_str) == env.profile();
    let digest_ok = foundation.and_then(|item| item.get("environment")).and_then(Value::as_str) == Some(foundation_digest);
    if !profile_ok || !digest_ok {
        return fail("G17C foundation mismatch");
    }
    for dependency in document["dependencies"].as_array().expect("validated") {
        let module = dependency["module"].as_str().expect("validated");
        if env.receipts.get(module).map(String::as_str) != dependency["digest"].as_str() {
            return fail(format!("missing or stale G17C dependency {module}"));
        }
    }
    if env.digest != document["baseEnvironment"].as_str().expect("validated") {
        return fail("G17C exact dependency-prefix mismatch");
    }
    for item in document["events"].as_array().expect("validated") {
        match item.get("kind").and_then(Value::as_str) {
            Some("admission") => replay_admission(env, get(item, "event")?)?,
            Some("theoremBatch") => {
                let statements = match item.get("statements") {
                    Some(Value::Array(statements)) if !statements.is_empty() => statements,
                    _ => return fail("malformed theorem batch"),
                };
                let mut expected: BTreeMap<String, Formula> = BTreeMap::new();
                for statement in statements {
                    let name = match statement.get("name") {
                        Some(Value::String(name)) if !name.is_empty() => name.clone(),
                        _ => return fail("duplicate theorem boundary"),
                    };
                    if expected.contains_key(&name) || env.axioms.contains_key(&name) || env.theorems.contains_key(&name) {
                        return fail("duplicate theorem boundary");
                    }
                    let formula = get_formula(statement, "statement")?;
                    env.check_formula(&formula)?;
                    if !free_formula(&formula).is_empty() {
                        return fail("theorem statement is not closed");
                    }
                    expected.insert(name, formula);
                }
                let program = machine::program_from_json(get(item, "machine")?)?;
                // The authenticated event order and final digest bind the live
                // environment, so an embedded batch skips the whole-environment hash.
                machine::verify(&program, env, false, Some(&expected))?;
                let boundaries: BTreeSet<String> = program.theorems.iter().map(|(name, _)| program.symbols[*name as usize].clone()).collect();
                let expected_names: BTreeSet<String> = expected.keys().cloned().collect();
                if boundaries != expected_names {
                    return fail("theorem boundary set mismatch");
                }
                env.theorems.extend(expected);
            }
            _ => return fail("unknown G17C event"),
        }
    }
    env.refresh_digest()?;
    if env.digest != document["resultEnvironment"].as_str().expect("validated") {
        return fail("G17C result-environment mismatch");
    }
    let module = document["module"].as_str().expect("validated").to_string();
    let digest = document["digest"].as_str().expect("validated").to_string();
    env.receipts.insert(module, digest);
    Ok(())
}
