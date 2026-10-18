// Named abstract syntax of terms and formulas, with the JSON spelling of
// the portable environment and the binding operations the checkers need.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::support::{fail, is_natural_literal, Result};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use serde_json::{json, Map, Value};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Term {
    Var(String),
    App(String, Vec<Term>),
    Nat(BigUint),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Formula {
    Bottom,
    Eq(Box<Term>, Box<Term>),
    Pred(String, Vec<Term>),
    Imp(Box<Formula>, Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Iff(Box<Formula>, Box<Formula>),
    Forall(String, Box<Formula>),
    Exists(String, Box<Formula>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Bind(String),
    Ctor(String, Vec<Pattern>),
}

// Constructors in the spelling of the Python reference checker.

pub fn v(name: &str) -> Term {
    Term::Var(name.to_string())
}

pub fn app(fn_name: &str, args: Vec<Term>) -> Term {
    Term::App(fn_name.to_string(), args)
}

pub fn nat(value: u64) -> Term {
    Term::Nat(BigUint::from(value))
}

pub fn eq(left: Term, right: Term) -> Formula {
    Formula::Eq(Box::new(left), Box::new(right))
}

pub fn pred(name: &str, args: Vec<Term>) -> Formula {
    Formula::Pred(name.to_string(), args)
}

pub fn imp(left: Formula, right: Formula) -> Formula {
    Formula::Imp(Box::new(left), Box::new(right))
}

pub fn and(left: Formula, right: Formula) -> Formula {
    Formula::And(Box::new(left), Box::new(right))
}

pub fn or(left: Formula, right: Formula) -> Formula {
    Formula::Or(Box::new(left), Box::new(right))
}

pub fn iff(left: Formula, right: Formula) -> Formula {
    Formula::Iff(Box::new(left), Box::new(right))
}

pub fn neg(value: Formula) -> Formula {
    imp(value, Formula::Bottom)
}

pub fn forall(variable: &str, body: Formula) -> Formula {
    Formula::Forall(variable.to_string(), Box::new(body))
}

pub fn exists(variable: &str, body: Formula) -> Formula {
    Formula::Exists(variable.to_string(), Box::new(body))
}

pub fn foralls(variables: &[String], body: Formula) -> Formula {
    let mut result = body;
    for variable in variables.iter().rev() {
        result = forall(variable, result);
    }
    result
}

pub fn binary(tag: &str, left: Formula, right: Formula) -> Formula {
    match tag {
        "imp" => imp(left, right),
        "and" => and(left, right),
        "or" => or(left, right),
        _ => iff(left, right),
    }
}

pub fn quantify(tag: &str, variable: &str, body: Formula) -> Formula {
    if tag == "forall" {
        forall(variable, body)
    } else {
        exists(variable, body)
    }
}

fn field<'a>(value: &'a Value, key: &str) -> Result<&'a Value> {
    match value.get(key) {
        Some(item) => Ok(item),
        None => fail(format!("malformed AST: missing {key}")),
    }
}

fn string_field(value: &Value, key: &str) -> Result<String> {
    match field(value, key)? {
        Value::String(text) => Ok(text.clone()),
        _ => fail(format!("malformed AST: {key} is not a string")),
    }
}

impl Term {
    pub fn from_json(value: &Value) -> Result<Term> {
        let tag = string_field(value, "tag")?;
        match tag.as_str() {
            "var" => Ok(Term::Var(string_field(value, "name")?)),
            "nat" => {
                let text = string_field(value, "value")?;
                if !is_natural_literal(&text) {
                    return fail("malformed natural literal");
                }
                Ok(Term::Nat(BigUint::parse_bytes(text.as_bytes(), 10).expect("decimal")))
            }
            "app" => {
                let fn_name = string_field(value, "fn")?;
                let args = match field(value, "args")? {
                    Value::Array(items) => items.iter().map(Term::from_json).collect::<Result<Vec<_>>>()?,
                    _ => return fail("malformed AST: args is not an array"),
                };
                Ok(Term::App(fn_name, args))
            }
            _ => fail("malformed term"),
        }
    }

    pub fn to_json(&self) -> Value {
        match self {
            Term::Var(name) => json!({"tag": "var", "name": name}),
            Term::Nat(value) => json!({"tag": "nat", "value": value.to_string()}),
            Term::App(fn_name, args) => {
                let mut map = Map::new();
                map.insert("tag".into(), Value::String("app".into()));
                map.insert("fn".into(), Value::String(fn_name.clone()));
                map.insert("args".into(), Value::Array(args.iter().map(Term::to_json).collect()));
                Value::Object(map)
            }
        }
    }
}

impl Formula {
    pub fn from_json(value: &Value) -> Result<Formula> {
        let tag = string_field(value, "tag")?;
        match tag.as_str() {
            "bottom" => Ok(Formula::Bottom),
            "eq" => Ok(eq(Term::from_json(field(value, "left")?)?, Term::from_json(field(value, "right")?)?)),
            "pred" => {
                let name = string_field(value, "pred")?;
                let args = match field(value, "args")? {
                    Value::Array(items) => items.iter().map(Term::from_json).collect::<Result<Vec<_>>>()?,
                    _ => return fail("malformed AST: args is not an array"),
                };
                Ok(Formula::Pred(name, args))
            }
            "imp" | "and" | "or" | "iff" => Ok(binary(
                &tag,
                Formula::from_json(field(value, "left")?)?,
                Formula::from_json(field(value, "right")?)?,
            )),
            "forall" | "exists" => Ok(quantify(
                &tag,
                &string_field(value, "variable")?,
                Formula::from_json(field(value, "body")?)?,
            )),
            _ => fail("malformed formula"),
        }
    }

    pub fn to_json(&self) -> Value {
        let binary_json = |tag: &str, left: &Formula, right: &Formula| {
            let mut map = Map::new();
            map.insert("tag".into(), Value::String(tag.into()));
            map.insert("left".into(), left.to_json());
            map.insert("right".into(), right.to_json());
            Value::Object(map)
        };
        let quantifier_json = |tag: &str, variable: &str, body: &Formula| {
            let mut map = Map::new();
            map.insert("tag".into(), Value::String(tag.into()));
            map.insert("variable".into(), Value::String(variable.into()));
            map.insert("body".into(), body.to_json());
            Value::Object(map)
        };
        match self {
            Formula::Bottom => json!({"tag": "bottom"}),
            Formula::Eq(left, right) => {
                let mut map = Map::new();
                map.insert("tag".into(), Value::String("eq".into()));
                map.insert("left".into(), left.to_json());
                map.insert("right".into(), right.to_json());
                Value::Object(map)
            }
            Formula::Pred(name, args) => {
                let mut map = Map::new();
                map.insert("tag".into(), Value::String("pred".into()));
                map.insert("pred".into(), Value::String(name.clone()));
                map.insert("args".into(), Value::Array(args.iter().map(Term::to_json).collect()));
                Value::Object(map)
            }
            Formula::Imp(left, right) => binary_json("imp", left, right),
            Formula::And(left, right) => binary_json("and", left, right),
            Formula::Or(left, right) => binary_json("or", left, right),
            Formula::Iff(left, right) => binary_json("iff", left, right),
            Formula::Forall(variable, body) => quantifier_json("forall", variable, body),
            Formula::Exists(variable, body) => quantifier_json("exists", variable, body),
        }
    }

    pub fn tag(&self) -> &'static str {
        match self {
            Formula::Bottom => "bottom",
            Formula::Eq(..) => "eq",
            Formula::Pred(..) => "pred",
            Formula::Imp(..) => "imp",
            Formula::And(..) => "and",
            Formula::Or(..) => "or",
            Formula::Iff(..) => "iff",
            Formula::Forall(..) => "forall",
            Formula::Exists(..) => "exists",
        }
    }
}

impl Pattern {
    pub fn from_json(value: &Value) -> Result<Pattern> {
        let tag = string_field(value, "tag")?;
        match tag.as_str() {
            "bind" => {
                let name = string_field(value, "name")?;
                if name.is_empty() {
                    return fail("empty pattern variable");
                }
                Ok(Pattern::Bind(name))
            }
            "ctor" => {
                let name = string_field(value, "name")?;
                let args = match value.get("args") {
                    Some(Value::Array(items)) => items.iter().map(Pattern::from_json).collect::<Result<Vec<_>>>()?,
                    None => Vec::new(),
                    _ => return fail("malformed pattern"),
                };
                Ok(Pattern::Ctor(name, args))
            }
            _ => fail("malformed pattern"),
        }
    }

    pub fn to_json(&self) -> Value {
        match self {
            Pattern::Bind(name) => json!({"tag": "bind", "name": name}),
            Pattern::Ctor(name, args) => {
                let mut map = Map::new();
                map.insert("tag".into(), Value::String("ctor".into()));
                map.insert("name".into(), Value::String(name.clone()));
                map.insert("args".into(), Value::Array(args.iter().map(Pattern::to_json).collect()));
                Value::Object(map)
            }
        }
    }
}

/// The natural a term denotes, folding `zero()` and `succ` chains.
pub fn natural_value(term: &Term) -> Option<BigUint> {
    let mut count = BigUint::zero();
    let mut cursor = term;
    loop {
        match cursor {
            Term::Nat(value) => return Some(value + count),
            Term::App(name, args) if name == "succ" && args.len() == 1 => {
                count += BigUint::one();
                cursor = &args[0];
            }
            Term::App(name, args) if name == "zero" && args.is_empty() => return Some(count),
            _ => return None,
        }
    }
}

/// Structural keys that identify terms and formulas up to natural folding
/// and renaming of bound variables.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TermKey {
    Nat(BigUint),
    Bound(usize),
    Free(String),
    App(String, Vec<TermKey>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FormulaKey {
    Bottom,
    Eq(Box<TermKey>, Box<TermKey>),
    Pred(String, Vec<TermKey>),
    Binary(&'static str, Box<FormulaKey>, Box<FormulaKey>),
    Quantifier(&'static str, Box<FormulaKey>),
}

pub fn term_key(term: &Term, binders: &[String]) -> TermKey {
    if let Some(value) = natural_value(term) {
        return TermKey::Nat(value);
    }
    match term {
        Term::Var(name) => {
            for (index, binder) in binders.iter().rev().enumerate() {
                if binder == name {
                    return TermKey::Bound(index);
                }
            }
            TermKey::Free(name.clone())
        }
        Term::App(fn_name, args) => TermKey::App(fn_name.clone(), args.iter().map(|arg| term_key(arg, binders)).collect()),
        Term::Nat(value) => TermKey::Nat(value.clone()),
    }
}

pub fn formula_key(formula: &Formula, binders: &mut Vec<String>) -> FormulaKey {
    match formula {
        Formula::Bottom => FormulaKey::Bottom,
        Formula::Eq(left, right) => FormulaKey::Eq(Box::new(term_key(left, binders)), Box::new(term_key(right, binders))),
        Formula::Pred(name, args) => FormulaKey::Pred(name.clone(), args.iter().map(|arg| term_key(arg, binders)).collect()),
        Formula::Imp(left, right) => FormulaKey::Binary("imp", Box::new(formula_key(left, binders)), Box::new(formula_key(right, binders))),
        Formula::And(left, right) => FormulaKey::Binary("and", Box::new(formula_key(left, binders)), Box::new(formula_key(right, binders))),
        Formula::Or(left, right) => FormulaKey::Binary("or", Box::new(formula_key(left, binders)), Box::new(formula_key(right, binders))),
        Formula::Iff(left, right) => FormulaKey::Binary("iff", Box::new(formula_key(left, binders)), Box::new(formula_key(right, binders))),
        Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
            binders.push(variable.clone());
            let inner = formula_key(body, binders);
            binders.pop();
            FormulaKey::Quantifier(if matches!(formula, Formula::Forall(..)) { "forall" } else { "exists" }, Box::new(inner))
        }
    }
}

pub fn same_formula(left: &Formula, right: &Formula) -> bool {
    formula_key(left, &mut Vec::new()) == formula_key(right, &mut Vec::new())
}

pub fn same_term(left: &Term, right: &Term) -> bool {
    term_key(left, &[]) == term_key(right, &[])
}

pub fn free_term_into(term: &Term, result: &mut BTreeSet<String>) {
    match term {
        Term::Var(name) => {
            result.insert(name.clone());
        }
        Term::App(_, args) => {
            for arg in args {
                free_term_into(arg, result);
            }
        }
        Term::Nat(_) => {}
    }
}

pub fn free_term(term: &Term) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    free_term_into(term, &mut result);
    result
}

fn free_formula_into(formula: &Formula, bound: &mut Vec<String>, result: &mut BTreeSet<String>) {
    let visit_term = |term: &Term, bound: &Vec<String>, result: &mut BTreeSet<String>| {
        for name in free_term(term) {
            if !bound.contains(&name) {
                result.insert(name);
            }
        }
    };
    match formula {
        Formula::Bottom => {}
        Formula::Eq(left, right) => {
            visit_term(left, bound, result);
            visit_term(right, bound, result);
        }
        Formula::Pred(_, args) => {
            for arg in args {
                visit_term(arg, bound, result);
            }
        }
        Formula::Imp(left, right) | Formula::And(left, right) | Formula::Or(left, right) | Formula::Iff(left, right) => {
            free_formula_into(left, bound, result);
            free_formula_into(right, bound, result);
        }
        Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
            bound.push(variable.clone());
            free_formula_into(body, bound, result);
            bound.pop();
        }
    }
}

pub fn free_formula(formula: &Formula) -> BTreeSet<String> {
    let mut result = BTreeSet::new();
    free_formula_into(formula, &mut Vec::new(), &mut result);
    result
}

pub fn substitute_term(term: &Term, variable: &str, replacement: &Term) -> Term {
    match term {
        Term::Var(name) if name == variable => replacement.clone(),
        Term::App(fn_name, args) => Term::App(fn_name.clone(), args.iter().map(|arg| substitute_term(arg, variable, replacement)).collect()),
        other => other.clone(),
    }
}

pub fn fresh(base: &str, forbidden: &BTreeSet<String>) -> String {
    if !forbidden.contains(base) {
        return base.to_string();
    }
    let mut index = 1;
    loop {
        let candidate = format!("{base}_{index}");
        if !forbidden.contains(&candidate) {
            return candidate;
        }
        index += 1;
    }
}

/// Capture-avoiding substitution of a free variable, renaming a binder that
/// would capture the replacement exactly as the reference checker does.
pub fn substitute_formula(formula: &Formula, variable: &str, replacement: &Term) -> Formula {
    match formula {
        Formula::Bottom => Formula::Bottom,
        Formula::Eq(left, right) => eq(substitute_term(left, variable, replacement), substitute_term(right, variable, replacement)),
        Formula::Pred(name, args) => Formula::Pred(name.clone(), args.iter().map(|arg| substitute_term(arg, variable, replacement)).collect()),
        Formula::Imp(left, right) => imp(substitute_formula(left, variable, replacement), substitute_formula(right, variable, replacement)),
        Formula::And(left, right) => and(substitute_formula(left, variable, replacement), substitute_formula(right, variable, replacement)),
        Formula::Or(left, right) => or(substitute_formula(left, variable, replacement), substitute_formula(right, variable, replacement)),
        Formula::Iff(left, right) => iff(substitute_formula(left, variable, replacement), substitute_formula(right, variable, replacement)),
        Formula::Forall(binder, body) | Formula::Exists(binder, body) => {
            let tag = formula.tag();
            if binder == variable {
                return formula.clone();
            }
            let replacement_free = free_term(replacement);
            if replacement_free.contains(binder) && free_formula(body).contains(variable) {
                let mut forbidden = free_formula(body);
                forbidden.extend(replacement_free.iter().cloned());
                forbidden.insert(variable.to_string());
                let renamed = fresh(binder, &forbidden);
                let renamed_body = substitute_formula(body, binder, &v(&renamed));
                return quantify(tag, &renamed, substitute_formula(&renamed_body, variable, replacement));
            }
            quantify(tag, binder, substitute_formula(body, variable, replacement))
        }
    }
}

/// Sequential substitution, one variable after another, as in the reference checker.
pub fn substitute_many(term: &Term, substitutions: &[(String, Term)]) -> Term {
    let mut result = term.clone();
    for (variable, replacement) in substitutions {
        result = substitute_term(&result, variable, replacement);
    }
    result
}

/// Simultaneous substitution, as the kernel's substituteMany.
pub fn substitute_simultaneous(term: &Term, substitutions: &BTreeMap<String, Term>) -> Term {
    match term {
        Term::Var(name) => substitutions.get(name).cloned().unwrap_or_else(|| term.clone()),
        Term::App(fn_name, args) => Term::App(fn_name.clone(), args.iter().map(|arg| substitute_simultaneous(arg, substitutions)).collect()),
        Term::Nat(_) => term.clone(),
    }
}

pub fn functions_in_term(term: &Term, result: &mut BTreeSet<String>) {
    if let Term::App(fn_name, args) = term {
        result.insert(fn_name.clone());
        for arg in args {
            functions_in_term(arg, result);
        }
    }
}

pub fn symbols_in_formula(formula: &Formula, result: &mut BTreeSet<String>) {
    match formula {
        Formula::Bottom => {}
        Formula::Eq(left, right) => {
            functions_in_term(left, result);
            functions_in_term(right, result);
        }
        Formula::Pred(name, args) => {
            result.insert(name.clone());
            for arg in args {
                functions_in_term(arg, result);
            }
        }
        Formula::Imp(left, right) | Formula::And(left, right) | Formula::Or(left, right) | Formula::Iff(left, right) => {
            symbols_in_formula(left, result);
            symbols_in_formula(right, result);
        }
        Formula::Forall(_, body) | Formula::Exists(_, body) => symbols_in_formula(body, result),
    }
}

pub fn pattern_bindings(patterns: &[Pattern], result: &mut Vec<String>) {
    for pattern in patterns {
        match pattern {
            Pattern::Bind(name) => result.push(name.clone()),
            Pattern::Ctor(_, args) => pattern_bindings(args, result),
        }
    }
}

pub fn pattern_term(pattern: &Pattern) -> Term {
    match pattern {
        Pattern::Bind(name) => v(name),
        Pattern::Ctor(name, args) => Term::App(name.clone(), args.iter().map(pattern_term).collect()),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn json_round_trip_is_exact() {
        let text = r#"{"tag":"forall","variable":"x","body":{"tag":"iff","left":{"tag":"pred","pred":"Nat","args":[{"tag":"var","name":"x"}]},"right":{"tag":"eq","left":{"tag":"app","fn":"succ","args":[{"tag":"nat","value":"3"}]},"right":{"tag":"app","fn":"zero","args":[]}}}}"#;
        let value: Value = serde_json::from_str(text).unwrap();
        let formula = Formula::from_json(&value).unwrap();
        assert_eq!(crate::support::canonical(&formula.to_json()).unwrap(), crate::support::canonical(&value).unwrap());
    }

    #[test]
    fn natural_folding_in_keys() {
        let left = app("succ", vec![app("succ", vec![app("zero", vec![])])]);
        let right = nat(2);
        assert!(same_term(&left, &right));
        assert!(!same_term(&left, &nat(3)));
    }

    #[test]
    fn substitution_avoids_capture() {
        let body = forall("y", pred("P", vec![v("x"), v("y")]));
        let result = substitute_formula(&body, "x", &v("y"));
        assert_eq!(result, forall("y_1", pred("P", vec![v("y"), v("y_1")])));
    }
}
