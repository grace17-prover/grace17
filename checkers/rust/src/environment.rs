// The logical environment: signatures, axioms, theorems, definitions,
// datatypes, recursive functions, and function bodies, with the canonical
// snapshot whose SHA-256 is the environment digest.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::ast::{Formula, Pattern, Term};
use crate::support::{canonical, fail, natural_int, sha256_hex, utf16_compare, Result};
use serde_json::{Map, Value};
use std::collections::BTreeMap;

#[derive(Debug, Clone)]
pub struct Definition {
    pub kind: String,
    pub parameters: Vec<String>,
    pub properties: Vec<(String, Formula)>,
}

#[derive(Debug, Clone)]
pub struct Body {
    pub parameters: Vec<String>,
    pub body: Term,
}

#[derive(Debug, Clone)]
pub struct Equation {
    pub patterns: Vec<Pattern>,
    pub body: Term,
}

/// An admitted recursive function. `raw` is the record exactly as the
/// snapshot carries it; the typed fields are parsed from it.
#[derive(Debug, Clone)]
pub struct Recursive {
    pub raw: Value,
    pub parameters: Vec<String>,
    pub datatype: String,
    pub decreasing_parameter: usize,
    pub equations: Vec<Equation>,
    pub admission: String,
}

#[derive(Debug, Clone)]
pub struct Constructor {
    pub name: String,
    pub arity: usize,
    pub recursive_fields: Vec<usize>,
    /// Pairs of (field index, parameter index).
    pub parameter_fields: Vec<(usize, usize)>,
}

#[derive(Debug, Clone)]
pub struct Datatype {
    pub raw: Value,
    pub predicate: String,
    pub parameters: Vec<String>,
    pub constructors: Vec<Constructor>,
}

#[derive(Debug, Clone)]
pub struct Environment {
    pub capabilities: Value,
    pub digest: String,
    pub functions: BTreeMap<String, usize>,
    pub predicates: BTreeMap<String, usize>,
    pub axioms: BTreeMap<String, Formula>,
    pub theorems: BTreeMap<String, Formula>,
    pub definitions: BTreeMap<String, Definition>,
    pub datatypes: BTreeMap<String, Datatype>,
    pub recursive: BTreeMap<String, Recursive>,
    pub bodies: BTreeMap<String, Body>,
    /// Module receipts of a compiled-module replay: module name to content digest.
    pub receipts: BTreeMap<String, String>,
}

fn string_list(value: &Value, what: &str) -> Result<Vec<String>> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::String(text) => Ok(text.clone()),
                _ => fail(format!("malformed {what}")),
            })
            .collect(),
        _ => fail(format!("malformed {what}")),
    }
}

fn index_list(value: &Value, what: &str) -> Result<Vec<usize>> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| natural_int(item).ok_or_else(|| crate::support::CheckError(format!("malformed {what}"))))
            .collect(),
        _ => fail(format!("malformed {what}")),
    }
}

pub fn parse_recursive(raw: &Value) -> Result<Recursive> {
    let parameters = string_list(raw.get("parameters").unwrap_or(&Value::Null), "recursive parameters")?;
    let datatype = match raw.get("datatype") {
        Some(Value::String(text)) => text.clone(),
        _ => return fail("malformed recursive datatype"),
    };
    let decreasing_parameter = natural_int(raw.get("decreasingParameter").unwrap_or(&Value::Null))
        .ok_or_else(|| crate::support::CheckError("malformed decreasing parameter".into()))?;
    let admission = match raw.get("admission") {
        Some(Value::String(text)) => text.clone(),
        _ => return fail("malformed recursive admission"),
    };
    let equations = match raw.get("equations") {
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| {
                let patterns = match item.get("patterns") {
                    Some(Value::Array(patterns)) => patterns.iter().map(Pattern::from_json).collect::<Result<Vec<_>>>()?,
                    _ => return fail("malformed recursive equation"),
                };
                let body = Term::from_json(item.get("body").unwrap_or(&Value::Null))?;
                Ok(Equation { patterns, body })
            })
            .collect::<Result<Vec<_>>>()?,
        _ => return fail("malformed recursive equations"),
    };
    Ok(Recursive { raw: raw.clone(), parameters, datatype, decreasing_parameter, equations, admission })
}

pub fn parse_datatype(raw: &Value) -> Result<Datatype> {
    let predicate = match raw.get("predicate") {
        Some(Value::String(text)) if !text.is_empty() => text.clone(),
        _ => return fail("malformed datatype predicate"),
    };
    let parameters = match raw.get("parameters") {
        Some(value) => string_list(value, "datatype parameters")?,
        None => Vec::new(),
    };
    let constructors = match raw.get("constructors") {
        Some(Value::Array(items)) if !items.is_empty() => items
            .iter()
            .map(|item| {
                let name = match item.get("name") {
                    Some(Value::String(text)) if !text.is_empty() => text.clone(),
                    _ => return fail("malformed constructor"),
                };
                let arity = natural_int(item.get("arity").unwrap_or(&Value::Null))
                    .ok_or_else(|| crate::support::CheckError("malformed constructor".into()))?;
                let recursive_fields = match item.get("recursiveFields") {
                    Some(value) => index_list(value, "recursive fields")?,
                    None => Vec::new(),
                };
                let parameter_fields = match item.get("parameterFields") {
                    Some(Value::Array(fields)) => fields
                        .iter()
                        .map(|entry| {
                            let field = natural_int(entry.get("field").unwrap_or(&Value::Null));
                            let parameter = natural_int(entry.get("parameter").unwrap_or(&Value::Null));
                            match (field, parameter) {
                                (Some(field), Some(parameter)) => Ok((field, parameter)),
                                _ => fail("bad parameter fields"),
                            }
                        })
                        .collect::<Result<Vec<_>>>()?,
                    None => Vec::new(),
                    _ => return fail("bad parameter fields"),
                };
                Ok(Constructor { name, arity, recursive_fields, parameter_fields })
            })
            .collect::<Result<Vec<_>>>()?,
        _ => return fail("malformed datatype"),
    };
    Ok(Datatype { raw: raw.clone(), predicate, parameters, constructors })
}

fn pairs<'a>(snapshot: &'a Value, key: &str) -> Result<Vec<(&'a str, &'a Value)>> {
    match snapshot.get(key) {
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| match item {
                Value::Array(pair) if pair.len() == 2 => match &pair[0] {
                    Value::String(name) => Ok((name.as_str(), &pair[1])),
                    _ => fail("malformed environment snapshot"),
                },
                _ => fail("malformed environment snapshot"),
            })
            .collect(),
        _ => fail("malformed environment snapshot"),
    }
}

impl Environment {
    /// An environment whose digest is computed from the given snapshot JSON,
    /// which must match the document's digest.
    pub fn from_document(document: &Value) -> Result<Environment> {
        if document.get("format") != Some(&Value::String("grace17.environment".into()))
            || document.get("version") != Some(&Value::Number(1.into()))
        {
            return fail("unsupported GRACE17 environment");
        }
        let snapshot = document.get("kernel").ok_or_else(|| crate::support::CheckError("unsupported GRACE17 environment".into()))?;
        let actual = sha256_hex(canonical(snapshot)?.as_bytes());
        if document.get("digest") != Some(&Value::String(actual.clone())) {
            return fail("environment digest mismatch");
        }
        let mut result = Environment {
            capabilities: snapshot.get("capabilities").cloned().unwrap_or(Value::Object(Map::new())),
            digest: actual,
            functions: BTreeMap::new(),
            predicates: BTreeMap::new(),
            axioms: BTreeMap::new(),
            theorems: BTreeMap::new(),
            definitions: BTreeMap::new(),
            datatypes: BTreeMap::new(),
            recursive: BTreeMap::new(),
            bodies: BTreeMap::new(),
            receipts: BTreeMap::new(),
        };
        for (name, arity) in pairs(snapshot, "functions")? {
            result.functions.insert(name.to_string(), natural_int(arity).ok_or_else(|| crate::support::CheckError("bad arity".into()))?);
        }
        for (name, arity) in pairs(snapshot, "predicates")? {
            result.predicates.insert(name.to_string(), natural_int(arity).ok_or_else(|| crate::support::CheckError("bad arity".into()))?);
        }
        for (name, formula) in pairs(snapshot, "axioms")? {
            result.axioms.insert(name.to_string(), Formula::from_json(formula)?);
        }
        for (name, formula) in pairs(snapshot, "theorems")? {
            result.theorems.insert(name.to_string(), Formula::from_json(formula)?);
        }
        for (name, record) in pairs(snapshot, "definitions")? {
            let kind = match record.get("kind") {
                Some(Value::String(text)) => text.clone(),
                _ => return fail("malformed definition record"),
            };
            let parameters = string_list(record.get("parameters").unwrap_or(&Value::Null), "definition parameters")?;
            let properties = pairs(record, "properties")?
                .into_iter()
                .map(|(property, formula)| Ok((property.to_string(), Formula::from_json(formula)?)))
                .collect::<Result<Vec<_>>>()?;
            result.definitions.insert(name.to_string(), Definition { kind, parameters, properties });
        }
        for (name, record) in pairs(snapshot, "datatypes")? {
            result.datatypes.insert(name.to_string(), parse_datatype(record)?);
        }
        for (name, record) in pairs(snapshot, "recursiveFunctions")? {
            result.recursive.insert(name.to_string(), parse_recursive(record)?);
        }
        for (name, record) in pairs(snapshot, "functionBodies")? {
            let parameters = string_list(record.get("parameters").unwrap_or(&Value::Null), "function body parameters")?;
            let body = Term::from_json(record.get("body").unwrap_or(&Value::Null))?;
            result.bodies.insert(name.to_string(), Body { parameters, body });
        }
        Ok(result)
    }

    pub fn from_file(path: &str) -> Result<Environment> {
        let text = crate::support::read_text(path)?;
        let document = crate::support::parse_json(&text)?;
        Environment::from_document(&document)
    }

    /// An empty environment of a foundation profile, before any axiom.
    pub fn empty_foundation(profile: &str) -> Result<Environment> {
        if !matches!(profile, "ZF" | "ZFC" | "ZFG") {
            return fail(format!("unsupported foundation profile: {profile}"));
        }
        // Exactly the capability object of the reference checkers; the
        // digest of the foundation depends on these keys and no others.
        let mut capabilities = Map::new();
        capabilities.insert("separation".into(), Value::Bool(true));
        capabilities.insert("replacement".into(), Value::Bool(true));
        capabilities.insert("inductiveDefinitions".into(), Value::Bool(true));
        capabilities.insert("setTheory".into(), Value::String(profile.into()));
        Ok(Environment {
            capabilities: Value::Object(capabilities),
            digest: String::new(),
            functions: BTreeMap::new(),
            predicates: BTreeMap::new(),
            axioms: BTreeMap::new(),
            theorems: BTreeMap::new(),
            definitions: BTreeMap::new(),
            datatypes: BTreeMap::new(),
            recursive: BTreeMap::new(),
            bodies: BTreeMap::new(),
            receipts: BTreeMap::new(),
        })
    }

    pub fn capability(&self, name: &str) -> bool {
        self.capabilities.get(name) == Some(&Value::Bool(true))
    }

    pub fn profile(&self) -> Option<&str> {
        self.capabilities.get("setTheory").and_then(Value::as_str)
    }

    fn sorted<'a, T>(map: &'a BTreeMap<String, T>) -> Vec<(&'a String, &'a T)> {
        let mut items: Vec<(&String, &T)> = map.iter().collect();
        items.sort_by(|left, right| utf16_compare(left.0, right.0));
        items
    }

    /// The canonical snapshot whose SHA-256 is the digest.
    pub fn snapshot(&self) -> Value {
        let arity_pairs = |map: &BTreeMap<String, usize>| {
            Value::Array(
                Self::sorted(map)
                    .into_iter()
                    .map(|(name, arity)| Value::Array(vec![Value::String(name.clone()), Value::Number((*arity as u64).into())]))
                    .collect(),
            )
        };
        let formula_pairs = |map: &BTreeMap<String, Formula>| {
            Value::Array(
                Self::sorted(map)
                    .into_iter()
                    .map(|(name, formula)| Value::Array(vec![Value::String(name.clone()), formula.to_json()]))
                    .collect(),
            )
        };
        let definitions = Value::Array(
            Self::sorted(&self.definitions)
                .into_iter()
                .map(|(name, item)| {
                    let mut properties: Vec<&(String, Formula)> = item.properties.iter().collect();
                    properties.sort_by(|left, right| utf16_compare(&left.0, &right.0));
                    let mut record = Map::new();
                    record.insert("kind".into(), Value::String(item.kind.clone()));
                    record.insert("parameters".into(), Value::Array(item.parameters.iter().map(|p| Value::String(p.clone())).collect()));
                    record.insert(
                        "properties".into(),
                        Value::Array(
                            properties
                                .into_iter()
                                .map(|(property, formula)| Value::Array(vec![Value::String(property.clone()), formula.to_json()]))
                                .collect(),
                        ),
                    );
                    Value::Array(vec![Value::String(name.clone()), Value::Object(record)])
                })
                .collect(),
        );
        let datatypes = Value::Array(
            Self::sorted(&self.datatypes)
                .into_iter()
                .map(|(name, item)| Value::Array(vec![Value::String(name.clone()), item.raw.clone()]))
                .collect(),
        );
        let recursive = Value::Array(
            Self::sorted(&self.recursive)
                .into_iter()
                .map(|(name, item)| Value::Array(vec![Value::String(name.clone()), item.raw.clone()]))
                .collect(),
        );
        let bodies = Value::Array(
            Self::sorted(&self.bodies)
                .into_iter()
                .map(|(name, item)| {
                    let mut record = Map::new();
                    record.insert("parameters".into(), Value::Array(item.parameters.iter().map(|p| Value::String(p.clone())).collect()));
                    record.insert("body".into(), item.body.to_json());
                    Value::Array(vec![Value::String(name.clone()), Value::Object(record)])
                })
                .collect(),
        );
        let mut snapshot = Map::new();
        snapshot.insert("capabilities".into(), self.capabilities.clone());
        snapshot.insert("functions".into(), arity_pairs(&self.functions));
        snapshot.insert("predicates".into(), arity_pairs(&self.predicates));
        snapshot.insert("axioms".into(), formula_pairs(&self.axioms));
        snapshot.insert("theorems".into(), formula_pairs(&self.theorems));
        snapshot.insert("definitions".into(), definitions);
        snapshot.insert("datatypes".into(), datatypes);
        snapshot.insert("recursiveFunctions".into(), recursive);
        snapshot.insert("functionBodies".into(), bodies);
        Value::Object(snapshot)
    }

    pub fn refresh_digest(&mut self) -> Result<String> {
        self.digest = sha256_hex(canonical(&self.snapshot())?.as_bytes());
        Ok(self.digest.clone())
    }

    pub fn property(&self, name: &str, property: &str) -> Option<&Formula> {
        self.definitions
            .get(name)
            .and_then(|definition| definition.properties.iter().find(|(key, _)| key == property).map(|(_, formula)| formula))
    }

    pub fn is_constructor(&self, name: &str) -> bool {
        self.datatypes.values().any(|datatype| datatype.constructors.iter().any(|ctor| ctor.name == name))
    }

    pub fn constructor(&self, name: &str) -> Option<&Constructor> {
        self.datatypes.values().flat_map(|datatype| datatype.constructors.iter()).find(|ctor| ctor.name == name)
    }

    /// A logical symbol is fresh when no function, predicate, or definition
    /// already uses it, as in the reference checkers.
    pub fn fresh_name(&self, name: &str) -> Result<()> {
        if name.is_empty() || self.functions.contains_key(name) || self.predicates.contains_key(name) || self.definitions.contains_key(name) {
            return fail(format!("duplicate logical symbol: {name}"));
        }
        Ok(())
    }

    pub fn check_parameters(&self, parameters: &[String]) -> Result<()> {
        let mut seen = std::collections::BTreeSet::new();
        for parameter in parameters {
            if parameter.is_empty() || !seen.insert(parameter.clone()) {
                return fail("duplicate or empty parameter");
            }
        }
        Ok(())
    }

    /// Every application is a declared function at its arity.
    pub fn check_term(&self, term: &Term) -> Result<()> {
        match term {
            Term::Var(name) => {
                if name.is_empty() {
                    return fail("empty variable");
                }
                Ok(())
            }
            Term::Nat(_) => Ok(()),
            Term::App(fn_name, args) => {
                if self.functions.get(fn_name) != Some(&args.len()) {
                    return fail(format!("unknown or misapplied function {fn_name}"));
                }
                for arg in args {
                    self.check_term(arg)?;
                }
                Ok(())
            }
        }
    }

    pub fn check_formula(&self, formula: &Formula) -> Result<()> {
        match formula {
            Formula::Bottom => Ok(()),
            Formula::Eq(left, right) => {
                self.check_term(left)?;
                self.check_term(right)
            }
            Formula::Pred(name, args) => {
                if self.predicates.get(name) != Some(&args.len()) {
                    return fail(format!("unknown or misapplied predicate {name}"));
                }
                for arg in args {
                    self.check_term(arg)?;
                }
                Ok(())
            }
            Formula::Imp(left, right) | Formula::And(left, right) | Formula::Or(left, right) | Formula::Iff(left, right) => {
                self.check_formula(left)?;
                self.check_formula(right)
            }
            Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
                if variable.is_empty() {
                    return fail("empty bound variable");
                }
                self.check_formula(body)
            }
        }
    }

    pub fn record_definition(&mut self, name: &str, kind: &str, parameters: &[String], properties: Vec<(String, Formula)>) -> Result<()> {
        for (_, formula) in &properties {
            self.check_formula(formula)?;
            if !crate::ast::free_formula(formula).is_empty() {
                return fail(format!("definition property of {name} is not closed"));
            }
        }
        self.definitions.insert(name.to_string(), Definition { kind: kind.to_string(), parameters: parameters.to_vec(), properties });
        Ok(())
    }

    pub fn add_axiom(&mut self, name: &str, formula: Formula) -> Result<()> {
        if name.is_empty() || self.axioms.contains_key(name) || self.theorems.contains_key(name) {
            return fail(format!("duplicate proposition name: {name}"));
        }
        self.check_formula(&formula)?;
        if !crate::ast::free_formula(&formula).is_empty() {
            return fail(format!("axiom {name} is not closed"));
        }
        self.axioms.insert(name.to_string(), formula);
        Ok(())
    }
}
