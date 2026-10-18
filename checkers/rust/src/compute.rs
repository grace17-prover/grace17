// Ground computation: the checked equation interpreter with the admitted
// big-integer shortcuts, and rational class equality.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::ast::{app, eq, forall, imp, nat, natural_value, pred, v, Formula, Pattern, Term};
use crate::environment::{Environment, Equation, Recursive};
use crate::support::{fail, Result};
use num_bigint::BigUint;
use num_traits::{One, Zero};
use std::collections::{BTreeSet, HashMap};
use std::sync::atomic::{AtomicI64, Ordering};

/// Steps of ground evaluation one computation may spend; `--fuel` sets it.
static FUEL: AtomicI64 = AtomicI64::new(1_000_000);

pub fn set_fuel(steps: i64) {
    FUEL.store(steps, Ordering::Relaxed);
}

pub fn fuel() -> i64 {
    FUEL.load(Ordering::Relaxed)
}

/// A normalized value: an arbitrary-precision natural or an application.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Val {
    Nat(BigUint),
    App(String, Vec<Val>),
}

pub const NAT_MOD: &str = "Grace.Cumulus.Nat.Mod.";
pub const NAT_REC: &str = "Grace.Core.Nat.Rec.";
pub const BOOL_OPS: &str = "Grace.Core.Data.BoolOps.";
pub const BOOL: &str = "Grace.Core.Data.Bool.";
pub const RAT_OPS: &str = "Grace.Cumulus.Rat.Computable.RationalCellOps.";
pub const NAT_SUB: &str = "Grace.Cumulus.Nat.Subtraction.";
pub const NAT_DIV: &str = "Grace.Cumulus.Nat.Division.";

fn bind(name: &str) -> Pattern {
    Pattern::Bind(name.to_string())
}

fn ctor(name: &str, args: Vec<Pattern>) -> Pattern {
    Pattern::Ctor(name.to_string(), args)
}

fn equations_equal(actual: &[Equation], expected: &[(Vec<Pattern>, Term)]) -> bool {
    actual.len() == expected.len()
        && actual.iter().zip(expected).all(|(item, (patterns, body))| item.patterns == *patterns && item.body == *body)
}

/// Exact recognition of a structural recursion by its admitted equations.
fn exact(env: &Environment, name: &str, parameters: &[&str], expected: &[(Vec<Pattern>, Term)]) -> bool {
    exact_at(env, name, parameters, 0, expected)
}

/// Exact recognition of a structural recursion descending on the given parameter.
fn exact_at(env: &Environment, name: &str, parameters: &[&str], decreasing: usize, expected: &[(Vec<Pattern>, Term)]) -> bool {
    match env.recursive.get(name) {
        Some(record) => {
            record.admission == "structural"
                && record.decreasing_parameter == decreasing
                && record.parameters.iter().map(String::as_str).eq(parameters.iter().copied())
                && equations_equal(&record.equations, expected)
        }
        None => false,
    }
}

/// Exact recognition of an explicit (non-recursive) definition by its admitted body.
fn exact_body(env: &Environment, name: &str, parameters: &[&str], expected: &Term) -> bool {
    match env.bodies.get(name) {
        Some(record) => record.parameters.iter().map(String::as_str).eq(parameters.iter().copied()) && record.body == *expected,
        None => false,
    }
}

/// The natural decision procedures (equality, order, truncated subtraction)
/// recognized exactly from their admitted equations and helper equations.
pub fn decision_equations(env: &Environment, name: &str, allowed: &BTreeSet<String>) -> Option<(String, Vec<String>)> {
    let decision = if name == format!("{NAT_MOD}equalNat") {
        "equal"
    } else if name == format!("{RAT_OPS}less") {
        "less"
    } else if name == format!("{RAT_OPS}minus") {
        "minus"
    } else {
        return None;
    };
    let shared = vec![format!("{NAT_MOD}isZero"), format!("{NAT_REC}predecessor")];
    let dependencies: Vec<String> = if decision == "minus" {
        [shared, vec![format!("{NAT_MOD}chooseNat"), format!("{RAT_OPS}minus")]].concat()
    } else {
        [shared, vec![format!("{BOOL_OPS}not"), format!("{BOOL_OPS}and"), name.to_string()]].concat()
    };
    if !dependencies.iter().all(|item| allowed.contains(item)) {
        return None;
    }
    let zero = ctor("zero", vec![]);
    let succ = |n: &str| ctor("succ", vec![bind(n)]);
    let is_zero = |n: &str| app(&format!("{NAT_MOD}isZero"), vec![v(n)]);
    let predecessor = |n: &str| app(&format!("{NAT_REC}predecessor"), vec![v(n)]);
    let nonzero = |n: &str| app(&format!("{BOOL_OPS}not"), vec![is_zero(n)]);
    let true_ = || app(&format!("{BOOL}true"), vec![]);
    let false_ = || app(&format!("{BOOL}false"), vec![]);

    let helpers = exact(env, &format!("{NAT_MOD}isZero"), &["n"], &[(vec![zero.clone()], true_()), (vec![succ("n")], false_())])
        && exact(
            env,
            &format!("{NAT_REC}predecessor"),
            &["n"],
            &[(vec![zero.clone()], app("zero", vec![])), (vec![succ("n")], v("n"))],
        );
    let logical = if decision == "minus" {
        exact(
            env,
            &format!("{NAT_MOD}chooseNat"),
            &["condition", "yes", "no"],
            &[
                (vec![ctor(&format!("{BOOL}false"), vec![]), bind("yes"), bind("no")], v("no")),
                (vec![ctor(&format!("{BOOL}true"), vec![]), bind("yes"), bind("no")], v("yes")),
            ],
        )
    } else {
        exact(
            env,
            &format!("{BOOL_OPS}not"),
            &["b"],
            &[(vec![ctor(&format!("{BOOL}false"), vec![])], true_()), (vec![ctor(&format!("{BOOL}true"), vec![])], false_())],
        ) && exact(
            env,
            &format!("{BOOL_OPS}and"),
            &["a", "b"],
            &[
                (vec![ctor(&format!("{BOOL}false"), vec![]), bind("b")], false_()),
                (vec![ctor(&format!("{BOOL}true"), vec![]), bind("b")], v("b")),
            ],
        )
    };
    let (first, other) = if decision == "equal" { ("m", "n") } else { ("a", "b") };
    let base = if decision == "minus" {
        nat(0)
    } else if decision == "equal" {
        is_zero(other)
    } else {
        nonzero(other)
    };
    let recurse = app(name, vec![v(first), predecessor(other)]);
    let step = if decision == "minus" {
        app(&format!("{NAT_MOD}chooseNat"), vec![is_zero(other), app("succ", vec![v(first)]), recurse])
    } else {
        app(&format!("{BOOL_OPS}and"), vec![nonzero(other), recurse])
    };
    if helpers
        && logical
        && exact(env, name, &[first, other], &[(vec![zero, bind(other)], base), (vec![succ(first), bind(other)], step)])
    {
        Some((decision.to_string(), dependencies))
    } else {
        None
    }
}

/// The remainder's fixed dependency list: its own equations, the helper
/// equations, and the equality decision with the helpers that one names.
fn mod_definitions() -> Vec<String> {
    vec![
        format!("{NAT_MOD}mod"),
        format!("{NAT_MOD}nextRemainder"),
        format!("{NAT_MOD}chooseNat"),
        format!("{NAT_MOD}equalNat"),
        format!("{NAT_MOD}isZero"),
        format!("{NAT_REC}predecessor"),
        format!("{BOOL_OPS}not"),
        format!("{BOOL_OPS}and"),
    ]
}

/// The descent-by-ones natural operators (predecessor, truncated subtraction,
/// remainder, quotient) recognized exactly from their admitted equations and
/// helper equations, each with a fixed dependency list recorded whatever the
/// arguments are.
pub fn shortcut_equations(env: &Environment, name: &str, allowed: &BTreeSet<String>) -> Option<(String, Vec<String>)> {
    let shortcut = if name == format!("{NAT_REC}predecessor") {
        "predecessor"
    } else if name == format!("{NAT_SUB}sub") {
        "sub"
    } else if name == format!("{NAT_MOD}mod") {
        "mod"
    } else if name == format!("{NAT_DIV}quotientNat") {
        "quotient"
    } else {
        return None;
    };
    let dependencies: Vec<String> = match shortcut {
        "predecessor" => vec![format!("{NAT_REC}predecessor")],
        "sub" => vec![format!("{NAT_SUB}sub"), format!("{NAT_REC}predecessor")],
        "mod" => mod_definitions(),
        _ => [vec![format!("{NAT_DIV}quotientNat")], mod_definitions()].concat(),
    };
    if !dependencies.iter().all(|item| allowed.contains(item)) {
        return None;
    }
    let zero = ctor("zero", vec![]);
    let succ = |n: &str| ctor("succ", vec![bind(n)]);
    let predecessor_name = format!("{NAT_REC}predecessor");
    let sub_name = format!("{NAT_SUB}sub");
    let mod_name = format!("{NAT_MOD}mod");
    let quotient_name = format!("{NAT_DIV}quotientNat");
    let choose_name = format!("{NAT_MOD}chooseNat");
    let equal_name = format!("{NAT_MOD}equalNat");
    let predecessor_exact =
        exact(env, &predecessor_name, &["n"], &[(vec![zero.clone()], app("zero", vec![])), (vec![succ("n")], v("n"))]);
    let recognized = if shortcut == "predecessor" {
        predecessor_exact
    } else if shortcut == "sub" {
        predecessor_exact
            && exact_at(
                env,
                &sub_name,
                &["m", "n"],
                1,
                &[
                    (vec![bind("m"), zero.clone()], v("m")),
                    (vec![bind("m"), succ("n")], app(&predecessor_name, vec![app(&sub_name, vec![v("m"), v("n")])])),
                ],
            )
    } else {
        // The remainder equations, shared by the quotient.
        let remainder = |n: &str, d: &str| app(&mod_name, vec![v(n), v(d)]);
        let mod_exact = decision_equations(env, &equal_name, allowed).is_some()
            && exact(
                env,
                &choose_name,
                &["condition", "yes", "no"],
                &[
                    (vec![ctor(&format!("{BOOL}false"), vec![]), bind("yes"), bind("no")], v("no")),
                    (vec![ctor(&format!("{BOOL}true"), vec![]), bind("yes"), bind("no")], v("yes")),
                ],
            )
            && exact_body(
                env,
                &format!("{NAT_MOD}nextRemainder"),
                &["d", "r"],
                &app(
                    &choose_name,
                    vec![app(&equal_name, vec![app("succ", vec![v("r")]), v("d")]), nat(0), app("succ", vec![v("r")])],
                ),
            )
            && exact(
                env,
                &mod_name,
                &["n", "d"],
                &[
                    (vec![zero.clone(), bind("d")], app("zero", vec![])),
                    (vec![succ("n"), bind("d")], app(&format!("{NAT_MOD}nextRemainder"), vec![v("d"), remainder("n", "d")])),
                ],
            );
        if shortcut == "mod" {
            mod_exact
        } else {
            mod_exact
                && exact(
                    env,
                    &quotient_name,
                    &["n", "d"],
                    &[
                        (vec![zero.clone(), bind("d")], app("zero", vec![])),
                        (
                            vec![succ("n"), bind("d")],
                            app(
                                &choose_name,
                                vec![
                                    app(&equal_name, vec![app("succ", vec![remainder("n", "d")]), v("d")]),
                                    app("succ", vec![app(&quotient_name, vec![v("n"), v("d")])]),
                                    app(&quotient_name, vec![v("n"), v("d")]),
                                ],
                            ),
                        ),
                    ],
                )
        }
    };
    if recognized {
        Some((shortcut.to_string(), dependencies))
    } else {
        None
    }
}

fn execute_shortcut(shortcut: &str, first: &BigUint, second: &BigUint) -> BigUint {
    match shortcut {
        "predecessor" => {
            if first.is_zero() {
                BigUint::zero()
            } else {
                first - BigUint::one()
            }
        }
        "sub" => {
            if first > second {
                first - second
            } else {
                BigUint::zero()
            }
        }
        // The remainder by zero never wraps, so n % 0 = n; the quotient by zero is zero.
        "mod" => {
            if second.is_zero() {
                first.clone()
            } else {
                first % second
            }
        }
        _ => {
            if second.is_zero() {
                BigUint::zero()
            } else {
                first / second
            }
        }
    }
}

pub fn equation_for<'a>(recursive: &'a Recursive, constructor: &str) -> Option<&'a Equation> {
    let position = recursive.decreasing_parameter;
    recursive.equations.iter().find(|equation| match equation.patterns.get(position) {
        Some(Pattern::Ctor(name, _)) => name == constructor,
        _ => false,
    })
}

pub fn match_pattern(pattern: &Pattern, value: &Val, bindings: &mut HashMap<String, Val>) -> bool {
    match pattern {
        Pattern::Bind(name) => {
            if let Some(previous) = bindings.get(name) {
                return previous == value;
            }
            bindings.insert(name.clone(), value.clone());
            true
        }
        Pattern::Ctor(name, args) if name == "zero" => args.is_empty() && *value == Val::Nat(BigUint::zero()),
        Pattern::Ctor(name, args) if name == "succ" => match value {
            Val::Nat(number) if args.len() == 1 && !number.is_zero() => {
                match_pattern(&args[0], &Val::Nat(number - BigUint::one()), bindings)
            }
            _ => false,
        },
        Pattern::Ctor(name, args) => match value {
            Val::App(head, items) => {
                head == name
                    && items.len() == args.len()
                    && args.iter().zip(items).all(|(child, item)| match_pattern(child, item, bindings))
            }
            Val::Nat(_) => false,
        },
    }
}

fn find_recursive_call<'a>(term: &'a Term, name: &str, patterns: &[Pattern], position: usize, predecessor: &str) -> Option<&'a Term> {
    if let Term::App(fn_name, args) = term {
        if fn_name == name && args.len() == patterns.len() {
            let good = args.iter().enumerate().all(|(index, argument)| {
                let expected: Option<&str> = if index == position {
                    Some(predecessor)
                } else {
                    match &patterns[index] {
                        Pattern::Bind(variable) => Some(variable.as_str()),
                        _ => None,
                    }
                };
                matches!((argument, expected), (Term::Var(actual), Some(expected)) if actual == expected)
            });
            if good {
                return Some(term);
            }
        }
        for argument in args {
            if let Some(found) = find_recursive_call(argument, name, patterns, position, predecessor) {
                return Some(found);
            }
        }
    }
    None
}

fn is_other_body(term: &Term, patterns: &[Pattern], position: usize) -> bool {
    match term {
        Term::Var(name) => patterns
            .iter()
            .enumerate()
            .any(|(index, pattern)| index != position && matches!(pattern, Pattern::Bind(variable) if variable == name)),
        _ => false,
    }
}

fn is_successor_of(term: &Term, variable: Option<&str>) -> bool {
    match (term, variable) {
        (Term::App(fn_name, args), Some(variable)) => {
            fn_name == "succ" && args.len() == 1 && args[0] == Term::Var(variable.to_string())
        }
        _ => false,
    }
}

pub struct Evaluator<'a> {
    env: &'a Environment,
    allowed: BTreeSet<String>,
    fuel: i64,
    pub used: BTreeSet<String>,
    memo: HashMap<(String, Vec<Val>), Val>,
    prefixes: HashMap<(String, Vec<Val>), (BigUint, Val)>,
    classifications: HashMap<String, Option<(String, Vec<String>)>>,
    decisions: HashMap<String, Option<(String, Vec<String>)>>,
    shortcuts: HashMap<String, Option<(String, Vec<String>)>>,
}

type Override = (String, Vec<Val>, Val);

impl<'a> Evaluator<'a> {
    pub fn new(env: &'a Environment, allowed: BTreeSet<String>) -> Self {
        Evaluator {
            env,
            allowed,
            fuel: fuel(),
            used: BTreeSet::new(),
            memo: HashMap::new(),
            prefixes: HashMap::new(),
            classifications: HashMap::new(),
            decisions: HashMap::new(),
            shortcuts: HashMap::new(),
        }
    }

    fn spend(&mut self) -> Result<()> {
        self.fuel -= 1;
        if self.fuel < 0 {
            return fail("ground evaluation exhausted its fuel");
        }
        Ok(())
    }

    pub fn evaluate(&mut self, term: &Term, bindings: &HashMap<String, Val>, override_: Option<&Override>) -> Result<Val> {
        self.spend()?;
        match term {
            Term::Nat(value) => Ok(Val::Nat(value.clone())),
            Term::Var(name) => match bindings.get(name) {
                Some(value) => Ok(value.clone()),
                None => fail(format!("ground computation contains free variable {name}")),
            },
            Term::App(fn_name, args) => {
                let mut values = Vec::with_capacity(args.len());
                for arg in args {
                    values.push(self.evaluate(arg, bindings, override_)?);
                }
                self.invoke(fn_name, values, override_)
            }
        }
    }

    pub fn invoke(&mut self, fn_name: &str, args: Vec<Val>, override_: Option<&Override>) -> Result<Val> {
        self.spend()?;
        if fn_name == "zero" && args.is_empty() {
            return Ok(Val::Nat(BigUint::zero()));
        }
        if fn_name == "succ" && args.len() == 1 {
            if let Val::Nat(value) = &args[0] {
                return Ok(Val::Nat(value + BigUint::one()));
            }
        }
        if let Some((name, expected, value)) = override_ {
            if name == fn_name && *expected == args {
                return Ok(value.clone());
            }
        }
        let key = (fn_name.to_string(), args.clone());
        if let Some(value) = self.memo.get(&key) {
            return Ok(value.clone());
        }
        if self.allowed.contains(fn_name) {
            if let Some(recursive) = self.env.recursive.get(fn_name) {
                if !self.decisions.contains_key(fn_name) {
                    let decision = decision_equations(self.env, fn_name, &self.allowed);
                    self.decisions.insert(fn_name.to_string(), decision);
                }
                let decision = self.decisions.get(fn_name).cloned().flatten();
                if let Some((operator, definitions)) = decision {
                    if let [Val::Nat(left), Val::Nat(right)] = args.as_slice() {
                        self.used.extend(definitions.iter().cloned());
                        let result = if operator == "minus" {
                            Val::Nat(if left >= right { left - right } else { BigUint::zero() })
                        } else {
                            let truth = if operator == "equal" { left == right } else { left < right };
                            Val::App(format!("{BOOL}{}", if truth { "true" } else { "false" }), vec![])
                        };
                        self.memo.insert(key, result.clone());
                        return Ok(result);
                    }
                }
                if !self.shortcuts.contains_key(fn_name) {
                    let shortcut = shortcut_equations(self.env, fn_name, &self.allowed);
                    self.shortcuts.insert(fn_name.to_string(), shortcut);
                }
                let shortcut = self.shortcuts.get(fn_name).cloned().flatten();
                if let Some((operator, definitions)) = shortcut {
                    let value = match (operator.as_str(), args.as_slice()) {
                        ("predecessor", [Val::Nat(first)]) => Some(execute_shortcut(&operator, first, &BigUint::zero())),
                        ("predecessor", _) => None,
                        (_, [Val::Nat(first), Val::Nat(second)]) => Some(execute_shortcut(&operator, first, second)),
                        _ => None,
                    };
                    if let Some(value) = value {
                        self.used.extend(definitions.iter().cloned());
                        let result = Val::Nat(value);
                        self.memo.insert(key, result.clone());
                        return Ok(result);
                    }
                }
                let classification = self.classify(fn_name, &mut BTreeSet::new());
                if let Some((operator, definitions)) = classification {
                    if args.iter().all(|arg| matches!(arg, Val::Nat(_))) {
                        self.used.extend(definitions.iter().cloned());
                        let numbers: Vec<&BigUint> = args
                            .iter()
                            .map(|arg| match arg {
                                Val::Nat(value) => value,
                                Val::App(..) => unreachable!(),
                            })
                            .collect();
                        let result = match operator.as_str() {
                            "add" => Val::Nat(numbers[0] + numbers[1]),
                            "mul" => Val::Nat(numbers[0] * numbers[1]),
                            _ => {
                                let mut product = BigUint::one();
                                let mut value = BigUint::from(2u32);
                                while &value <= numbers[0] {
                                    self.spend()?;
                                    product *= &value;
                                    value += BigUint::one();
                                }
                                Val::Nat(product)
                            }
                        };
                        self.memo.insert(key, result.clone());
                        return Ok(result);
                    }
                }
                if let Some(primitive) = self.primitive(fn_name, recursive, &args)? {
                    self.used.insert(fn_name.to_string());
                    self.memo.insert(key, primitive.clone());
                    return Ok(primitive);
                }
                for equation in &recursive.equations {
                    let mut found = HashMap::new();
                    if equation.patterns.len() == args.len()
                        && equation.patterns.iter().zip(&args).all(|(pattern, arg)| match_pattern(pattern, arg, &mut found))
                    {
                        self.used.insert(fn_name.to_string());
                        let result = self.evaluate(&equation.body, &found, override_)?;
                        self.memo.insert(key, result.clone());
                        return Ok(result);
                    }
                }
            }
            if let Some(explicit) = self.env.bodies.get(fn_name) {
                self.used.insert(fn_name.to_string());
                let found: HashMap<String, Val> = explicit.parameters.iter().cloned().zip(args.iter().cloned()).collect();
                let result = self.evaluate(&explicit.body, &found, override_)?;
                self.memo.insert(key, result.clone());
                return Ok(result);
            }
        }
        let result = Val::App(fn_name.to_string(), args);
        self.memo.insert(key, result.clone());
        Ok(result)
    }

    /// A primitive recursion on a natural argument evaluated as a prefix
    /// iteration, so deep recursion never grows the host stack.
    fn primitive(&mut self, name: &str, recursive: &Recursive, args: &[Val]) -> Result<Option<Val>> {
        let position = recursive.decreasing_parameter;
        let count = match args.get(position) {
            Some(Val::Nat(value)) => value.clone(),
            _ => return Ok(None),
        };
        let (zero, successor) = match (equation_for(recursive, "zero"), equation_for(recursive, "succ")) {
            (Some(zero), Some(successor)) => (zero.clone(), successor.clone()),
            _ => return Ok(None),
        };
        let mut current = args.to_vec();
        current[position] = Val::Nat(BigUint::zero());
        let mut bindings = HashMap::new();
        if zero.patterns.len() != current.len()
            || !zero.patterns.iter().zip(&current).all(|(pattern, value)| match_pattern(pattern, value, &mut bindings))
        {
            return Ok(None);
        }
        let prefix_key = (name.to_string(), current.clone());
        let (mut index, mut value) = match self.prefixes.get(&prefix_key) {
            Some((start, value)) if start <= &count => (start.clone(), value.clone()),
            _ => {
                let value = self.evaluate(&zero.body, &bindings, None)?;
                self.memo.insert(prefix_key.clone(), value.clone());
                (BigUint::zero(), value)
            }
        };
        while index < count {
            let mut next_args = args.to_vec();
            next_args[position] = Val::Nat(&index + BigUint::one());
            let mut bindings = HashMap::new();
            if successor.patterns.len() != next_args.len()
                || !successor.patterns.iter().zip(&next_args).all(|(pattern, item)| match_pattern(pattern, item, &mut bindings))
            {
                return Ok(None);
            }
            let mut previous = args.to_vec();
            previous[position] = Val::Nat(index.clone());
            let override_: Override = (name.to_string(), previous, value.clone());
            value = self.evaluate(&successor.body, &bindings, Some(&override_))?;
            self.memo.insert((name.to_string(), next_args), value.clone());
            index += BigUint::one();
            self.prefixes.insert(prefix_key.clone(), (index.clone(), value.clone()));
        }
        Ok(Some(value))
    }

    /// Recognize the admitted addition, multiplication, and factorial schemas.
    fn classify(&mut self, name: &str, visiting: &mut BTreeSet<String>) -> Option<(String, Vec<String>)> {
        if let Some(cached) = self.classifications.get(name) {
            return cached.clone();
        }
        if !self.allowed.contains(name) || visiting.contains(name) || !self.env.recursive.contains_key(name) {
            return None;
        }
        visiting.insert(name.to_string());
        let recursive = self.env.recursive.get(name).expect("checked").clone();
        let mut result: Option<(String, Vec<String>)> = None;
        if let (Some(zero), Some(successor)) = (equation_for(&recursive, "zero"), equation_for(&recursive, "succ")) {
            let position = recursive.decreasing_parameter;
            let predecessor: Option<String> = match &successor.patterns[position] {
                Pattern::Ctor(_, args) if args.len() == 1 => match &args[0] {
                    Pattern::Bind(variable) => Some(variable.clone()),
                    _ => None,
                },
                _ => None,
            };
            let call = predecessor
                .as_deref()
                .and_then(|variable| find_recursive_call(&successor.body, name, &successor.patterns, position, variable))
                .cloned();
            let body = &successor.body;
            let parameter_count = recursive.parameters.len();
            if let Some(call) = &call {
                if parameter_count == 2
                    && is_other_body(&zero.body, &zero.patterns, position)
                    && matches!(body, Term::App(fn_name, args) if fn_name == "succ" && args.len() == 1 && &args[0] == call)
                {
                    result = Some(("add".to_string(), vec![name.to_string()]));
                }
            }
            if result.is_none() {
                if let Term::App(fn_name, args) = body {
                    let nested = self.classify(fn_name, visiting);
                    if let (Some(call), Some((operator, definitions))) = (&call, &nested) {
                        let mut names: BTreeSet<String> = definitions.iter().cloned().collect();
                        names.insert(name.to_string());
                        let zero_value = natural_value(&zero.body);
                        if parameter_count == 2
                            && zero_value == Some(BigUint::zero())
                            && args.len() == 2
                            && operator == "add"
                            && args.iter().any(|arg| arg == call)
                            && args.iter().any(|arg| is_other_body(arg, &successor.patterns, position))
                        {
                            result = Some(("mul".to_string(), names.into_iter().collect()));
                        } else if parameter_count == 1
                            && zero_value == Some(BigUint::one())
                            && args.len() == 2
                            && operator == "mul"
                            && args.iter().any(|arg| arg == call)
                            && args.iter().any(|arg| is_successor_of(arg, predecessor.as_deref()))
                        {
                            result = Some(("factorial".to_string(), names.into_iter().collect()));
                        }
                    }
                }
            }
        }
        visiting.remove(name);
        self.classifications.insert(name.to_string(), result.clone());
        result
    }
}

/// The ground computation rule of a proof tape: both sides normalize to the
/// same value, and the definitions unfolded are exactly those listed.
pub fn check_computation(env: &Environment, left: &Term, right: &Term, definitions: &[String], require_known: bool) -> Result<()> {
    let mut sorted: Vec<String> = definitions.to_vec();
    sorted.sort();
    sorted.dedup();
    if sorted != definitions {
        return fail("computation dependencies must be unique and sorted");
    }
    if require_known && definitions.iter().any(|name| !env.bodies.contains_key(name) && !env.recursive.contains_key(name)) {
        return fail("unknown computational definition");
    }
    let allowed: BTreeSet<String> = definitions.iter().cloned().collect();
    let mut left_eval = Evaluator::new(env, allowed.clone());
    let mut right_eval = Evaluator::new(env, allowed);
    let left_value = left_eval.evaluate(left, &HashMap::new(), None)?;
    let right_value = right_eval.evaluate(right, &HashMap::new(), None)?;
    let used: Vec<String> = left_eval.used.union(&right_eval.used).cloned().collect();
    if used != definitions {
        return fail("computation certificate has an inexact definition dependency list");
    }
    if left_value != right_value {
        return fail("closed terms have different normal forms");
    }
    Ok(())
}

/// Equality of two rational classes by the proved quotient criterion and an
/// exact natural cross-product computation.
pub fn check_rational_class_equality(env: &Environment, left: &Term, right: &Term) -> Result<()> {
    let class = "Grace.Cumulus.Rat.Operations.rationalClass";
    let theorem = format!("{class}.eq");
    let add_name = format!("{NAT_REC}add");
    let mul_name = format!("{NAT_REC}mul");
    let cross = |first: &[Term], second: &[Term]| -> Formula {
        eq(
            app(&add_name, vec![app(&mul_name, vec![second[2].clone(), first[0].clone()]), app(&mul_name, vec![first[2].clone(), second[1].clone()])]),
            app(&add_name, vec![app(&mul_name, vec![first[2].clone(), second[0].clone()]), app(&mul_name, vec![second[2].clone(), first[1].clone()])]),
        )
    };
    let arguments = |term: &Term| -> Option<Vec<Term>> {
        match term {
            Term::App(fn_name, args) if fn_name == class && args.len() == 3 => Some(args.clone()),
            _ => None,
        }
    };
    let (left_args, right_args) = match (arguments(left), arguments(right)) {
        (Some(left_args), Some(right_args)) => (left_args, right_args),
        _ => return fail("rational computation needs ground classes with positive denominators"),
    };
    let all_natural = left_args.iter().chain(right_args.iter()).all(|arg| natural_value(arg).is_some());
    let positive = |term: &Term| natural_value(term).map(|value| !value.is_zero()).unwrap_or(false);
    if !env.datatypes.contains_key("Naturals") || !all_natural || !positive(&left_args[2]) || !positive(&right_args[2]) {
        return fail("rational computation needs ground classes with positive denominators");
    }
    let names = ["a", "b", "m", "c", "d", "n"];
    let variables: Vec<Term> = names.iter().map(|name| v(name)).collect();
    let zero_equal = |variable: &Term| imp(eq(variable.clone(), nat(0)), Formula::Bottom);
    let mut premises: Vec<Formula> = variables.iter().map(|item| pred("Nat", vec![item.clone()])).collect();
    premises.push(zero_equal(&variables[2]));
    premises.push(zero_equal(&variables[5]));
    premises.push(cross(&variables[0..3], &variables[3..6]));
    let mut schema = eq(app(class, variables[0..3].to_vec()), app(class, variables[3..6].to_vec()));
    for premise in premises.into_iter().rev() {
        schema = imp(premise, schema);
    }
    for name in names.iter().rev() {
        schema = forall(name, schema);
    }
    match env.theorems.get(&theorem) {
        Some(actual) if *actual == schema => {}
        _ => return fail("rational computation requires proved quotient criterion"),
    }
    let concrete = cross(&left_args, &right_args);
    let allowed: BTreeSet<String> = [add_name.clone(), mul_name.clone()].into_iter().collect();
    let (concrete_left, concrete_right) = match concrete {
        Formula::Eq(left, right) => (*left, *right),
        _ => unreachable!(),
    };
    let mut left_eval = Evaluator::new(env, allowed.clone());
    let mut right_eval = Evaluator::new(env, allowed.clone());
    let first = left_eval.evaluate(&concrete_left, &HashMap::new(), None)?;
    let second = right_eval.evaluate(&concrete_right, &HashMap::new(), None)?;
    let used: BTreeSet<String> = left_eval.used.union(&right_eval.used).cloned().collect();
    if first != second || used != allowed {
        return fail("rational cross-product computation failed");
    }
    Ok(())
}
