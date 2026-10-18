// The G17M proof machine: tape decoding, arena validation, the thirty
// inference rules, and theorem boundaries.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use crate::ast::{natural_value, Formula, Term};
use crate::compute;
use crate::environment::Environment;
use crate::support::{fail, hex, is_natural_literal, natural_int, sha256_bytes, Reader, Result, MAX_COUNT, MAX_VECTOR};
use num_bigint::BigUint;
use num_traits::One;
use serde_json::Value;
use std::collections::{BTreeMap, HashMap};

pub const MAGIC: &[u8; 4] = b"G17M";
pub const VERSION: u8 = 4;
const DIGEST_BYTES: usize = 32;

#[derive(Debug, Clone)]
pub struct Program {
    pub environment: String,
    pub symbols: Vec<String>,
    pub terms: Vec<Vec<u32>>,
    pub formulas: Vec<Vec<u32>>,
    pub contexts: Vec<Vec<u32>>,
    pub code: Vec<Vec<u32>>,
    pub root: u32,
    pub theorems: Vec<(u32, u32)>,
}

fn read_vectors(reader: &mut Reader, name: &str) -> Result<Vec<Vec<u32>>> {
    let count = reader.count(name, MAX_COUNT)?;
    let mut result = Vec::with_capacity(count.min(1 << 16));
    for index in 0..count {
        let words = reader.count(&format!("{name}[{index}] words"), MAX_VECTOR)?;
        let mut vector = Vec::with_capacity(words.min(1 << 12));
        for _ in 0..words {
            vector.push(reader.uint()? as u32);
        }
        result.push(vector);
    }
    Ok(result)
}

/// Decode and validate a G17M tape; the digest over every preceding byte
/// is checked first.
pub fn decode(data: &[u8]) -> Result<Program> {
    if data.len() < 4 + 2 + 32 + DIGEST_BYTES {
        return fail("truncated G17M certificate");
    }
    let (body, supplied) = data.split_at(data.len() - DIGEST_BYTES);
    if sha256_bytes(body) != supplied {
        return fail("corrupted G17M certificate digest");
    }
    let mut reader = Reader::new(body);
    if reader.bytes(4)? != MAGIC {
        return fail("bad G17M magic");
    }
    if reader.byte()? != VERSION {
        return fail("unsupported G17M version");
    }
    let flags = reader.byte()?;
    if flags > 1 {
        return fail("unsupported G17M flags");
    }
    let environment = hex(reader.bytes(32)?);
    let symbol_count = reader.count("symbols", MAX_COUNT)?;
    let mut symbols = Vec::with_capacity(symbol_count.min(1 << 16));
    for _ in 0..symbol_count {
        symbols.push(reader.string()?);
    }
    let terms = read_vectors(&mut reader, "terms")?;
    let formulas = read_vectors(&mut reader, "formulas")?;
    let contexts = read_vectors(&mut reader, "contexts")?;
    let code = read_vectors(&mut reader, "instructions")?;
    let root = reader.uint()? as u32;
    let theorem_count = reader.count("theorems", MAX_COUNT)?;
    let mut theorems = Vec::with_capacity(theorem_count.min(1 << 16));
    for _ in 0..theorem_count {
        theorems.push((reader.uint()? as u32, reader.uint()? as u32));
    }
    if reader.offset != reader.len() {
        return fail("trailing G17M data");
    }
    if (flags == 0) != theorems.is_empty() {
        return fail("G17M theorem-boundary flag mismatch");
    }
    let program = Program { environment, symbols, terms, formulas, contexts, code, root, theorems };
    validate_program(&program)?;
    Ok(program)
}

pub fn validate_program(p: &Program) -> Result<()> {
    let mut seen_symbols = std::collections::HashSet::with_capacity(p.symbols.len());
    for symbol in &p.symbols {
        if symbol.is_empty() || !seen_symbols.insert(symbol.as_str()) {
            return fail("empty or duplicate G17M symbol");
        }
    }
    let symbol_count = p.symbols.len() as u32;
    let mut seen: std::collections::HashSet<&[u32]> = std::collections::HashSet::with_capacity(p.terms.len());
    for (index, node) in p.terms.iter().enumerate() {
        if node.len() < 2 {
            return fail(format!("malformed G17M term {index}"));
        }
        let op = node[0];
        let bad = match op {
            0 => node.len() != 2 || node[1] >= symbol_count,
            1 => node.len() != 2,
            2 => node[1] >= symbol_count || node[2..].iter().any(|child| *child as usize >= index),
            3 => node.len() != 2 || node[1] >= symbol_count || !is_natural_literal(&p.symbols[node[1] as usize]),
            _ => return fail(format!("unknown G17M term opcode {op}")),
        };
        if bad {
            return fail(format!("malformed G17M term {index}"));
        }
        if !seen.insert(node.as_slice()) {
            return fail(format!("duplicate G17M term {index}"));
        }
    }
    seen.clear();
    let term_count = p.terms.len() as u32;
    for (index, node) in p.formulas.iter().enumerate() {
        if node.is_empty() {
            return fail(format!("malformed G17M formula {index}"));
        }
        let op = node[0];
        let bad = match op {
            0 => node.len() != 1,
            1 => node.len() != 3 || node[1] >= term_count || node[2] >= term_count,
            2 => node.len() < 2 || node[1] >= symbol_count || node[2..].iter().any(|x| *x >= term_count),
            3 | 5 | 6 | 7 => node.len() != 3 || node[1] as usize >= index || node[2] as usize >= index,
            4 | 8 => node.len() != 2 || node[1] as usize >= index,
            _ => return fail(format!("unknown G17M formula opcode {op}")),
        };
        if bad {
            return fail(format!("malformed G17M formula {index}"));
        }
        if !seen.insert(node.as_slice()) {
            return fail(format!("duplicate G17M formula {index}"));
        }
    }
    seen.clear();
    let formula_count = p.formulas.len() as u32;
    for (index, context) in p.contexts.iter().enumerate() {
        if context.len() as u64 > MAX_VECTOR || context.iter().any(|x| *x >= formula_count) {
            return fail(format!("malformed G17M context {index}"));
        }
        if !seen.insert(context.as_slice()) {
            return fail(format!("duplicate G17M context {index}"));
        }
    }
    let context_count = p.contexts.len() as u32;
    for (pc, instruction) in p.code.iter().enumerate() {
        if instruction.len() < 4 || instruction.len() as u64 > MAX_VECTOR {
            return fail(format!("malformed G17M instruction {pc}"));
        }
        let (op, claim, context, premises) = (instruction[0], instruction[1], instruction[2], instruction[3] as usize);
        if op > 29 || claim >= formula_count || context >= context_count || premises > instruction.len() - 4 {
            return fail(format!("invalid G17M instruction {pc}"));
        }
        if instruction[4..4 + premises].iter().any(|premise| *premise as usize >= pc) {
            return fail(format!("forward premise at G17M instruction {pc}"));
        }
    }
    if p.root as usize >= p.code.len() {
        return fail("invalid G17M root");
    }
    let mut names = std::collections::HashSet::new();
    for (name, root) in &p.theorems {
        if *name >= symbol_count || *root as usize >= p.code.len() || !names.insert(*name) {
            return fail("malformed G17M theorem boundary");
        }
    }
    Ok(())
}

fn word_vectors(value: &Value, what: &str) -> Result<Vec<Vec<u32>>> {
    match value {
        Value::Array(items) => items
            .iter()
            .map(|item| match item {
                Value::Array(words) => words
                    .iter()
                    .map(|word| match natural_int(word) {
                        Some(n) if n <= 0xFFFF_FFFF => Ok(n as u32),
                        _ => fail(format!("malformed embedded G17M {what}")),
                    })
                    .collect(),
                _ => fail(format!("malformed embedded G17M {what}")),
            })
            .collect(),
        _ => fail(format!("malformed embedded G17M {what}")),
    }
}

/// A theorem batch embeds its program as JSON arrays of words.
pub fn program_from_json(value: &Value) -> Result<Program> {
    if value.get("version") != Some(&Value::Number(u64::from(VERSION).into())) {
        return fail("unsupported embedded G17M version");
    }
    let environment = match value.get("environment") {
        Some(Value::String(text)) => text.clone(),
        _ => return fail("malformed embedded G17M program"),
    };
    let symbols = match value.get("symbols") {
        Some(Value::Array(items)) => items
            .iter()
            .map(|item| match item {
                Value::String(text) => Ok(text.clone()),
                _ => fail("malformed embedded G17M program"),
            })
            .collect::<Result<Vec<_>>>()?,
        _ => return fail("malformed embedded G17M program"),
    };
    let get = |key: &str| value.get(key).ok_or_else(|| crate::support::CheckError("malformed embedded G17M program".into()));
    let terms = word_vectors(get("terms")?, "terms")?;
    let formulas = word_vectors(get("formulas")?, "formulas")?;
    let contexts = word_vectors(get("contexts")?, "contexts")?;
    let code = word_vectors(get("code")?, "code")?;
    let root = match natural_int(get("root")?) {
        Some(n) if n <= 0xFFFF_FFFF => n as u32,
        _ => return fail("malformed embedded G17M program"),
    };
    let theorems = word_vectors(get("theorems")?, "theorems")?
        .into_iter()
        .map(|pair| if pair.len() == 2 { Ok((pair[0], pair[1])) } else { fail("malformed embedded G17M program") })
        .collect::<Result<Vec<_>>>()?;
    let program = Program { environment, symbols, terms, formulas, contexts, code, root, theorems };
    validate_program(&program)?;
    Ok(program)
}

/// The intern tables of a program, extended as rules construct new nodes.
pub struct Arena {
    pub symbols: Vec<String>,
    pub terms: Vec<Vec<u32>>,
    pub formulas: Vec<Vec<u32>>,
    pub contexts: Vec<Vec<u32>>,
    symbol_map: HashMap<String, usize>,
    term_map: HashMap<Vec<u32>, usize>,
    formula_map: HashMap<Vec<u32>, usize>,
    abstract_cache: HashMap<(usize, usize, u32), usize>,
    substitution_cache: HashMap<(usize, usize, usize), usize>,
    instantiate_cache: HashMap<(usize, usize, u32), usize>,
}

impl Arena {
    pub fn new(p: &Program) -> Arena {
        let symbol_map = p.symbols.iter().enumerate().map(|(index, symbol)| (symbol.clone(), index)).collect();
        let term_map = p.terms.iter().enumerate().map(|(index, node)| (node.clone(), index)).collect();
        let formula_map = p.formulas.iter().enumerate().map(|(index, node)| (node.clone(), index)).collect();
        Arena {
            symbols: p.symbols.clone(),
            terms: p.terms.clone(),
            formulas: p.formulas.clone(),
            contexts: p.contexts.clone(),
            symbol_map,
            term_map,
            formula_map,
            abstract_cache: HashMap::new(),
            substitution_cache: HashMap::new(),
            instantiate_cache: HashMap::new(),
        }
    }

    pub fn symbol(&self, index: u32) -> Result<&str> {
        match self.symbols.get(index as usize) {
            Some(symbol) => Ok(symbol.as_str()),
            None => fail(format!("invalid machine symbol {index}")),
        }
    }

    pub fn symbol_id(&mut self, value: &str) -> usize {
        if let Some(index) = self.symbol_map.get(value) {
            return *index;
        }
        let index = self.symbols.len();
        self.symbols.push(value.to_string());
        self.symbol_map.insert(value.to_string(), index);
        index
    }

    pub fn term_node(&mut self, node: Vec<u32>) -> usize {
        if let Some(index) = self.term_map.get(&node) {
            return *index;
        }
        let index = self.terms.len();
        self.terms.push(node.clone());
        self.term_map.insert(node, index);
        index
    }

    pub fn formula_node(&mut self, node: Vec<u32>) -> usize {
        if let Some(index) = self.formula_map.get(&node) {
            return *index;
        }
        let index = self.formulas.len();
        self.formulas.push(node.clone());
        self.formula_map.insert(node, index);
        index
    }

    fn natural_node(&mut self, value: &BigUint) -> usize {
        let symbol = self.symbol_id(&value.to_string()) as u32;
        self.term_node(vec![3, symbol])
    }

    /// Applications of `zero` and `succ` fold into natural literals.
    pub fn application_symbol(&mut self, fn_id: usize, args: Vec<usize>) -> usize {
        let name = self.symbols[fn_id].as_str();
        if name == "zero" && args.is_empty() {
            return self.natural_node(&BigUint::from(0u32));
        }
        if name == "succ" && args.len() == 1 && self.terms[args[0]][0] == 3 {
            let value = BigUint::parse_bytes(self.symbols[self.terms[args[0]][1] as usize].as_bytes(), 10).expect("natural literal");
            return self.natural_node(&(value + BigUint::one()));
        }
        let mut node = Vec::with_capacity(args.len() + 2);
        node.push(2);
        node.push(fn_id as u32);
        node.extend(args.iter().map(|arg| *arg as u32));
        self.term_node(node)
    }

    pub fn application(&mut self, fn_name: &str, args: Vec<usize>) -> usize {
        let fn_id = self.symbol_id(fn_name);
        self.application_symbol(fn_id, args)
    }

    pub fn predicate(&mut self, name: &str, args: Vec<usize>) -> usize {
        let id = self.symbol_id(name) as u32;
        let mut node = Vec::with_capacity(args.len() + 2);
        node.push(2);
        node.push(id);
        node.extend(args.iter().map(|arg| *arg as u32));
        self.formula_node(node)
    }

    pub fn intern_term(&mut self, term: &Term, binders: &[String]) -> usize {
        if let Some(value) = natural_value(term) {
            return self.natural_node(&value);
        }
        match term {
            Term::Var(name) => {
                if let Some(position) = binders.iter().rev().position(|binder| binder == name) {
                    return self.term_node(vec![1, position as u32]);
                }
                let id = self.symbol_id(name) as u32;
                self.term_node(vec![0, id])
            }
            Term::App(fn_name, args) => {
                let interned: Vec<usize> = args.iter().map(|arg| self.intern_term(arg, binders)).collect();
                self.application(fn_name, interned)
            }
            Term::Nat(value) => self.natural_node(value),
        }
    }

    pub fn intern_formula(&mut self, formula: &Formula, binders: &mut Vec<String>) -> usize {
        match formula {
            Formula::Bottom => self.formula_node(vec![0]),
            Formula::Eq(left, right) => {
                let left = self.intern_term(left, binders) as u32;
                let right = self.intern_term(right, binders) as u32;
                self.formula_node(vec![1, left, right])
            }
            Formula::Pred(name, args) => {
                let interned: Vec<usize> = args.iter().map(|arg| self.intern_term(arg, binders)).collect();
                self.predicate(name, interned)
            }
            Formula::Imp(left, right) | Formula::And(left, right) | Formula::Or(left, right) | Formula::Iff(left, right) => {
                let op = match formula {
                    Formula::Imp(..) => 3,
                    Formula::And(..) => 5,
                    Formula::Or(..) => 6,
                    _ => 7,
                };
                let left = self.intern_formula(left, binders) as u32;
                let right = self.intern_formula(right, binders) as u32;
                self.formula_node(vec![op, left, right])
            }
            Formula::Forall(variable, body) | Formula::Exists(variable, body) => {
                let op = if matches!(formula, Formula::Forall(..)) { 4 } else { 8 };
                binders.push(variable.clone());
                let inner = self.intern_formula(body, binders) as u32;
                binders.pop();
                self.formula_node(vec![op, inner])
            }
        }
    }

    pub fn abstract_term(&mut self, term: usize, symbol: usize, depth: u32) -> usize {
        let node = self.terms[term].clone();
        if node[0] == 0 && node[1] as usize == symbol {
            return self.term_node(vec![1, depth]);
        }
        if node[0] != 2 {
            return term;
        }
        let args: Vec<usize> = node[2..].iter().map(|x| self.abstract_term(*x as usize, symbol, depth)).collect();
        self.application_symbol(node[1] as usize, args)
    }

    pub fn abstract_formula(&mut self, formula: usize, symbol: usize, depth: u32) -> usize {
        let key = (formula, symbol, depth);
        if let Some(result) = self.abstract_cache.get(&key) {
            return *result;
        }
        let node = self.formulas[formula].clone();
        let result = match node[0] {
            0 => formula,
            1 => {
                let left = self.abstract_term(node[1] as usize, symbol, depth) as u32;
                let right = self.abstract_term(node[2] as usize, symbol, depth) as u32;
                self.formula_node(vec![1, left, right])
            }
            2 => {
                let mut out = vec![2, node[1]];
                for x in &node[2..] {
                    out.push(self.abstract_term(*x as usize, symbol, depth) as u32);
                }
                self.formula_node(out)
            }
            3 | 5 | 6 | 7 => {
                let left = self.abstract_formula(node[1] as usize, symbol, depth) as u32;
                let right = self.abstract_formula(node[2] as usize, symbol, depth) as u32;
                self.formula_node(vec![node[0], left, right])
            }
            _ => {
                let inner = self.abstract_formula(node[1] as usize, symbol, depth + 1) as u32;
                self.formula_node(vec![node[0], inner])
            }
        };
        self.abstract_cache.insert(key, result);
        result
    }

    pub fn substitute_term(&mut self, term: usize, symbol: usize, replacement: usize) -> usize {
        let node = self.terms[term].clone();
        if node[0] == 0 && node[1] as usize == symbol {
            return replacement;
        }
        if node[0] != 2 {
            return term;
        }
        let args: Vec<usize> = node[2..].iter().map(|x| self.substitute_term(*x as usize, symbol, replacement)).collect();
        self.application_symbol(node[1] as usize, args)
    }

    pub fn substitute_formula(&mut self, formula: usize, symbol: usize, replacement: usize) -> usize {
        let key = (formula, symbol, replacement);
        if let Some(result) = self.substitution_cache.get(&key) {
            return *result;
        }
        let node = self.formulas[formula].clone();
        let result = match node[0] {
            0 => formula,
            1 => {
                let left = self.substitute_term(node[1] as usize, symbol, replacement) as u32;
                let right = self.substitute_term(node[2] as usize, symbol, replacement) as u32;
                self.formula_node(vec![1, left, right])
            }
            2 => {
                let mut out = vec![2, node[1]];
                for x in &node[2..] {
                    out.push(self.substitute_term(*x as usize, symbol, replacement) as u32);
                }
                self.formula_node(out)
            }
            3 | 5 | 6 | 7 => {
                let left = self.substitute_formula(node[1] as usize, symbol, replacement) as u32;
                let right = self.substitute_formula(node[2] as usize, symbol, replacement) as u32;
                self.formula_node(vec![node[0], left, right])
            }
            _ => {
                let inner = self.substitute_formula(node[1] as usize, symbol, replacement) as u32;
                self.formula_node(vec![node[0], inner])
            }
        };
        self.substitution_cache.insert(key, result);
        result
    }

    pub fn shift_term(&mut self, term: usize, amount: u32) -> usize {
        if amount == 0 {
            return term;
        }
        let node = self.terms[term].clone();
        if node[0] == 1 {
            return self.term_node(vec![1, node[1] + amount]);
        }
        if node[0] != 2 {
            return term;
        }
        let args: Vec<usize> = node[2..].iter().map(|x| self.shift_term(*x as usize, amount)).collect();
        self.application_symbol(node[1] as usize, args)
    }

    pub fn instantiate_term(&mut self, term: usize, replacement: usize, depth: u32) -> usize {
        let node = self.terms[term].clone();
        if node[0] == 1 {
            if node[1] == depth {
                return self.shift_term(replacement, depth);
            }
            return if node[1] > depth { self.term_node(vec![1, node[1] - 1]) } else { term };
        }
        if node[0] != 2 {
            return term;
        }
        let args: Vec<usize> = node[2..].iter().map(|x| self.instantiate_term(*x as usize, replacement, depth)).collect();
        self.application_symbol(node[1] as usize, args)
    }

    pub fn instantiate_formula(&mut self, formula: usize, replacement: usize, depth: u32) -> usize {
        let key = (formula, replacement, depth);
        if let Some(result) = self.instantiate_cache.get(&key) {
            return *result;
        }
        let node = self.formulas[formula].clone();
        let result = match node[0] {
            0 => formula,
            1 => {
                let left = self.instantiate_term(node[1] as usize, replacement, depth) as u32;
                let right = self.instantiate_term(node[2] as usize, replacement, depth) as u32;
                self.formula_node(vec![1, left, right])
            }
            2 => {
                let mut out = vec![2, node[1]];
                for x in &node[2..] {
                    out.push(self.instantiate_term(*x as usize, replacement, depth) as u32);
                }
                self.formula_node(out)
            }
            3 | 5 | 6 | 7 => {
                let left = self.instantiate_formula(node[1] as usize, replacement, depth) as u32;
                let right = self.instantiate_formula(node[2] as usize, replacement, depth) as u32;
                self.formula_node(vec![node[0], left, right])
            }
            _ => {
                let inner = self.instantiate_formula(node[1] as usize, replacement, depth + 1) as u32;
                self.formula_node(vec![node[0], inner])
            }
        };
        self.instantiate_cache.insert(key, result);
        result
    }

    pub fn has_free_term(&self, term: usize, symbol: usize) -> bool {
        let node = &self.terms[term];
        (node[0] == 0 && node[1] as usize == symbol) || (node[0] == 2 && node[2..].iter().any(|x| self.has_free_term(*x as usize, symbol)))
    }

    pub fn has_free_formula(&self, formula: usize, symbol: usize) -> bool {
        let node = &self.formulas[formula];
        match node[0] {
            1 => self.has_free_term(node[1] as usize, symbol) || self.has_free_term(node[2] as usize, symbol),
            2 => node[2..].iter().any(|x| self.has_free_term(*x as usize, symbol)),
            3 | 5 | 6 | 7 => self.has_free_formula(node[1] as usize, symbol) || self.has_free_formula(node[2] as usize, symbol),
            4 | 8 => self.has_free_formula(node[1] as usize, symbol),
            _ => false,
        }
    }

    pub fn reify_term(&self, term: usize, binders: &[String]) -> Term {
        let node = &self.terms[term];
        match node[0] {
            0 => Term::Var(self.symbols[node[1] as usize].clone()),
            1 => {
                let index = node[1] as usize;
                let name = if index < binders.len() { binders[binders.len() - index - 1].clone() } else { format!("#{index}") };
                Term::Var(name)
            }
            3 => Term::Nat(BigUint::parse_bytes(self.symbols[node[1] as usize].as_bytes(), 10).expect("natural literal")),
            _ => Term::App(self.symbols[node[1] as usize].clone(), node[2..].iter().map(|x| self.reify_term(*x as usize, binders)).collect()),
        }
    }

    pub fn reify_formula(&self, formula: usize, binders: &mut Vec<String>) -> Formula {
        let node = &self.formulas[formula];
        match node[0] {
            0 => Formula::Bottom,
            1 => Formula::Eq(Box::new(self.reify_term(node[1] as usize, binders)), Box::new(self.reify_term(node[2] as usize, binders))),
            2 => Formula::Pred(self.symbols[node[1] as usize].clone(), node[2..].iter().map(|x| self.reify_term(*x as usize, binders)).collect()),
            3 | 5 | 6 | 7 => {
                let left = Box::new(self.reify_formula(node[1] as usize, binders));
                let right = Box::new(self.reify_formula(node[2] as usize, binders));
                match node[0] {
                    3 => Formula::Imp(left, right),
                    5 => Formula::And(left, right),
                    6 => Formula::Or(left, right),
                    _ => Formula::Iff(left, right),
                }
            }
            _ => {
                let name = format!("x{}", binders.len());
                binders.push(name.clone());
                let body = Box::new(self.reify_formula(node[1] as usize, binders));
                binders.pop();
                if node[0] == 4 { Formula::Forall(name, body) } else { Formula::Exists(name, body) }
            }
        }
    }
}

fn fixed_data(op: u32) -> Option<usize> {
    match op {
        0 | 1 | 2 | 4 | 7 | 8 | 10 | 11 | 17 | 18 | 24 | 25 | 26 => Some(1),
        3 => Some(2),
        5 | 6 | 9 | 14 | 15 | 16 | 19 | 20 | 21 | 22 | 29 => Some(0),
        13 | 23 => Some(3),
        27 => Some(5),
        _ => None,
    }
}

fn expect(arena: &Arena, formula: usize, op: u32, description: &str) -> Result<Vec<u32>> {
    match arena.formulas.get(formula) {
        Some(node) if node[0] == op => Ok(node.clone()),
        _ => fail(format!("{description} received the wrong formula")),
    }
}

fn same_contexts(p: &Program, instruction: &[u32], pc: usize) -> Result<()> {
    let count = instruction[3] as usize;
    for premise in &instruction[4..4 + count] {
        if p.code[*premise as usize][2] != instruction[2] {
            return fail(format!("context mismatch at instruction {pc}"));
        }
    }
    Ok(())
}

fn require_context(arena: &Arena, expected: &[u32], actual: u32, pc: usize) -> Result<()> {
    if arena.contexts[actual as usize] != expected {
        return fail(format!("branch context mismatch at instruction {pc}"));
    }
    Ok(())
}

fn extended(context: &[u32], extra: &[usize]) -> Vec<u32> {
    let mut result = context.to_vec();
    result.extend(extra.iter().map(|x| *x as u32));
    result
}

/// Run the proof machine over a program. Returns the arena and the result
/// formula of every instruction.
pub fn verify(
    p: &Program,
    env: &Environment,
    require_environment: bool,
    boundary_statements: Option<&BTreeMap<String, Formula>>,
) -> Result<(Arena, Vec<usize>)> {
    if require_environment && p.environment != env.digest {
        return fail("proof and environment digests differ");
    }
    let mut arena = Arena::new(p);
    let roots = std::iter::once(p.root).chain(p.theorems.iter().map(|(_, root)| *root));
    for root in roots {
        if root as usize >= p.code.len() || !p.contexts[p.code[root as usize][2] as usize].is_empty() {
            return fail("proof roots and theorem boundaries must have empty contexts");
        }
    }
    for (index, node) in p.terms.iter().enumerate() {
        if node[0] == 2 {
            let name = arena.symbol(node[1])?;
            if env.functions.get(name) != Some(&(node.len() - 2)) {
                return fail(format!("unknown or malformed machine function {name} at term {index}"));
            }
        }
    }
    for (index, node) in p.formulas.iter().enumerate() {
        if node[0] == 2 {
            let name = arena.symbol(node[1])?;
            if env.predicates.get(name) != Some(&(node.len() - 2)) {
                return fail(format!("unknown or malformed machine predicate {name} at formula {index}"));
            }
        }
    }
    let boundary_roots: HashMap<String, usize> = p.theorems.iter().map(|(name, root)| (p.symbols[*name as usize].clone(), *root as usize)).collect();
    let mut results: Vec<usize> = vec![usize::MAX; p.code.len()];
    for (pc, instruction) in p.code.iter().enumerate() {
        let op = instruction[0];
        let claim = instruction[1] as usize;
        let context_id = instruction[2];
        let premise_count = instruction[3] as usize;
        let premises: Vec<usize> = instruction[4..4 + premise_count].iter().map(|x| *x as usize).collect();
        let data: Vec<u32> = instruction[4 + premise_count..].to_vec();
        if let Some(expected) = fixed_data(op) {
            if data.len() != expected {
                return fail(format!("malformed data at instruction {pc}"));
            }
        }
        let context = arena.contexts[context_id as usize].clone();
        let derived: usize = match op {
            0 => {
                if premise_count != 0 || !context.contains(&data[0]) {
                    return fail(format!("inactive assumption at instruction {pc}"));
                }
                data[0] as usize
            }
            1 | 2 | 3 => {
                if premise_count != 0 {
                    return fail(format!("dependency has premises at instruction {pc}"));
                }
                let name = arena.symbol(data[0])?.to_string();
                if op == 2 && boundary_roots.contains_key(&name) {
                    // A theorem proved earlier in this tape, by its boundary.
                    let boundary = boundary_roots[&name];
                    if boundary >= pc {
                        return fail(format!("theorem dependency is not yet proved: {name}"));
                    }
                    results[boundary]
                } else {
                    let formula: Option<Formula> = if op == 1 {
                        env.axioms.get(&name).cloned()
                    } else if op == 3 {
                        let property = arena.symbol(data[1])?.to_string();
                        env.property(&name, &property).cloned()
                    } else {
                        env.theorems.get(&name).cloned()
                    };
                    match formula {
                        Some(formula) => arena.intern_formula(&formula, &mut Vec::new()),
                        None => return fail(format!("unknown machine dependency {name}")),
                    }
                }
            }
            4 => {
                if premise_count != 0 {
                    return fail(format!("reflexivity has premises at instruction {pc}"));
                }
                let conclusion = expect(&arena, claim, 1, "reflexivity")?;
                if conclusion[1..] != [data[0], data[0]] {
                    return fail(format!("bad reflexivity at instruction {pc}"));
                }
                claim
            }
            28 => {
                if premise_count != 0 || data.is_empty() || data.len() != 1 + data[0] as usize {
                    return fail(format!("malformed computation at instruction {pc}"));
                }
                let mut definitions = Vec::with_capacity(data.len() - 1);
                for item in &data[1..] {
                    definitions.push(arena.symbol(*item)?.to_string());
                }
                let node = arena.formulas[claim].clone();
                if node[0] != 1 {
                    return fail("kernel computation requires an equality");
                }
                let left = arena.reify_term(node[1] as usize, &[]);
                let right = arena.reify_term(node[2] as usize, &[]);
                compute::check_computation(env, &left, &right, &definitions, true)?;
                claim
            }
            29 => {
                if premise_count != 0 || !data.is_empty() {
                    return fail(format!("malformed rational computation at instruction {pc}"));
                }
                match arena.reify_formula(claim, &mut Vec::new()) {
                    Formula::Eq(left, right) => compute::check_rational_class_equality(env, &left, &right)?,
                    _ => return fail("rational computation requires equality"),
                }
                claim
            }
            5 => {
                if premise_count != 1 {
                    return fail(format!("bad symmetry premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let equality = expect(&arena, results[premises[0]], 1, "symmetry")?;
                let conclusion = expect(&arena, claim, 1, "symmetry")?;
                if conclusion[1..] != [equality[2], equality[1]] {
                    return fail(format!("bad symmetry at instruction {pc}"));
                }
                claim
            }
            6 => {
                if premise_count != 2 {
                    return fail(format!("bad transitivity premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let left = expect(&arena, results[premises[0]], 1, "transitivity")?;
                let right = expect(&arena, results[premises[1]], 1, "transitivity")?;
                let conclusion = expect(&arena, claim, 1, "transitivity")?;
                if left[2] != right[1] || conclusion[1..] != [left[1], right[2]] {
                    return fail(format!("bad transitivity at instruction {pc}"));
                }
                claim
            }
            7 => {
                same_contexts(p, instruction, pc)?;
                let fn_name = arena.symbol(data[0])?.to_string();
                if env.functions.get(&fn_name) != Some(&premise_count) {
                    return fail(format!("bad congruence arity at instruction {pc}"));
                }
                let mut equalities = Vec::with_capacity(premise_count);
                for premise in &premises {
                    equalities.push(expect(&arena, results[*premise], 1, "congruence")?);
                }
                let left = arena.application(&fn_name, equalities.iter().map(|item| item[1] as usize).collect());
                let right = arena.application(&fn_name, equalities.iter().map(|item| item[2] as usize).collect());
                if expect(&arena, claim, 1, "congruence")?[1..] != [left as u32, right as u32] {
                    return fail(format!("bad congruence at instruction {pc}"));
                }
                claim
            }
            8 => {
                if premise_count != 1 {
                    return fail(format!("bad implication introduction premise count at {pc}"));
                }
                let assumption = data[0] as usize;
                require_context(&arena, &extended(&context, &[assumption]), p.code[premises[0]][2], pc)?;
                let conclusion = expect(&arena, claim, 3, "implication introduction")?;
                if conclusion[1..] != [assumption as u32, results[premises[0]] as u32] {
                    return fail(format!("bad implication introduction at {pc}"));
                }
                claim
            }
            9 => {
                if premise_count != 2 {
                    return fail(format!("bad implication elimination premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let implication = expect(&arena, results[premises[0]], 3, "implication elimination")?;
                if implication[1] as usize != results[premises[1]] || implication[2] as usize != claim {
                    return fail(format!("bad implication elimination at {pc}"));
                }
                claim
            }
            10 => {
                if premise_count != 1 {
                    return fail(format!("bad universal introduction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let symbol = data[0] as usize;
                if context.iter().any(|formula| arena.has_free_formula(*formula as usize, symbol)) {
                    return fail(format!("generalized variable is free in context at {pc}"));
                }
                let body = expect(&arena, claim, 4, "universal introduction")?[1] as usize;
                if body != arena.abstract_formula(results[premises[0]], symbol, 0) {
                    return fail(format!("bad universal introduction at {pc}"));
                }
                claim
            }
            11 => {
                if premise_count != 1 {
                    return fail(format!("bad universal elimination premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let universal = expect(&arena, results[premises[0]], 4, "universal elimination")?;
                if claim != arena.instantiate_formula(universal[1] as usize, data[0] as usize, 0) {
                    return fail(format!("bad universal elimination at {pc}"));
                }
                claim
            }
            13 => {
                if premise_count != 2 || data[2] > 1 {
                    return fail(format!("bad equality elimination data at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let equality = expect(&arena, results[premises[0]], 1, "equality elimination")?;
                let (source, target) = if data[2] == 1 { (equality[2], equality[1]) } else { (equality[1], equality[2]) };
                let evidence = arena.substitute_formula(data[1] as usize, data[0] as usize, source as usize);
                let conclusion = arena.substitute_formula(data[1] as usize, data[0] as usize, target as usize);
                if results[premises[1]] != evidence || claim != conclusion {
                    return fail(format!("bad equality elimination at {pc}"));
                }
                claim
            }
            14 => {
                if premise_count != 2 {
                    return fail(format!("bad conjunction introduction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                if expect(&arena, claim, 5, "conjunction introduction")?[1..] != [results[premises[0]] as u32, results[premises[1]] as u32] {
                    return fail(format!("bad conjunction introduction at {pc}"));
                }
                claim
            }
            15 | 16 => {
                if premise_count != 1 {
                    return fail(format!("bad conjunction elimination premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let conjunction = expect(&arena, results[premises[0]], 5, "conjunction elimination")?;
                if claim as u32 != conjunction[if op == 15 { 1 } else { 2 }] {
                    return fail(format!("bad conjunction elimination at {pc}"));
                }
                claim
            }
            17 | 18 => {
                if premise_count != 1 {
                    return fail(format!("bad disjunction introduction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let conclusion = expect(&arena, claim, 6, "disjunction introduction")?;
                let expected = if op == 17 { [results[premises[0]] as u32, data[0]] } else { [data[0], results[premises[0]] as u32] };
                if conclusion[1..] != expected {
                    return fail(format!("bad disjunction introduction at {pc}"));
                }
                claim
            }
            19 => {
                if premise_count != 3 || p.code[premises[0]][2] != context_id {
                    return fail(format!("bad disjunction elimination context at {pc}"));
                }
                let disjunction = expect(&arena, results[premises[0]], 6, "disjunction elimination")?;
                require_context(&arena, &extended(&context, &[disjunction[1] as usize]), p.code[premises[1]][2], pc)?;
                require_context(&arena, &extended(&context, &[disjunction[2] as usize]), p.code[premises[2]][2], pc)?;
                if results[premises[1]] != results[premises[2]] || claim != results[premises[1]] {
                    return fail(format!("bad disjunction elimination at {pc}"));
                }
                claim
            }
            20 => {
                if premise_count != 2 {
                    return fail(format!("bad equivalence introduction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let forward = expect(&arena, results[premises[0]], 3, "equivalence introduction")?;
                let backward = expect(&arena, results[premises[1]], 3, "equivalence introduction")?;
                let conclusion = expect(&arena, claim, 7, "equivalence introduction")?;
                if forward[1] != backward[2] || forward[2] != backward[1] || conclusion[1..] != forward[1..] {
                    return fail(format!("bad equivalence introduction at {pc}"));
                }
                claim
            }
            21 | 22 => {
                if premise_count != 1 {
                    return fail(format!("bad equivalence elimination premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let equivalence = expect(&arena, results[premises[0]], 7, "equivalence elimination")?;
                let conclusion = expect(&arena, claim, 3, "equivalence elimination")?;
                let expected = if op == 22 { [equivalence[2], equivalence[1]] } else { [equivalence[1], equivalence[2]] };
                if conclusion[1..] != expected {
                    return fail(format!("bad equivalence elimination at {pc}"));
                }
                claim
            }
            23 => {
                if premise_count != 1 {
                    return fail(format!("bad existential introduction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let body = expect(&arena, claim, 8, "existential introduction")?[1] as usize;
                let abstracted = arena.abstract_formula(data[1] as usize, data[0] as usize, 0);
                let instance = arena.substitute_formula(data[1] as usize, data[0] as usize, data[2] as usize);
                if body != abstracted || results[premises[0]] != instance {
                    return fail(format!("bad existential introduction at {pc}"));
                }
                claim
            }
            24 => {
                if premise_count != 2 || p.code[premises[0]][2] != context_id {
                    return fail(format!("bad existential elimination context at {pc}"));
                }
                let existential = expect(&arena, results[premises[0]], 8, "existential elimination")?;
                let witness = data[0] as usize;
                if context.iter().any(|formula| arena.has_free_formula(*formula as usize, witness))
                    || arena.has_free_formula(results[premises[0]], witness)
                {
                    return fail(format!("existential witness is not fresh at {pc}"));
                }
                let witness_term = arena.term_node(vec![0, witness as u32]);
                let instance = arena.instantiate_formula(existential[1] as usize, witness_term, 0);
                require_context(&arena, &extended(&context, &[instance]), p.code[premises[1]][2], pc)?;
                if arena.has_free_formula(results[premises[1]], witness) || claim != results[premises[1]] {
                    return fail(format!("existential witness escapes at {pc}"));
                }
                claim
            }
            25 => {
                if premise_count != 1 {
                    return fail(format!("bad false elimination premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                expect(&arena, results[premises[0]], 0, "false elimination")?;
                if claim as u32 != data[0] {
                    return fail(format!("bad false elimination at {pc}"));
                }
                claim
            }
            26 => {
                if premise_count != 1 {
                    return fail(format!("bad DNE premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let bottom = arena.formula_node(vec![0]) as u32;
                let negated = arena.formula_node(vec![3, data[0], bottom]) as u32;
                let double = arena.formula_node(vec![3, negated, bottom]);
                if results[premises[0]] != double || claim as u32 != data[0] {
                    return fail(format!("bad double-negation elimination at {pc}"));
                }
                claim
            }
            12 => {
                if data.len() < 4 {
                    return fail(format!("malformed induction at {pc}"));
                }
                let datatype_name = arena.symbol(data[0])?.to_string();
                let datatype = env.datatypes.get(&datatype_name);
                let variable = data[1] as usize;
                let motive = data[2] as usize;
                let parameter_count = data[3] as usize;
                if 4 + parameter_count >= data.len() {
                    return fail(format!("truncated induction parameters at {pc}"));
                }
                let parameters: Vec<usize> = data[4..4 + parameter_count].iter().map(|x| *x as usize).collect();
                if parameters.iter().any(|parameter| *parameter >= arena.terms.len()) {
                    return fail(format!("invalid induction parameter at {pc}"));
                }
                let case_count = data[4 + parameter_count] as usize;
                let datatype = match datatype {
                    Some(datatype)
                        if parameter_count == datatype.parameters.len()
                            && case_count == datatype.constructors.len()
                            && premise_count == case_count =>
                    {
                        datatype
                    }
                    _ => return fail(format!("malformed induction at {pc}")),
                };
                if parameters.iter().any(|parameter| arena.has_free_term(*parameter, variable)) {
                    return fail(format!("induction variable occurs in a datatype parameter at {pc}"));
                }
                if context.iter().any(|formula| arena.has_free_formula(*formula as usize, variable)) {
                    return fail(format!("induction variable is free in context at {pc}"));
                }
                let mut cursor = 5 + parameter_count;
                let mut seen: std::collections::HashSet<String> = std::collections::HashSet::new();
                for index in 0..case_count {
                    if cursor + 2 > data.len() {
                        return fail(format!("truncated induction case at {pc}"));
                    }
                    let constructor_name = arena.symbol(data[cursor])?.to_string();
                    let field_count = data[cursor + 1] as usize;
                    cursor += 2;
                    if cursor + field_count > data.len() {
                        return fail(format!("truncated induction case at {pc}"));
                    }
                    let fields: Vec<usize> = data[cursor..cursor + field_count].iter().map(|x| *x as usize).collect();
                    cursor += field_count;
                    let constructor = datatype.constructors.iter().find(|item| item.name == constructor_name);
                    let distinct: std::collections::HashSet<usize> = fields.iter().copied().collect();
                    let constructor = match constructor {
                        Some(constructor) if constructor.arity == field_count && !seen.contains(&constructor_name) && distinct.len() == fields.len() => constructor,
                        _ => return fail(format!("malformed induction case at {pc}")),
                    };
                    seen.insert(constructor_name.clone());
                    if fields.iter().any(|field| {
                        *field == variable
                            || arena.has_free_formula(motive, *field)
                            || parameters.iter().any(|parameter| arena.has_free_term(*parameter, *field))
                            || context.iter().any(|formula| arena.has_free_formula(*formula as usize, *field))
                    }) {
                        return fail(format!("induction field is not fresh at {pc}"));
                    }
                    let field_terms: Vec<usize> = fields.iter().map(|field| arena.term_node(vec![0, *field as u32])).collect();
                    let mut expected_context = context.clone();
                    for field_index in 0..constructor.arity {
                        if constructor.recursive_fields.contains(&field_index) {
                            let mut args = parameters.clone();
                            args.push(field_terms[field_index]);
                            let membership = arena.predicate(&datatype.predicate, args) as u32;
                            expected_context.push(membership);
                            let hypothesis = arena.substitute_formula(motive, variable, field_terms[field_index]) as u32;
                            expected_context.push(hypothesis);
                        } else if let Some((_, parameter)) = constructor.parameter_fields.iter().find(|(field, _)| *field == field_index) {
                            let carrier = arena.predicate("in", vec![field_terms[field_index], parameters[*parameter]]) as u32;
                            expected_context.push(carrier);
                        }
                    }
                    require_context(&arena, &expected_context, p.code[premises[index]][2], pc)?;
                    let constructor_term = arena.application(&constructor_name, field_terms.clone());
                    if results[premises[index]] != arena.substitute_formula(motive, variable, constructor_term) {
                        return fail(format!("wrong induction case at {pc}"));
                    }
                }
                if cursor != data.len() || seen.len() != case_count {
                    return fail(format!("malformed induction data at {pc}"));
                }
                let variable_term = arena.term_node(vec![0, variable as u32]);
                let mut args = parameters.clone();
                args.push(variable_term);
                let membership = arena.predicate(&datatype.predicate, args) as u32;
                let body = arena.formula_node(vec![3, membership, motive as u32]);
                let abstracted = arena.abstract_formula(body, variable, 0) as u32;
                arena.formula_node(vec![4, abstracted])
            }
            27 => {
                if premise_count != 2 {
                    return fail(format!("bad well-founded induction premise count at {pc}"));
                }
                same_contexts(p, instruction, pc)?;
                let (relation, domain, variable, predecessor, motive) =
                    (data[0] as usize, data[1] as usize, data[2] as usize, data[3] as usize, data[4] as usize);
                if variable == predecessor
                    || arena.has_free_term(relation, variable)
                    || arena.has_free_term(relation, predecessor)
                    || arena.has_free_term(domain, variable)
                    || arena.has_free_term(domain, predecessor)
                    || arena.has_free_formula(motive, predecessor)
                    || context.iter().any(|formula| {
                        arena.has_free_formula(*formula as usize, variable) || arena.has_free_formula(*formula as usize, predecessor)
                    })
                {
                    return fail(format!("malformed well-founded induction variables at {pc}"));
                }
                let well_founded = arena.predicate("wellFoundedOn", vec![relation, domain]);
                if results[premises[0]] != well_founded {
                    return fail(format!("wrong well-foundedness certificate at {pc}"));
                }
                let x = arena.term_node(vec![0, variable as u32]);
                let y = arena.term_node(vec![0, predecessor as u32]);
                let predecessor_motive = arena.substitute_formula(motive, variable, y) as u32;
                let y_in_domain = arena.predicate("in", vec![y, domain]) as u32;
                let relates = arena.predicate("relates", vec![relation, y, x]) as u32;
                let conjunction = arena.formula_node(vec![5, y_in_domain, relates]) as u32;
                let ih_body = arena.formula_node(vec![3, conjunction, predecessor_motive]);
                let ih_abstracted = arena.abstract_formula(ih_body, predecessor, 0) as u32;
                let ih = arena.formula_node(vec![4, ih_abstracted]) as u32;
                let in_domain = arena.predicate("in", vec![x, domain]) as u32;
                let inner = arena.formula_node(vec![3, ih, motive as u32]) as u32;
                let step_body = arena.formula_node(vec![3, in_domain, inner]);
                let step_abstracted = arena.abstract_formula(step_body, variable, 0) as u32;
                let expected_step = arena.formula_node(vec![4, step_abstracted]);
                if results[premises[1]] != expected_step {
                    return fail(format!("wrong well-founded induction step at {pc}"));
                }
                let result_body = arena.formula_node(vec![3, in_domain, motive as u32]);
                let result_abstracted = arena.abstract_formula(result_body, variable, 0) as u32;
                arena.formula_node(vec![4, result_abstracted])
            }
            _ => return fail(format!("unsupported proof opcode {op} at {pc}")),
        };
        if derived != claim {
            return fail(format!("instruction {pc} derives the wrong formula"));
        }
        results[pc] = derived;
    }
    for (name_id, root) in &p.theorems {
        let name = arena.symbol(*name_id)?.to_string();
        let statement = match boundary_statements {
            Some(statements) => statements.get(&name),
            None => env.theorems.get(&name),
        };
        let interned = match statement {
            Some(statement) => arena.intern_formula(statement, &mut Vec::new()),
            None => return fail(format!("theorem boundary mismatch: {name}")),
        };
        if results[*root as usize] != interned {
            return fail(format!("theorem boundary mismatch: {name}"));
        }
    }
    Ok((arena, results))
}
