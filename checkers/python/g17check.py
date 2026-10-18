#!/usr/bin/env python3
# Independent, dependency-free checker for G17M proof tapes.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Independent, dependency-free checker for GRACE17 G17M version 4 files."""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any

MAGIC = b"G17M"
VERSION = 4
DIGEST_BYTES = 32
MAX_COUNT = 10_000_000
MAX_VECTOR = 1_000_000
# Steps of ground evaluation one computation instruction may spend; `--fuel` sets it.
FUEL = 1_000_000
NAT = re.compile(r"(?:0|[1-9][0-9]*)\Z")


class CheckError(Exception):
    pass


def fail(message: str) -> None:
    raise CheckError(message)


def utf16_key(value: str) -> bytes:
    return value.encode("utf-16-be", "surrogatepass")


def canonical(value: Any) -> str:
    """The tiny canonical JSON function used by the TypeScript kernel."""
    if value is None:
        return "null"
    if value is True:
        return "true"
    if value is False:
        return "false"
    if isinstance(value, str):
        return json.dumps(value, ensure_ascii=False, separators=(",", ":"))
    if isinstance(value, int):
        return str(value)
    if isinstance(value, list):
        return "[" + ",".join(canonical(item) for item in value) + "]"
    if isinstance(value, dict):
        keys = sorted(value, key=utf16_key)
        return "{" + ",".join(
            json.dumps(key, ensure_ascii=False) + ":" + canonical(value[key]) for key in keys
        ) + "}"
    fail(f"environment contains unsupported value {type(value).__name__}")


class Reader:
    def __init__(self, data: bytes):
        self.data = data
        self.offset = 0

    def byte(self) -> int:
        if self.offset >= len(self.data):
            fail("truncated G17M data")
        result = self.data[self.offset]
        self.offset += 1
        return result

    def bytes(self, count: int) -> bytes:
        end = self.offset + count
        if end > len(self.data):
            fail("truncated G17M data")
        result = self.data[self.offset:end]
        self.offset = end
        return result

    def uint(self) -> int:
        value = 0
        factor = 1
        count = 0
        while True:
            chunk = self.byte()
            count += 1
            if count > 5:
                fail("oversized G17M integer")
            value += (chunk & 0x7F) * factor
            factor *= 128
            if not chunk & 0x80:
                break
        if (count > 1 and chunk & 0x7F == 0) or value > 0xFFFF_FFFF:
            fail("noncanonical G17M integer")
        return value

    def count(self, name: str, limit: int = MAX_COUNT) -> int:
        result = self.uint()
        if result > limit:
            fail(f"too many G17M {name}")
        return result

    def string(self) -> str:
        raw = self.bytes(self.count("string bytes", MAX_VECTOR))
        try:
            value = raw.decode("utf-8", "strict")
        except UnicodeDecodeError as error:
            raise CheckError("noncanonical G17M UTF-8") from error
        if value.encode("utf-8") != raw:
            fail("noncanonical G17M UTF-8")
        return value


@dataclass
class Program:
    environment: str
    symbols: list[str]
    terms: list[list[int]]
    formulas: list[list[int]]
    contexts: list[list[int]]
    code: list[list[int]]
    root: int
    theorems: list[list[int]]


def read_vectors(reader: Reader, name: str) -> list[list[int]]:
    return [
        [reader.uint() for _ in range(reader.count(f"{name}[{index}] words", MAX_VECTOR))]
        for index in range(reader.count(name))
    ]


def decode(path: Path) -> Program:
    data = path.read_bytes()
    if len(data) < 4 + 2 + 32 + DIGEST_BYTES:
        fail("truncated G17M certificate")
    body, supplied = data[:-DIGEST_BYTES], data[-DIGEST_BYTES:]
    if hashlib.sha256(body).digest() != supplied:
        fail("corrupted G17M certificate digest")
    reader = Reader(body)
    if reader.bytes(4) != MAGIC:
        fail("bad G17M magic")
    if reader.byte() != VERSION:
        fail("unsupported G17M version")
    flags = reader.byte()
    if flags not in (0, 1):
        fail("unsupported G17M flags")
    environment = reader.bytes(32).hex()
    symbols = [reader.string() for _ in range(reader.count("symbols"))]
    terms = read_vectors(reader, "terms")
    formulas = read_vectors(reader, "formulas")
    contexts = read_vectors(reader, "contexts")
    code = read_vectors(reader, "instructions")
    root = reader.uint()
    theorems = [[reader.uint(), reader.uint()] for _ in range(reader.count("theorems"))]
    if reader.offset != len(body):
        fail("trailing G17M data")
    if (flags == 0) != (len(theorems) == 0):
        fail("G17M theorem-boundary flag mismatch")
    result = Program(environment, symbols, terms, formulas, contexts, code, root, theorems)
    validate_program(result)
    return result


def validate_program(p: Program) -> None:
    if len(set(p.symbols)) != len(p.symbols) or any(not symbol for symbol in p.symbols):
        fail("empty or duplicate G17M symbol")
    seen: set[tuple[int, ...]] = set()
    for index, node in enumerate(p.terms):
        if len(node) < 2:
            fail(f"malformed G17M term {index}")
        op = node[0]
        if op == 0 and (len(node) != 2 or node[1] >= len(p.symbols)):
            fail(f"malformed G17M free variable {index}")
        elif op == 1 and len(node) != 2:
            fail(f"malformed G17M bound variable {index}")
        elif op == 2 and (node[1] >= len(p.symbols) or any(child >= index for child in node[2:])):
            fail(f"malformed G17M application {index}")
        elif op == 3 and (len(node) != 2 or node[1] >= len(p.symbols) or not NAT.fullmatch(p.symbols[node[1]])):
            fail(f"malformed G17M natural {index}")
        elif op > 3:
            fail(f"unknown G17M term opcode {op}")
        key = tuple(node)
        if key in seen:
            fail(f"duplicate G17M term {index}")
        seen.add(key)
    seen.clear()
    for index, node in enumerate(p.formulas):
        if not node:
            fail(f"malformed G17M formula {index}")
        op = node[0]
        if op == 0 and len(node) != 1:
            fail(f"malformed G17M bottom {index}")
        elif op == 1 and (len(node) != 3 or max(node[1:]) >= len(p.terms)):
            fail(f"malformed G17M equality {index}")
        elif op == 2 and (len(node) < 2 or node[1] >= len(p.symbols) or any(x >= len(p.terms) for x in node[2:])):
            fail(f"malformed G17M predicate {index}")
        elif op in (3, 5, 6, 7) and (len(node) != 3 or node[1] >= index or node[2] >= index):
            fail(f"malformed G17M binary formula {index}")
        elif op in (4, 8) and (len(node) != 2 or node[1] >= index):
            fail(f"malformed G17M quantifier {index}")
        elif op > 8:
            fail(f"unknown G17M formula opcode {op}")
        key = tuple(node)
        if key in seen:
            fail(f"duplicate G17M formula {index}")
        seen.add(key)
    seen.clear()
    for index, context in enumerate(p.contexts):
        if len(context) > MAX_VECTOR or any(x >= len(p.formulas) for x in context):
            fail(f"malformed G17M context {index}")
        key = tuple(context)
        if key in seen:
            fail(f"duplicate G17M context {index}")
        seen.add(key)
    for pc, instruction in enumerate(p.code):
        if len(instruction) < 4 or len(instruction) > MAX_VECTOR:
            fail(f"malformed G17M instruction {pc}")
        op, claim, context, premises = instruction[:4]
        if op > 29 or claim >= len(p.formulas) or context >= len(p.contexts) or premises > len(instruction) - 4:
            fail(f"invalid G17M instruction {pc}")
        if any(premise >= pc for premise in instruction[4:4 + premises]):
            fail(f"forward premise at G17M instruction {pc}")
    if p.root >= len(p.code):
        fail("invalid G17M root")
    names: set[int] = set()
    for boundary in p.theorems:
        if len(boundary) != 2 or boundary[0] >= len(p.symbols) or boundary[1] >= len(p.code) or boundary[0] in names:
            fail("malformed G17M theorem boundary")
        names.add(boundary[0])


class Environment:
    def __init__(self, path: Path):
        document = json.loads(path.read_text("utf-8"))
        if document.get("format") != "grace17.environment" or document.get("version") != 1:
            fail("unsupported GRACE17 environment")
        snapshot = document.get("kernel")
        actual = hashlib.sha256(canonical(snapshot).encode("utf-8")).hexdigest()
        if document.get("digest") != actual:
            fail("environment digest mismatch")
        self.capabilities = dict(snapshot["capabilities"])
        self.digest = actual
        self.functions = dict(snapshot["functions"])
        self.predicates = dict(snapshot["predicates"])
        self.axioms = dict(snapshot["axioms"])
        self.theorems = dict(snapshot["theorems"])
        self.definitions = {name: value for name, value in snapshot["definitions"]}
        self.datatypes = {name: value for name, value in snapshot["datatypes"]}
        self.recursive = {name: value for name, value in snapshot["recursiveFunctions"]}
        self.bodies = {name: value for name, value in snapshot["functionBodies"]}

    @classmethod
    def from_document(cls, document: dict[str, Any]) -> "Environment":
        result = cls.__new__(cls)
        if document.get("format") != "grace17.environment" or document.get("version") != 1:
            fail("unsupported GRACE17 environment")
        snapshot = document.get("kernel")
        actual = hashlib.sha256(canonical(snapshot).encode("utf-8")).hexdigest()
        if document.get("digest") != actual:
            fail("environment digest mismatch")
        result.capabilities = dict(snapshot["capabilities"])
        result.digest = actual
        result.functions = dict(snapshot["functions"])
        result.predicates = dict(snapshot["predicates"])
        result.axioms = dict(snapshot["axioms"])
        result.theorems = dict(snapshot["theorems"])
        result.definitions = {name: value for name, value in snapshot["definitions"]}
        result.datatypes = {name: value for name, value in snapshot["datatypes"]}
        result.recursive = {name: value for name, value in snapshot["recursiveFunctions"]}
        result.bodies = {name: value for name, value in snapshot["functionBodies"]}
        return result

    def snapshot(self) -> dict[str, Any]:
        ordered_code = lambda values: [[name, item] for name, item in sorted(values.items(), key=lambda pair: utf16_key(pair[0]))]
        definitions = []
        for name, item in ordered_code(self.definitions):
            definitions.append([name, {
                "kind": item["kind"],
                "parameters": item["parameters"],
                "properties": ordered_code(dict(item["properties"])),
            }])
        return {
            "capabilities": self.capabilities,
            "functions": ordered_code(self.functions),
            "predicates": ordered_code(self.predicates),
            "axioms": ordered_code(self.axioms),
            "theorems": ordered_code(self.theorems),
            "definitions": definitions,
            "datatypes": ordered_code(self.datatypes),
            "recursiveFunctions": ordered_code(self.recursive),
            "functionBodies": ordered_code(self.bodies),
        }

    def refresh_digest(self) -> str:
        self.digest = hashlib.sha256(canonical(self.snapshot()).encode("utf-8")).hexdigest()
        return self.digest

    def property(self, name: str, prop: str) -> dict[str, Any] | None:
        definition = self.definitions.get(name)
        return None if definition is None else dict(definition["properties"]).get(prop)


class Arena:
    def __init__(self, p: Program):
        self.symbols = list(p.symbols)
        self.terms = [list(node) for node in p.terms]
        self.formulas = [list(node) for node in p.formulas]
        self.contexts = [list(node) for node in p.contexts]
        self.symbol_map = {value: index for index, value in enumerate(self.symbols)}
        self.term_map = {tuple(node): index for index, node in enumerate(self.terms)}
        self.formula_map = {tuple(node): index for index, node in enumerate(self.formulas)}
        self.context_map = {tuple(node): index for index, node in enumerate(self.contexts)}
        self.abstract_cache: dict[tuple[int, int, int], int] = {}
        self.substitution_cache: dict[tuple[int, int, int], int] = {}
        self.instantiate_cache: dict[tuple[int, int, int], int] = {}

    def symbol(self, index: int) -> str:
        if index < 0 or index >= len(self.symbols):
            fail(f"invalid machine symbol {index}")
        return self.symbols[index]

    def symbol_id(self, value: str) -> int:
        if value not in self.symbol_map:
            self.symbol_map[value] = len(self.symbols)
            self.symbols.append(value)
        return self.symbol_map[value]

    @staticmethod
    def _intern(node: list[int], nodes: list[list[int]], index: dict[tuple[int, ...], int]) -> int:
        key = tuple(node)
        if key not in index:
            index[key] = len(nodes)
            nodes.append(node)
        return index[key]

    def term_node(self, node: list[int]) -> int:
        return self._intern(node, self.terms, self.term_map)

    def formula_node(self, node: list[int]) -> int:
        return self._intern(node, self.formulas, self.formula_map)

    def application_symbol(self, fn: int, args: list[int]) -> int:
        name = self.symbol(fn)
        if name == "zero" and not args:
            return self.term_node([3, self.symbol_id("0")])
        if name == "succ" and len(args) == 1 and self.terms[args[0]][0] == 3:
            value = int(self.symbol(self.terms[args[0]][1])) + 1
            return self.term_node([3, self.symbol_id(str(value))])
        return self.term_node([2, fn, *args])

    def application(self, fn: str, args: list[int]) -> int:
        return self.application_symbol(self.symbol_id(fn), args)

    def predicate(self, pred: str, args: list[int]) -> int:
        return self.formula_node([2, self.symbol_id(pred), *args])

    def intern_term(self, term: dict[str, Any], binders: tuple[str, ...] = ()) -> int:
        number = natural_ast(term)
        if number is not None:
            return self.term_node([3, self.symbol_id(str(number))])
        if term["tag"] == "var":
            if term["name"] in binders:
                reverse = binders[::-1].index(term["name"])
                return self.term_node([1, reverse])
            return self.term_node([0, self.symbol_id(term["name"])])
        return self.application(term["fn"], [self.intern_term(arg, binders) for arg in term["args"]])

    def intern_formula(self, formula: dict[str, Any], binders: tuple[str, ...] = ()) -> int:
        tag = formula["tag"]
        if tag == "bottom":
            return self.formula_node([0])
        if tag == "eq":
            return self.formula_node([1, self.intern_term(formula["left"], binders), self.intern_term(formula["right"], binders)])
        if tag == "pred":
            return self.formula_node([2, self.symbol_id(formula["pred"]), *[self.intern_term(x, binders) for x in formula["args"]]])
        if tag in ("imp", "and", "or", "iff"):
            op = {"imp": 3, "and": 5, "or": 6, "iff": 7}[tag]
            return self.formula_node([op, self.intern_formula(formula["left"], binders), self.intern_formula(formula["right"], binders)])
        op = 4 if tag == "forall" else 8
        return self.formula_node([op, self.intern_formula(formula["body"], (*binders, formula["variable"]))])

    def abstract_term(self, term: int, symbol: int, depth: int) -> int:
        node = self.terms[term]
        if node[0] == 0 and node[1] == symbol:
            return self.term_node([1, depth])
        if node[0] != 2:
            return term
        return self.application_symbol(node[1], [self.abstract_term(x, symbol, depth) for x in node[2:]])

    def abstract_formula(self, formula: int, symbol: int, depth: int = 0) -> int:
        key = (formula, symbol, depth)
        if key in self.abstract_cache:
            return self.abstract_cache[key]
        node = self.formulas[formula]
        if node[0] == 0:
            result = formula
        elif node[0] == 1:
            result = self.formula_node([1, self.abstract_term(node[1], symbol, depth), self.abstract_term(node[2], symbol, depth)])
        elif node[0] == 2:
            result = self.formula_node([2, node[1], *[self.abstract_term(x, symbol, depth) for x in node[2:]]])
        elif node[0] in (3, 5, 6, 7):
            result = self.formula_node([node[0], self.abstract_formula(node[1], symbol, depth), self.abstract_formula(node[2], symbol, depth)])
        else:
            result = self.formula_node([node[0], self.abstract_formula(node[1], symbol, depth + 1)])
        self.abstract_cache[key] = result
        return result

    def matches_abstraction(self, target: int, source: int, symbol: int, depth: int = 0) -> bool:
        return target == self.abstract_formula(source, symbol, depth)

    def substitute_term(self, term: int, symbol: int, replacement: int) -> int:
        node = self.terms[term]
        if node[0] == 0 and node[1] == symbol:
            return replacement
        if node[0] != 2:
            return term
        return self.application_symbol(node[1], [self.substitute_term(x, symbol, replacement) for x in node[2:]])

    def substitute_formula(self, formula: int, symbol: int, replacement: int) -> int:
        key = (formula, symbol, replacement)
        if key in self.substitution_cache:
            return self.substitution_cache[key]
        node = self.formulas[formula]
        if node[0] == 0:
            result = formula
        elif node[0] == 1:
            result = self.formula_node([1, self.substitute_term(node[1], symbol, replacement), self.substitute_term(node[2], symbol, replacement)])
        elif node[0] == 2:
            result = self.formula_node([2, node[1], *[self.substitute_term(x, symbol, replacement) for x in node[2:]]])
        elif node[0] in (3, 5, 6, 7):
            result = self.formula_node([node[0], self.substitute_formula(node[1], symbol, replacement), self.substitute_formula(node[2], symbol, replacement)])
        else:
            result = self.formula_node([node[0], self.substitute_formula(node[1], symbol, replacement)])
        self.substitution_cache[key] = result
        return result

    def shift_term(self, term: int, amount: int) -> int:
        if amount == 0:
            return term
        node = self.terms[term]
        if node[0] == 1:
            return self.term_node([1, node[1] + amount])
        if node[0] != 2:
            return term
        return self.application_symbol(node[1], [self.shift_term(x, amount) for x in node[2:]])

    def instantiate_term(self, term: int, replacement: int, depth: int) -> int:
        node = self.terms[term]
        if node[0] == 1:
            if node[1] == depth:
                return self.shift_term(replacement, depth)
            return self.term_node([1, node[1] - 1]) if node[1] > depth else term
        if node[0] != 2:
            return term
        return self.application_symbol(node[1], [self.instantiate_term(x, replacement, depth) for x in node[2:]])

    def instantiate_formula(self, formula: int, replacement: int, depth: int = 0) -> int:
        key = (formula, replacement, depth)
        if key in self.instantiate_cache:
            return self.instantiate_cache[key]
        node = self.formulas[formula]
        if node[0] == 0:
            result = formula
        elif node[0] == 1:
            result = self.formula_node([1, self.instantiate_term(node[1], replacement, depth), self.instantiate_term(node[2], replacement, depth)])
        elif node[0] == 2:
            result = self.formula_node([2, node[1], *[self.instantiate_term(x, replacement, depth) for x in node[2:]]])
        elif node[0] in (3, 5, 6, 7):
            result = self.formula_node([node[0], self.instantiate_formula(node[1], replacement, depth), self.instantiate_formula(node[2], replacement, depth)])
        else:
            result = self.formula_node([node[0], self.instantiate_formula(node[1], replacement, depth + 1)])
        self.instantiate_cache[key] = result
        return result

    def has_free_term(self, term: int, symbol: int) -> bool:
        node = self.terms[term]
        return node[0] == 0 and node[1] == symbol or node[0] == 2 and any(self.has_free_term(x, symbol) for x in node[2:])

    def has_free_formula(self, formula: int, symbol: int) -> bool:
        node = self.formulas[formula]
        if node[0] == 1:
            return self.has_free_term(node[1], symbol) or self.has_free_term(node[2], symbol)
        if node[0] == 2:
            return any(self.has_free_term(x, symbol) for x in node[2:])
        if node[0] in (3, 5, 6, 7):
            return self.has_free_formula(node[1], symbol) or self.has_free_formula(node[2], symbol)
        return node[0] in (4, 8) and self.has_free_formula(node[1], symbol)

    def reify_term(self, term: int, binders: tuple[str, ...] = ()) -> dict[str, Any]:
        node = self.terms[term]
        if node[0] == 0:
            return {"tag": "var", "name": self.symbol(node[1])}
        if node[0] == 1:
            name = binders[-node[1] - 1] if node[1] < len(binders) else f"#{node[1]}"
            return {"tag": "var", "name": name}
        if node[0] == 3:
            return {"tag": "nat", "value": self.symbol(node[1])}
        return {"tag": "app", "fn": self.symbol(node[1]), "args": [self.reify_term(x, binders) for x in node[2:]]}

    def reify_formula(self, formula: int, binders: tuple[str, ...] = ()) -> dict[str, Any]:
        node = self.formulas[formula]
        if node[0] == 0:
            return {"tag": "bottom"}
        if node[0] == 1:
            return {"tag": "eq", "left": self.reify_term(node[1], binders), "right": self.reify_term(node[2], binders)}
        if node[0] == 2:
            return {"tag": "pred", "pred": self.symbol(node[1]), "args": [self.reify_term(x, binders) for x in node[2:]]}
        if node[0] in (3, 5, 6, 7):
            tag = {3: "imp", 5: "and", 6: "or", 7: "iff"}[node[0]]
            return {"tag": tag, "left": self.reify_formula(node[1], binders), "right": self.reify_formula(node[2], binders)}
        name = f"x{len(binders)}"
        return {"tag": "forall" if node[0] == 4 else "exists", "variable": name, "body": self.reify_formula(node[1], (*binders, name))}


def natural_ast(term: dict[str, Any]) -> int | None:
    if term.get("tag") == "nat" and NAT.fullmatch(term.get("value", "")):
        return int(term["value"])
    value = 0
    cursor = term
    while cursor.get("tag") == "app" and cursor.get("fn") == "succ" and len(cursor.get("args", [])) == 1:
        value += 1
        cursor = cursor["args"][0]
    if cursor.get("tag") == "nat" and NAT.fullmatch(cursor.get("value", "")):
        return value + int(cursor["value"])
    if cursor.get("tag") == "app" and cursor.get("fn") == "zero" and cursor.get("args") == []:
        return value
    return None


Value = int | tuple[str, tuple["Value", ...]]


NAT_MOD = "Grace.Cumulus.Nat.Mod."
NAT_REC = "Grace.Core.Nat.Rec."
BOOL_OPS = "Grace.Core.Data.BoolOps."
BOOL = "Grace.Core.Data.Bool."
RAT_OPS = "Grace.Cumulus.Rat.Computable.RationalCellOps."
NAT_SUB = "Grace.Cumulus.Nat.Subtraction."
NAT_DIV = "Grace.Cumulus.Nat.Division."


def exact_equations(env: Environment, fn: str, params: list[str], equations: list[dict[str, Any]],
                    decreasing: int = 0) -> bool:
    """A structural recursion admitted with exactly these parameters and equations."""
    record = env.recursive.get(fn)
    return record is not None and record.get("admission") == "structural" and \
        record["decreasingParameter"] == decreasing and record["parameters"] == params and \
        record["equations"] == equations


def exact_body(env: Environment, fn: str, params: list[str], body: dict[str, Any]) -> bool:
    """An explicit (non-recursive) definition admitted with exactly this body."""
    record = env.bodies.get(fn)
    return record is not None and record.get("parameters") == params and record.get("body") == body


def decision_equations(env: Environment, name: str, allowed: set[str]) -> tuple[str, tuple[str, ...]] | None:
    decision = {NAT_MOD + "equalNat": "equal", RAT_OPS + "less": "less",
                RAT_OPS + "minus": "minus"}.get(name)
    if decision is None: return None
    shared = [NAT_MOD + "isZero", NAT_REC + "predecessor"]
    dependencies = (shared + [NAT_MOD + "chooseNat", RAT_OPS + "minus"] if decision == "minus" else
                    shared + [BOOL_OPS + "not", BOOL_OPS + "and", name])
    if not set(dependencies) <= allowed: return None
    var = lambda n: {"tag": "var", "name": n}
    app = lambda n, *args: {"tag": "app", "fn": n, "args": list(args)}
    bind = lambda n: {"tag": "bind", "name": n}
    ctor = lambda n, *args: {"tag": "ctor", "name": n, "args": list(args)}
    eq = lambda patterns, body: {"patterns": patterns, "body": body}
    zero = ctor("zero")
    succ = lambda n: ctor("succ", bind(n))
    is_zero = lambda n: app(NAT_MOD + "isZero", var(n))
    pred = lambda n: app(NAT_REC + "predecessor", var(n))
    nonzero = lambda n: app(BOOL_OPS + "not", is_zero(n))

    def exact(fn: str, params: list[str], equations: list[dict[str, Any]]) -> bool:
        return exact_equations(env, fn, params, equations)

    helpers = exact(NAT_MOD + "isZero", ["n"], [
        eq([zero], app(BOOL + "true")), eq([succ("n")], app(BOOL + "false"))]) and \
        exact(NAT_REC + "predecessor", ["n"], [
            eq([zero], app("zero")), eq([succ("n")], var("n"))])
    if decision == "minus":
        logical = exact(NAT_MOD + "chooseNat", ["condition", "yes", "no"], [
            eq([ctor(BOOL + "false"), bind("yes"), bind("no")], var("no")),
            eq([ctor(BOOL + "true"), bind("yes"), bind("no")], var("yes"))])
    else:
        logical = exact(BOOL_OPS + "not", ["b"], [
            eq([ctor(BOOL + "false")], app(BOOL + "true")),
            eq([ctor(BOOL + "true")], app(BOOL + "false"))]) and \
            exact(BOOL_OPS + "and", ["a", "b"], [
                eq([ctor(BOOL + "false"), bind("b")], app(BOOL + "false")),
                eq([ctor(BOOL + "true"), bind("b")], var("b"))])
    first, other = ("m", "n") if decision == "equal" else ("a", "b")
    base = ({"tag": "nat", "value": "0"} if decision == "minus" else
            is_zero(other) if decision == "equal" else nonzero(other))
    recurse = app(name, var(first), pred(other))
    step = (app(NAT_MOD + "chooseNat", is_zero(other), app("succ", var(first)), recurse)
            if decision == "minus" else app(BOOL_OPS + "and", nonzero(other), recurse))
    if helpers and logical and exact(name, [first, other], [
        eq([zero, bind(other)], base), eq([succ(first), bind(other)], step)]):
        return decision, tuple(dependencies)
    return None


# The remainder's fixed dependency list: its own equations, the helper
# equations, and the equality decision with the helpers that one names.
MOD_DEFINITIONS = (NAT_MOD + "mod", NAT_MOD + "nextRemainder", NAT_MOD + "chooseNat", NAT_MOD + "equalNat",
                   NAT_MOD + "isZero", NAT_REC + "predecessor", BOOL_OPS + "not", BOOL_OPS + "and")


def shortcut_equations(env: Environment, name: str, allowed: set[str]) -> tuple[str, tuple[str, ...]] | None:
    """The descent-by-ones natural operators (predecessor, truncated subtraction,
    remainder, quotient) recognized exactly from their admitted equations and
    helper equations, each with a fixed dependency list recorded whatever the
    arguments are."""
    shortcut = {NAT_REC + "predecessor": "predecessor", NAT_SUB + "sub": "sub",
                NAT_MOD + "mod": "mod", NAT_DIV + "quotientNat": "quotient"}.get(name)
    if shortcut is None: return None
    dependencies = {"predecessor": (NAT_REC + "predecessor",),
                    "sub": (NAT_SUB + "sub", NAT_REC + "predecessor"),
                    "mod": MOD_DEFINITIONS,
                    "quotient": (NAT_DIV + "quotientNat", *MOD_DEFINITIONS)}[shortcut]
    if not set(dependencies) <= allowed: return None
    var = lambda n: {"tag": "var", "name": n}
    app = lambda n, *args: {"tag": "app", "fn": n, "args": list(args)}
    bind = lambda n: {"tag": "bind", "name": n}
    ctor = lambda n, *args: {"tag": "ctor", "name": n, "args": list(args)}
    eq = lambda patterns, body: {"patterns": patterns, "body": body}
    zero = ctor("zero")
    succ = lambda n: ctor("succ", bind(n))
    predecessor_exact = exact_equations(env, NAT_REC + "predecessor", ["n"], [
        eq([zero], app("zero")), eq([succ("n")], var("n"))])
    if shortcut == "predecessor":
        recognized = predecessor_exact
    elif shortcut == "sub":
        recognized = predecessor_exact and exact_equations(env, NAT_SUB + "sub", ["m", "n"], [
            eq([bind("m"), zero], var("m")),
            eq([bind("m"), succ("n")], app(NAT_REC + "predecessor", app(NAT_SUB + "sub", var("m"), var("n"))))],
            decreasing=1)
    else:
        # The remainder equations, shared by the quotient.
        remainder = lambda n, d: app(NAT_MOD + "mod", var(n), var(d))
        mod_exact = decision_equations(env, NAT_MOD + "equalNat", allowed) is not None and \
            exact_equations(env, NAT_MOD + "chooseNat", ["condition", "yes", "no"], [
                eq([ctor(BOOL + "false"), bind("yes"), bind("no")], var("no")),
                eq([ctor(BOOL + "true"), bind("yes"), bind("no")], var("yes"))]) and \
            exact_body(env, NAT_MOD + "nextRemainder", ["d", "r"],
                       app(NAT_MOD + "chooseNat", app(NAT_MOD + "equalNat", app("succ", var("r")), var("d")),
                           {"tag": "nat", "value": "0"}, app("succ", var("r")))) and \
            exact_equations(env, NAT_MOD + "mod", ["n", "d"], [
                eq([zero, bind("d")], app("zero")),
                eq([succ("n"), bind("d")], app(NAT_MOD + "nextRemainder", var("d"), remainder("n", "d")))])
        recognized = mod_exact if shortcut == "mod" else mod_exact and \
            exact_equations(env, NAT_DIV + "quotientNat", ["n", "d"], [
                eq([zero, bind("d")], app("zero")),
                eq([succ("n"), bind("d")], app(NAT_MOD + "chooseNat",
                    app(NAT_MOD + "equalNat", app("succ", remainder("n", "d")), var("d")),
                    app("succ", app(NAT_DIV + "quotientNat", var("n"), var("d"))),
                    app(NAT_DIV + "quotientNat", var("n"), var("d"))))])
    return (shortcut, dependencies) if recognized else None


def execute_shortcut(shortcut: str, first: int, second: int) -> int:
    if shortcut == "predecessor":
        return first - 1 if first > 0 else 0
    if shortcut == "sub":
        return first - second if first > second else 0
    # The remainder by zero never wraps, so n % 0 = n; the quotient by zero is zero.
    if shortcut == "mod":
        return first if second == 0 else first % second
    return 0 if second == 0 else first // second


class Evaluator:
    def __init__(self, environment: Environment, allowed: set[str], fuel: int | None = None):
        self.env = environment
        self.allowed = allowed
        self.fuel = FUEL if fuel is None else fuel
        self.used: set[str] = set()
        self.memo: dict[tuple[str, tuple[Value, ...]], Value] = {}
        self.prefixes: dict[tuple[str, tuple[Value, ...]], tuple[int, Value]] = {}
        self.classifications: dict[str, tuple[str, tuple[str, ...]] | None] = {}
        self.decisions: dict[str, tuple[str, tuple[str, ...]] | None] = {}
        self.shortcuts: dict[str, tuple[str, tuple[str, ...]] | None] = {}

    def spend(self) -> None:
        self.fuel -= 1
        if self.fuel < 0:
            fail("ground evaluation exhausted its fuel")

    def evaluate(self, term: dict[str, Any], bindings: dict[str, Value] | None = None,
                 override: tuple[str, tuple[Value, ...], Value] | None = None) -> Value:
        self.spend()
        bindings = {} if bindings is None else bindings
        tag = term["tag"]
        if tag == "nat":
            return int(term["value"])
        if tag == "var":
            if term["name"] not in bindings:
                fail(f"ground computation contains free variable {term['name']}")
            return bindings[term["name"]]
        args = tuple(self.evaluate(arg, bindings, override) for arg in term["args"])
        return self.invoke(term["fn"], args, override)

    def invoke(self, fn: str, args: tuple[Value, ...],
               override: tuple[str, tuple[Value, ...], Value] | None = None) -> Value:
        self.spend()
        if fn == "zero" and not args:
            return 0
        if fn == "succ" and len(args) == 1 and isinstance(args[0], int):
            return args[0] + 1
        if override is not None and fn == override[0] and args == override[1]:
            return override[2]
        key = (fn, args)
        if key in self.memo:
            return self.memo[key]
        recursive = self.env.recursive.get(fn) if fn in self.allowed else None
        if recursive is not None:
            if fn not in self.decisions:
                self.decisions[fn] = decision_equations(self.env, fn, self.allowed)
            decision = self.decisions[fn]
            if decision is not None and len(args) == 2 and all(isinstance(arg, int) for arg in args):
                operator, definitions = decision
                self.used.update(definitions)
                left, right = int(args[0]), int(args[1])
                if operator == "minus":
                    result = max(0, left - right)
                else:
                    truth = left == right if operator == "equal" else left < right
                    result = (BOOL + ("true" if truth else "false"), ())
                self.memo[key] = result
                return result
            if fn not in self.shortcuts:
                self.shortcuts[fn] = shortcut_equations(self.env, fn, self.allowed)
            shortcut = self.shortcuts[fn]
            if shortcut is not None and len(args) == (1 if shortcut[0] == "predecessor" else 2) and \
                    all(isinstance(arg, int) for arg in args):
                operator, definitions = shortcut
                self.used.update(definitions)
                result = execute_shortcut(operator, int(args[0]), int(args[1]) if len(args) == 2 else 0)
                self.memo[key] = result
                return result
            classification = self.classify(fn, set())
            if classification is not None and all(isinstance(arg, int) for arg in args):
                operator, definitions = classification
                self.used.update(definitions)
                numbers = tuple(int(arg) for arg in args)
                if operator == "add":
                    result: Value = numbers[0] + numbers[1]
                elif operator == "mul":
                    result = numbers[0] * numbers[1]
                else:
                    result = 1
                    for value in range(2, numbers[0] + 1):
                        self.spend()
                        result *= value
                self.memo[key] = result
                return result
            primitive = self.primitive(fn, recursive, args)
            if primitive is not None:
                self.used.add(fn)
                self.memo[key] = primitive
                return primitive
            for equation in recursive["equations"]:
                found: dict[str, Value] = {}
                if all(match_pattern(pattern, args[index], found) for index, pattern in enumerate(equation["patterns"])):
                    self.used.add(fn)
                    result = self.evaluate(equation["body"], found, override)
                    self.memo[key] = result
                    return result
        explicit = self.env.bodies.get(fn) if fn in self.allowed else None
        if explicit is not None:
            self.used.add(fn)
            found = dict(zip(explicit["parameters"], args))
            result = self.evaluate(explicit["body"], found, override)
            self.memo[key] = result
            return result
        result = (fn, args)
        self.memo[key] = result
        return result

    def primitive(self, name: str, recursive: dict[str, Any], args: tuple[Value, ...]) -> Value | None:
        position = recursive["decreasingParameter"]
        count = args[position]
        if not isinstance(count, int) or count < 0:
            return None
        zero = equation_for(recursive, "zero")
        successor = equation_for(recursive, "succ")
        if zero is None or successor is None:
            return None
        current = list(args)
        current[position] = 0
        bindings: dict[str, Value] = {}
        if not all(match_pattern(pattern, current[index], bindings) for index, pattern in enumerate(zero["patterns"])):
            return None
        prefix_key = (name, tuple(current))
        cached = self.prefixes.get(prefix_key)
        if cached is not None and cached[0] <= count:
            start, value = cached
        else:
            start, value = 0, self.evaluate(zero["body"], bindings)
            self.memo[prefix_key] = value
        # Each prefix is an exact evaluation at this argument tuple. Retaining
        # it avoids rebuilding the whole prefix when another recursive state
        # asks for the same fixed arguments at the next natural index.
        for index in range(start, count):
            next_args = list(args)
            next_args[position] = index + 1
            bindings = {}
            if not all(match_pattern(pattern, next_args[i], bindings) for i, pattern in enumerate(successor["patterns"])):
                return None
            previous = list(args)
            previous[position] = index
            value = self.evaluate(successor["body"], bindings, (name, tuple(previous), value))
            self.memo[(name, tuple(next_args))] = value
            self.prefixes[prefix_key] = (index + 1, value)
        return value

    def classify(self, name: str, visiting: set[str]) -> tuple[str, tuple[str, ...]] | None:
        if name in self.classifications:
            return self.classifications[name]
        if name not in self.allowed or name in visiting or name not in self.env.recursive:
            return None
        visiting.add(name)
        recursive = self.env.recursive[name]
        zero = equation_for(recursive, "zero")
        successor = equation_for(recursive, "succ")
        result: tuple[str, tuple[str, ...]] | None = None
        if zero is not None and successor is not None:
            position = recursive["decreasingParameter"]
            root = successor["patterns"][position]
            predecessor = root["args"][0].get("name") if root.get("tag") == "ctor" and len(root.get("args", [])) == 1 and root["args"][0].get("tag") == "bind" else None
            call = find_recursive_call(successor["body"], name, successor["patterns"], position, predecessor) if predecessor else None
            body = successor["body"]
            if (call is not None and len(recursive["parameters"]) == 2 and
                    is_other_body(zero["body"], zero["patterns"], position) and
                    body.get("tag") == "app" and body.get("fn") == "succ" and body.get("args") == [call]):
                result = ("add", (name,))
            elif body.get("tag") == "app":
                nested = self.classify(body["fn"], visiting)
                args = body.get("args", [])
                if (call is not None and len(recursive["parameters"]) == 2 and natural_ast(zero["body"]) == 0 and
                        len(args) == 2 and nested is not None and nested[0] == "add" and
                        any(arg is call for arg in args) and any(is_other(arg, successor["patterns"], position) for arg in args)):
                    result = ("mul", tuple(sorted({name, *nested[1]})))
                elif (call is not None and len(recursive["parameters"]) == 1 and natural_ast(zero["body"]) == 1 and
                      len(args) == 2 and nested is not None and nested[0] == "mul" and
                      any(arg is call for arg in args) and any(is_successor_of(arg, predecessor) for arg in args)):
                    result = ("factorial", tuple(sorted({name, *nested[1]})))
        visiting.remove(name)
        self.classifications[name] = result
        return result


def equation_for(recursive: dict[str, Any], constructor: str) -> dict[str, Any] | None:
    position = recursive["decreasingParameter"]
    for equation in recursive["equations"]:
        root = equation["patterns"][position]
        if root.get("tag") == "ctor" and root.get("name") == constructor:
            return equation
    return None


def match_pattern(pattern: dict[str, Any], value: Value, bindings: dict[str, Value]) -> bool:
    if pattern["tag"] == "bind":
        previous = bindings.get(pattern["name"])
        if previous is not None:
            return previous == value
        bindings[pattern["name"]] = value
        return True
    if pattern["name"] == "zero":
        return value == 0 and pattern["args"] == []
    if pattern["name"] == "succ":
        return len(pattern["args"]) == 1 and isinstance(value, int) and value > 0 and match_pattern(pattern["args"][0], value - 1, bindings)
    return (not isinstance(value, int) and value[0] == pattern["name"] and len(value[1]) == len(pattern["args"]) and
            all(match_pattern(child, value[1][index], bindings) for index, child in enumerate(pattern["args"])))


def find_recursive_call(term: dict[str, Any], name: str, patterns: list[dict[str, Any]],
                        position: int, predecessor: str) -> dict[str, Any] | None:
    if term.get("tag") == "app" and term.get("fn") == name and len(term.get("args", [])) == len(patterns):
        good = True
        for index, argument in enumerate(term["args"]):
            pattern = patterns[index]
            expected = predecessor if index == position else pattern.get("name") if pattern.get("tag") == "bind" else None
            good = good and argument.get("tag") == "var" and argument.get("name") == expected
        if good:
            return term
    if term.get("tag") == "app":
        for argument in term["args"]:
            found = find_recursive_call(argument, name, patterns, position, predecessor)
            if found is not None:
                return found
    return None


def is_other_body(term: dict[str, Any], patterns: list[dict[str, Any]], position: int) -> bool:
    return term.get("tag") == "var" and any(
        index != position and pattern.get("tag") == "bind" and pattern.get("name") == term.get("name")
        for index, pattern in enumerate(patterns)
    )


def is_other(term: dict[str, Any], patterns: list[dict[str, Any]], position: int) -> bool:
    return is_other_body(term, patterns, position)


def is_successor_of(term: dict[str, Any], variable: str | None) -> bool:
    return (variable is not None and term.get("tag") == "app" and term.get("fn") == "succ" and
            len(term.get("args", [])) == 1 and term["args"][0] == {"tag": "var", "name": variable})


def check_computation(arena: Arena, environment: Environment, formula: int, definitions: list[str]) -> None:
    if definitions != sorted(set(definitions)):
        fail("computation dependencies must be unique and sorted")
    if any(name not in environment.bodies and name not in environment.recursive for name in definitions):
        fail("unknown computational definition")
    node = arena.formulas[formula]
    if node[0] != 1:
        fail("kernel computation requires an equality")
    allowed = set(definitions)
    left = Evaluator(environment, allowed)
    right = Evaluator(environment, allowed)
    left_value = left.evaluate(arena.reify_term(node[1]))
    right_value = right.evaluate(arena.reify_term(node[2]))
    used = sorted(left.used | right.used)
    if used != definitions:
        fail("computation certificate has an inexact definition dependency list")
    if left_value != right_value:
        fail("closed terms have different normal forms")


def check_rational_class_equality(environment: Environment, left: dict[str, Any], right: dict[str, Any]) -> None:
    cls = "Grace.Cumulus.Rat.Operations.rationalClass"
    theorem = cls + ".eq"
    add_name, mul_name = "Grace.Core.Nat.Rec.add", "Grace.Core.Nat.Rec.mul"
    def var(name: str) -> dict[str, Any]: return {"tag": "var", "name": name}
    def app(fn: str, *args: dict[str, Any]) -> dict[str, Any]: return {"tag": "app", "fn": fn, "args": list(args)}
    def eq(a: dict[str, Any], b: dict[str, Any]) -> dict[str, Any]: return {"tag": "eq", "left": a, "right": b}
    def cross(first: list[dict[str, Any]], second: list[dict[str, Any]]) -> dict[str, Any]:
        return eq(app(add_name, app(mul_name, second[2], first[0]), app(mul_name, first[2], second[1])),
                  app(add_name, app(mul_name, first[2], second[0]), app(mul_name, second[2], first[1])))
    if ("Naturals" not in environment.datatypes or any(term.get("tag") != "app" or term.get("fn") != cls or
        len(term.get("args", [])) != 3 for term in (left, right)) or
        any(natural_ast(arg) is None for arg in [*left["args"], *right["args"]]) or
        natural_ast(left["args"][2]) == 0 or natural_ast(right["args"][2]) == 0):
        fail("rational computation needs ground classes with positive denominators")
    names = ["a", "b", "m", "c", "d", "n"]
    variables = [var(name) for name in names]
    a, b, m, c, d, n = variables
    premises = ([{"tag": "pred", "pred": "Nat", "args": [item]} for item in variables] +
        [{"tag": "imp", "left": eq(m, {"tag": "nat", "value": "0"}), "right": {"tag": "bottom"}},
         {"tag": "imp", "left": eq(n, {"tag": "nat", "value": "0"}), "right": {"tag": "bottom"}},
         cross([a, b, m], [c, d, n])])
    schema = eq(app(cls, a, b, m), app(cls, c, d, n))
    for premise in reversed(premises): schema = {"tag": "imp", "left": premise, "right": schema}
    for name in reversed(names): schema = {"tag": "forall", "variable": name, "body": schema}
    if canonical(environment.theorems.get(theorem)) != canonical(schema):
        fail("rational computation requires proved quotient criterion")
    concrete = cross(left["args"], right["args"])
    allowed = {add_name, mul_name}
    left_eval, right_eval = Evaluator(environment, allowed), Evaluator(environment, allowed)
    first, second = left_eval.evaluate(concrete["left"]), right_eval.evaluate(concrete["right"])
    if first != second or left_eval.used | right_eval.used != allowed:
        fail("rational cross-product computation failed")


FIXED_DATA = {
    0: 1, 1: 1, 2: 1, 3: 2, 4: 1, 5: 0, 6: 0, 7: 1,
    8: 1, 9: 0, 10: 1, 11: 1, 13: 3, 14: 0, 15: 0, 16: 0,
    17: 1, 18: 1, 19: 0, 20: 0, 21: 0, 22: 0, 23: 3, 24: 1,
    25: 1, 26: 1, 27: 5,
    29: 0,
}


def expect(arena: Arena, formula: int, op: int, description: str) -> list[int]:
    if formula < 0 or formula >= len(arena.formulas) or arena.formulas[formula][0] != op:
        fail(f"{description} received the wrong formula")
    return arena.formulas[formula]


def same_contexts(p: Program, instruction: list[int], pc: int) -> None:
    count = instruction[3]
    for premise in instruction[4:4 + count]:
        if p.code[premise][2] != instruction[2]:
            fail(f"context mismatch at instruction {pc}")


def require_context(arena: Arena, expected: list[int], actual: int, pc: int) -> None:
    if arena.contexts[actual] != expected:
        fail(f"branch context mismatch at instruction {pc}")


def verify(p: Program, env: Environment, require_environment: bool = True,
           boundary_statements: dict[str, dict[str, Any]] | None = None) -> tuple[Arena, list[int]]:
    if require_environment and p.environment != env.digest:
        fail("proof and environment digests differ")
    arena = Arena(p)
    for root in [p.root, *[root for _, root in p.theorems]]:
        if root < 0 or root >= len(p.code) or p.contexts[p.code[root][2]]:
            fail("proof roots and theorem boundaries must have empty contexts")
    for index, node in enumerate(p.terms):
        if node[0] == 2:
            name = arena.symbol(node[1])
            if env.functions.get(name) != len(node) - 2:
                fail(f"unknown or malformed machine function {name} at term {index}")
    for index, node in enumerate(p.formulas):
        if node[0] == 2:
            name = arena.symbol(node[1])
            if env.predicates.get(name) != len(node) - 2:
                fail(f"unknown or malformed machine predicate {name} at formula {index}")

    boundary_roots = {arena.symbol(name): root for name, root in p.theorems}
    results = [-1] * len(p.code)
    for pc, instruction in enumerate(p.code):
        op, claim, context_id, premise_count = instruction[:4]
        premises = instruction[4:4 + premise_count]
        data = instruction[4 + premise_count:]
        if op in FIXED_DATA and len(data) != FIXED_DATA[op]:
            fail(f"malformed data at instruction {pc}")
        context = arena.contexts[context_id]
        derived = -1

        if op == 0:  # assumption
            if premise_count != 0 or data[0] not in context:
                fail(f"inactive assumption at instruction {pc}")
            derived = data[0]
        elif op in (1, 2, 3):  # environment dependency
            if premise_count != 0:
                fail(f"dependency has premises at instruction {pc}")
            name = arena.symbol(data[0])
            if op == 1:
                formula = env.axioms.get(name)
            elif op == 3:
                formula = env.property(name, arena.symbol(data[1]))
            elif name in boundary_roots:
                boundary = boundary_roots[name]
                if boundary >= pc:
                    fail(f"theorem dependency is not yet proved: {name}")
                derived = results[boundary]
                formula = None
            else:
                formula = env.theorems.get(name)
            if derived < 0:
                if formula is None:
                    fail(f"unknown machine dependency {name}")
                derived = arena.intern_formula(formula)
        elif op == 4:  # reflexivity
            if premise_count != 0:
                fail(f"reflexivity has premises at instruction {pc}")
            conclusion = expect(arena, claim, 1, "reflexivity")
            if conclusion[1:] != [data[0], data[0]]:
                fail(f"bad reflexivity at instruction {pc}")
            derived = claim
        elif op == 28:  # compute
            if premise_count != 0 or not data or len(data) != 1 + data[0]:
                fail(f"malformed computation at instruction {pc}")
            definitions = [arena.symbol(item) for item in data[1:]]
            check_computation(arena, env, claim, definitions)
            derived = claim
        elif op == 29:  # rationalClassCompute
            if premise_count != 0 or data:
                fail(f"malformed rational computation at instruction {pc}")
            formula = arena.reify_formula(claim)
            if formula["tag"] != "eq": fail("rational computation requires equality")
            check_rational_class_equality(env, formula["left"], formula["right"])
            derived = claim
        elif op == 5:  # symmetry
            if premise_count != 1:
                fail(f"bad symmetry premise count at {pc}")
            same_contexts(p, instruction, pc)
            equality = expect(arena, results[premises[0]], 1, "symmetry")
            conclusion = expect(arena, claim, 1, "symmetry")
            if conclusion[1:] != [equality[2], equality[1]]:
                fail(f"bad symmetry at instruction {pc}")
            derived = claim
        elif op == 6:  # transitivity
            if premise_count != 2:
                fail(f"bad transitivity premise count at {pc}")
            same_contexts(p, instruction, pc)
            left = expect(arena, results[premises[0]], 1, "transitivity")
            right = expect(arena, results[premises[1]], 1, "transitivity")
            conclusion = expect(arena, claim, 1, "transitivity")
            if left[2] != right[1] or conclusion[1:] != [left[1], right[2]]:
                fail(f"bad transitivity at instruction {pc}")
            derived = claim
        elif op == 7:  # congruence
            same_contexts(p, instruction, pc)
            fn = arena.symbol(data[0])
            if env.functions.get(fn) != premise_count:
                fail(f"bad congruence arity at instruction {pc}")
            equalities = [expect(arena, results[x], 1, "congruence") for x in premises]
            left = arena.application(fn, [item[1] for item in equalities])
            right = arena.application(fn, [item[2] for item in equalities])
            if expect(arena, claim, 1, "congruence")[1:] != [left, right]:
                fail(f"bad congruence at instruction {pc}")
            derived = claim
        elif op == 8:  # implication introduction
            if premise_count != 1:
                fail(f"bad implication introduction premise count at {pc}")
            assumption = data[0]
            require_context(arena, [*context, assumption], p.code[premises[0]][2], pc)
            conclusion = expect(arena, claim, 3, "implication introduction")
            if conclusion[1:] != [assumption, results[premises[0]]]:
                fail(f"bad implication introduction at {pc}")
            derived = claim
        elif op == 9:  # implication elimination
            if premise_count != 2:
                fail(f"bad implication elimination premise count at {pc}")
            same_contexts(p, instruction, pc)
            implication = expect(arena, results[premises[0]], 3, "implication elimination")
            if implication[1] != results[premises[1]] or implication[2] != claim:
                fail(f"bad implication elimination at {pc}")
            derived = claim
        elif op == 10:  # universal introduction
            if premise_count != 1:
                fail(f"bad universal introduction premise count at {pc}")
            same_contexts(p, instruction, pc)
            symbol = data[0]
            if any(arena.has_free_formula(formula, symbol) for formula in context):
                fail(f"generalized variable is free in context at {pc}")
            body = expect(arena, claim, 4, "universal introduction")[1]
            if not arena.matches_abstraction(body, results[premises[0]], symbol):
                fail(f"bad universal introduction at {pc}")
            derived = claim
        elif op == 11:  # universal elimination
            if premise_count != 1:
                fail(f"bad universal elimination premise count at {pc}")
            same_contexts(p, instruction, pc)
            universal = expect(arena, results[premises[0]], 4, "universal elimination")
            if claim != arena.instantiate_formula(universal[1], data[0]):
                fail(f"bad universal elimination at {pc}")
            derived = claim
        elif op == 13:  # equality elimination
            if premise_count != 2 or data[2] not in (0, 1):
                fail(f"bad equality elimination data at {pc}")
            same_contexts(p, instruction, pc)
            equality = expect(arena, results[premises[0]], 1, "equality elimination")
            source, target = (equality[2], equality[1]) if data[2] else (equality[1], equality[2])
            if (results[premises[1]] != arena.substitute_formula(data[1], data[0], source) or
                    claim != arena.substitute_formula(data[1], data[0], target)):
                fail(f"bad equality elimination at {pc}")
            derived = claim
        elif op == 14:  # conjunction introduction
            if premise_count != 2:
                fail(f"bad conjunction introduction premise count at {pc}")
            same_contexts(p, instruction, pc)
            if expect(arena, claim, 5, "conjunction introduction")[1:] != [results[premises[0]], results[premises[1]]]:
                fail(f"bad conjunction introduction at {pc}")
            derived = claim
        elif op in (15, 16):  # conjunction elimination
            if premise_count != 1:
                fail(f"bad conjunction elimination premise count at {pc}")
            same_contexts(p, instruction, pc)
            conjunction = expect(arena, results[premises[0]], 5, "conjunction elimination")
            if claim != conjunction[1 if op == 15 else 2]:
                fail(f"bad conjunction elimination at {pc}")
            derived = claim
        elif op in (17, 18):  # disjunction introduction
            if premise_count != 1:
                fail(f"bad disjunction introduction premise count at {pc}")
            same_contexts(p, instruction, pc)
            conclusion = expect(arena, claim, 6, "disjunction introduction")
            expected = [results[premises[0]], data[0]] if op == 17 else [data[0], results[premises[0]]]
            if conclusion[1:] != expected:
                fail(f"bad disjunction introduction at {pc}")
            derived = claim
        elif op == 19:  # disjunction elimination
            if premise_count != 3 or p.code[premises[0]][2] != context_id:
                fail(f"bad disjunction elimination context at {pc}")
            disjunction = expect(arena, results[premises[0]], 6, "disjunction elimination")
            require_context(arena, [*context, disjunction[1]], p.code[premises[1]][2], pc)
            require_context(arena, [*context, disjunction[2]], p.code[premises[2]][2], pc)
            if results[premises[1]] != results[premises[2]] or claim != results[premises[1]]:
                fail(f"bad disjunction elimination at {pc}")
            derived = claim
        elif op == 20:  # equivalence introduction
            if premise_count != 2:
                fail(f"bad equivalence introduction premise count at {pc}")
            same_contexts(p, instruction, pc)
            forward = expect(arena, results[premises[0]], 3, "equivalence introduction")
            backward = expect(arena, results[premises[1]], 3, "equivalence introduction")
            conclusion = expect(arena, claim, 7, "equivalence introduction")
            if forward[1] != backward[2] or forward[2] != backward[1] or conclusion[1:] != forward[1:]:
                fail(f"bad equivalence introduction at {pc}")
            derived = claim
        elif op in (21, 22):  # equivalence elimination
            if premise_count != 1:
                fail(f"bad equivalence elimination premise count at {pc}")
            same_contexts(p, instruction, pc)
            equivalence = expect(arena, results[premises[0]], 7, "equivalence elimination")
            conclusion = expect(arena, claim, 3, "equivalence elimination")
            expected = [equivalence[2], equivalence[1]] if op == 22 else equivalence[1:]
            if conclusion[1:] != expected:
                fail(f"bad equivalence elimination at {pc}")
            derived = claim
        elif op == 23:  # existential introduction
            if premise_count != 1:
                fail(f"bad existential introduction premise count at {pc}")
            same_contexts(p, instruction, pc)
            body = expect(arena, claim, 8, "existential introduction")[1]
            if (not arena.matches_abstraction(body, data[1], data[0]) or
                    results[premises[0]] != arena.substitute_formula(data[1], data[0], data[2])):
                fail(f"bad existential introduction at {pc}")
            derived = claim
        elif op == 24:  # existential elimination
            if premise_count != 2 or p.code[premises[0]][2] != context_id:
                fail(f"bad existential elimination context at {pc}")
            existential = expect(arena, results[premises[0]], 8, "existential elimination")
            witness = data[0]
            if any(arena.has_free_formula(formula, witness) for formula in context) or arena.has_free_formula(results[premises[0]], witness):
                fail(f"existential witness is not fresh at {pc}")
            witness_term = arena.term_node([0, witness])
            instance = arena.instantiate_formula(existential[1], witness_term)
            require_context(arena, [*context, instance], p.code[premises[1]][2], pc)
            if arena.has_free_formula(results[premises[1]], witness) or claim != results[premises[1]]:
                fail(f"existential witness escapes at {pc}")
            derived = claim
        elif op == 25:  # false elimination
            if premise_count != 1:
                fail(f"bad false elimination premise count at {pc}")
            same_contexts(p, instruction, pc)
            expect(arena, results[premises[0]], 0, "false elimination")
            if claim != data[0]:
                fail(f"bad false elimination at {pc}")
            derived = claim
        elif op == 26:  # double-negation elimination
            if premise_count != 1:
                fail(f"bad DNE premise count at {pc}")
            same_contexts(p, instruction, pc)
            bottom = arena.formula_node([0])
            negated = arena.formula_node([3, data[0], bottom])
            double = arena.formula_node([3, negated, bottom])
            if results[premises[0]] != double or claim != data[0]:
                fail(f"bad double-negation elimination at {pc}")
            derived = claim
        elif op == 12:  # structural induction
            if len(data) < 4:
                fail(f"malformed induction at {pc}")
            datatype = env.datatypes.get(arena.symbol(data[0]))
            variable, motive, parameter_count = data[1:4]
            parameters = data[4:4 + parameter_count]
            if 4 + parameter_count >= len(data):
                fail(f"truncated induction parameters at {pc}")
            if any(parameter < 0 or parameter >= len(arena.terms) for parameter in parameters):
                fail(f"invalid induction parameter at {pc}")
            case_count = data[4 + parameter_count]
            if datatype is None or parameter_count != len(datatype.get("parameters", [])) or case_count != len(datatype["constructors"]) or premise_count != case_count:
                fail(f"malformed induction at {pc}")
            if any(arena.has_free_term(parameter, variable) for parameter in parameters):
                fail(f"induction variable occurs in a datatype parameter at {pc}")
            if any(arena.has_free_formula(formula, variable) for formula in context):
                fail(f"induction variable is free in context at {pc}")
            cursor = 5 + parameter_count
            seen: set[str] = set()
            for index in range(case_count):
                if cursor + 2 > len(data):
                    fail(f"truncated induction case at {pc}")
                constructor_name = arena.symbol(data[cursor])
                field_count = data[cursor + 1]
                cursor += 2
                fields = data[cursor:cursor + field_count]
                cursor += field_count
                constructor = next((item for item in datatype["constructors"] if item["name"] == constructor_name), None)
                if constructor is None or constructor["arity"] != field_count or constructor_name in seen or len(set(fields)) != len(fields):
                    fail(f"malformed induction case at {pc}")
                seen.add(constructor_name)
                if any(field == variable or arena.has_free_formula(motive, field) or
                       any(arena.has_free_term(parameter, field) for parameter in parameters) or
                       any(arena.has_free_formula(formula, field) for formula in context)
                       for field in fields):
                    fail(f"induction field is not fresh at {pc}")
                field_terms = [arena.term_node([0, field]) for field in fields]
                expected_context = list(context)
                for field_index in range(constructor["arity"]):
                    if field_index in constructor["recursiveFields"]:
                        expected_context.append(arena.predicate(datatype["predicate"], parameters + [field_terms[field_index]]))
                        expected_context.append(arena.substitute_formula(motive, variable, field_terms[field_index]))
                    else:
                        parameter_field = next((item for item in constructor.get("parameterFields", []) if item["field"] == field_index), None)
                        if parameter_field is not None:
                            expected_context.append(arena.predicate("in", [field_terms[field_index], parameters[parameter_field["parameter"]]]))
                require_context(arena, expected_context, p.code[premises[index]][2], pc)
                constructor_term = arena.application(constructor_name, field_terms)
                if results[premises[index]] != arena.substitute_formula(motive, variable, constructor_term):
                    fail(f"wrong induction case at {pc}")
            if cursor != len(data) or len(seen) != case_count:
                fail(f"malformed induction data at {pc}")
            variable_term = arena.term_node([0, variable])
            membership = arena.predicate(datatype["predicate"], parameters + [variable_term])
            body = arena.formula_node([3, membership, motive])
            derived = arena.formula_node([4, arena.abstract_formula(body, variable)])
        elif op == 27:  # well-founded induction
            if premise_count != 2:
                fail(f"bad well-founded induction premise count at {pc}")
            same_contexts(p, instruction, pc)
            relation, domain, variable, predecessor, motive = data
            if variable == predecessor or arena.has_free_term(relation, variable) or arena.has_free_term(relation, predecessor) or \
                    arena.has_free_term(domain, variable) or arena.has_free_term(domain, predecessor) or \
                    arena.has_free_formula(motive, predecessor) or any(
                    arena.has_free_formula(formula, variable) or arena.has_free_formula(formula, predecessor) for formula in context):
                fail(f"malformed well-founded induction variables at {pc}")
            if results[premises[0]] != arena.predicate("wellFoundedOn", [relation, domain]):
                fail(f"wrong well-foundedness certificate at {pc}")
            x, y = arena.term_node([0, variable]), arena.term_node([0, predecessor])
            predecessor_motive = arena.substitute_formula(motive, variable, y)
            conjunction = arena.formula_node([5, arena.predicate("in", [y, domain]), arena.predicate("relates", [relation, y, x])])
            ih_body = arena.formula_node([3, conjunction, predecessor_motive])
            ih = arena.formula_node([4, arena.abstract_formula(ih_body, predecessor)])
            in_domain = arena.predicate("in", [x, domain])
            step_body = arena.formula_node([3, in_domain, arena.formula_node([3, ih, motive])])
            expected_step = arena.formula_node([4, arena.abstract_formula(step_body, variable)])
            if results[premises[1]] != expected_step:
                fail(f"wrong well-founded induction step at {pc}")
            result_body = arena.formula_node([3, in_domain, motive])
            derived = arena.formula_node([4, arena.abstract_formula(result_body, variable)])
        else:
            fail(f"unsupported proof opcode {op} at {pc}")

        if derived != claim:
            fail(f"instruction {pc} derives the wrong formula")
        results[pc] = derived

    for name_id, root in p.theorems:
        name = arena.symbol(name_id)
        statement = boundary_statements.get(name) if boundary_statements is not None else env.theorems.get(name)
        if statement is None or results[root] != arena.intern_formula(statement):
            fail(f"theorem boundary mismatch: {name}")
    return arena, results


def main() -> int:
    global FUEL
    parser = argparse.ArgumentParser(description="Check a GRACE17 G17M certificate independently")
    parser.add_argument("certificate", type=Path, help="G17M certificate file (.g17m)")
    parser.add_argument("--environment", required=True, type=Path, help="authenticated logical environment (.g17env) the certificate was exported against")
    parser.add_argument("--json", action="store_true", help="print a JSON report instead of plain text")
    parser.add_argument("--fuel", type=int, default=FUEL, metavar="STEPS",
                        help=f"ground evaluation steps per computation instruction (default {FUEL})")
    args = parser.parse_args()
    if args.fuel < 1: parser.error("--fuel must be positive")
    FUEL = args.fuel
    try:
        environment = Environment(args.environment)
        program = decode(args.certificate)
        arena, _ = verify(program, environment)
        result = {
            "ok": True,
            "checker": "grace17-python-reference",
            "version": VERSION,
            "theorems": len(program.theorems) if program.theorems else 1,
            "instructions": len(program.code),
            "terms": len(arena.terms),
            "formulas": len(arena.formulas),
            "environment": environment.digest,
        }
        print(json.dumps(result, separators=(",", ":")) if args.json else
              f"checked {result['theorems']} theorem(s), {result['instructions']} instructions")
        return 0
    except (CheckError, OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        result = {"ok": False, "checker": "grace17-python-reference", "message": str(error)}
        print(json.dumps(result, separators=(",", ":")) if args.json else f"check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
