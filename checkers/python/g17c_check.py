#!/usr/bin/env python3
# Independent, dependency-free checker for G17C compiled modules.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Independent, dependency-free strict checker for GRACE17 G17C v3 modules.

This file deliberately imports only the equally small G17M reference checker.
It does not parse Grace17 source, elaborate soft types, run tactics, or read a
surface index. Named ZF/ZFC/ZFG foundations are constructed by this checker;
every library extension is then reconstructed by checked events.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import sys
import re
from pathlib import Path
from typing import Any

import g17check as machine

CheckError = machine.CheckError
fail = machine.fail
canonical = machine.canonical
DIGEST = re.compile(r"[0-9a-f]{64}\Z")


def natural_int(value: Any) -> bool:
    return type(value) is int and 0 <= value <= 0xFFFF_FFFF


def v(name: str) -> dict[str, Any]:
    return {"tag": "var", "name": name}


def app(fn: str, *args: dict[str, Any]) -> dict[str, Any]:
    return {"tag": "app", "fn": fn, "args": list(args)}


def nat(value: int | str) -> dict[str, Any]:
    return {"tag": "nat", "value": str(value)}


def bottom() -> dict[str, Any]:
    return {"tag": "bottom"}


def eq(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return {"tag": "eq", "left": left, "right": right}


def pred(name: str, *args: dict[str, Any]) -> dict[str, Any]:
    return {"tag": "pred", "pred": name, "args": list(args)}


def binary(tag: str, left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return {"tag": tag, "left": left, "right": right}


def imp(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return binary("imp", left, right)


def conjunction(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return binary("and", left, right)


def disjunction(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return binary("or", left, right)


def iff(left: dict[str, Any], right: dict[str, Any]) -> dict[str, Any]:
    return binary("iff", left, right)


def neg(value: dict[str, Any]) -> dict[str, Any]:
    return imp(value, bottom())


def quantify(tag: str, variable: str, body: dict[str, Any]) -> dict[str, Any]:
    return {"tag": tag, "variable": variable, "body": body}


def forall(variable: str, body: dict[str, Any]) -> dict[str, Any]:
    return quantify("forall", variable, body)


def exists(variable: str, body: dict[str, Any]) -> dict[str, Any]:
    return quantify("exists", variable, body)


def foralls(variables: list[str], body: dict[str, Any]) -> dict[str, Any]:
    for variable in reversed(variables):
        body = forall(variable, body)
    return body


def natural_value(term: dict[str, Any]) -> int | None:
    return machine.natural_ast(term)


def term_key(term: dict[str, Any], binders: tuple[str, ...] = ()) -> Any:
    number = natural_value(term)
    if number is not None:
        return ("nat", number)
    if term.get("tag") == "var":
        for index, name in enumerate(reversed(binders)):
            if name == term.get("name"):
                return ("bound", index)
        return ("free", term.get("name"))
    return ("app", term.get("fn"), tuple(term_key(arg, binders) for arg in term.get("args", [])))


def formula_key(formula: dict[str, Any], binders: tuple[str, ...] = ()) -> Any:
    tag = formula.get("tag")
    if tag == "bottom":
        return (tag,)
    if tag == "eq":
        return (tag, term_key(formula["left"], binders), term_key(formula["right"], binders))
    if tag == "pred":
        return (tag, formula.get("pred"), tuple(term_key(arg, binders) for arg in formula.get("args", [])))
    if tag in ("imp", "and", "or", "iff"):
        return (tag, formula_key(formula["left"], binders), formula_key(formula["right"], binders))
    if tag in ("forall", "exists"):
        return (tag, formula_key(formula["body"], (*binders, formula["variable"])))
    fail("malformed formula")


def same_formula(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return formula_key(left) == formula_key(right)


def same_term(left: dict[str, Any], right: dict[str, Any]) -> bool:
    return term_key(left) == term_key(right)


def free_term(term: dict[str, Any], result: set[str] | None = None) -> set[str]:
    result = set() if result is None else result
    if term.get("tag") == "var":
        result.add(term["name"])
    elif term.get("tag") == "app":
        for argument in term.get("args", []):
            free_term(argument, result)
    return result


def free_formula(formula: dict[str, Any]) -> set[str]:
    result: set[str] = set()

    def visit_term(term: dict[str, Any], bound: set[str]) -> None:
        if term.get("tag") == "var":
            if term["name"] not in bound:
                result.add(term["name"])
        elif term.get("tag") == "app":
            for argument in term.get("args", []):
                visit_term(argument, bound)

    def visit(value: dict[str, Any], bound: set[str]) -> None:
        tag = value.get("tag")
        if tag == "eq":
            visit_term(value["left"], bound); visit_term(value["right"], bound)
        elif tag == "pred":
            for argument in value.get("args", []): visit_term(argument, bound)
        elif tag in ("imp", "and", "or", "iff"):
            visit(value["left"], bound); visit(value["right"], bound)
        elif tag in ("forall", "exists"):
            visit(value["body"], {*bound, value["variable"]})
        elif tag != "bottom":
            fail("malformed formula")
    visit(formula, set())
    return result


def substitute_term(term: dict[str, Any], variable: str, replacement: dict[str, Any]) -> dict[str, Any]:
    if term.get("tag") == "var":
        return replacement if term.get("name") == variable else term
    if term.get("tag") != "app":
        return term
    return app(term["fn"], *(substitute_term(arg, variable, replacement) for arg in term["args"]))


def fresh(base: str, forbidden: set[str]) -> str:
    if base not in forbidden:
        return base
    index = 1
    while f"{base}_{index}" in forbidden:
        index += 1
    return f"{base}_{index}"


def substitute_formula(formula: dict[str, Any], variable: str, replacement: dict[str, Any]) -> dict[str, Any]:
    tag = formula["tag"]
    if tag == "bottom":
        return formula
    if tag == "eq":
        return eq(substitute_term(formula["left"], variable, replacement),
                  substitute_term(formula["right"], variable, replacement))
    if tag == "pred":
        return pred(formula["pred"], *(substitute_term(arg, variable, replacement) for arg in formula["args"]))
    if tag in ("imp", "and", "or", "iff"):
        return binary(tag, substitute_formula(formula["left"], variable, replacement),
                      substitute_formula(formula["right"], variable, replacement))
    binder = formula["variable"]
    if binder == variable:
        return formula
    if binder in free_term(replacement) and variable in free_formula(formula["body"]):
        forbidden = free_formula(formula["body"]) | free_term(replacement) | {variable}
        renamed = fresh(binder, forbidden)
        body = substitute_formula(formula["body"], binder, v(renamed))
        return quantify(tag, renamed, substitute_formula(body, variable, replacement))
    return quantify(tag, binder, substitute_formula(formula["body"], variable, replacement))


def substitute_many(term: dict[str, Any], substitutions: dict[str, dict[str, Any]]) -> dict[str, Any]:
    result = term
    for variable, replacement in substitutions.items():
        result = substitute_term(result, variable, replacement)
    return result


def substitute_simultaneous(term: dict[str, Any], substitutions: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Replace every listed variable at once, as the kernel's substituteMany does."""
    if term.get("tag") == "var":
        return substitutions.get(term["name"], term)
    if term.get("tag") != "app":
        return term
    return app(term["fn"], *(substitute_simultaneous(arg, substitutions) for arg in term["args"]))


class KernelEnvironment(machine.Environment):
    def __init__(self, path: Path):
        super().__init__(path)
        self.receipts: dict[str, str] = {}
        self.results: dict[str, str] = {}

    @classmethod
    def empty_foundation(cls, profile: str) -> "KernelEnvironment":
        if profile not in ("ZF", "ZFC", "ZFG"):
            fail(f"unsupported foundation profile: {profile}")
        result = cls.__new__(cls)
        result.capabilities = {
            "separation": True,
            "replacement": True,
            "inductiveDefinitions": True,
            "setTheory": profile,
        }
        result.digest = ""
        result.functions = {}
        result.predicates = {}
        result.axioms = {}
        result.theorems = {}
        result.definitions = {}
        result.datatypes = {}
        result.recursive = {}
        result.bodies = {}
        result.receipts = {}
        result.results = {}
        return result

    def add_axiom(self, name: str, formula: dict[str, Any]) -> None:
        if not name or name in self.axioms or name in self.theorems:
            fail(f"duplicate proposition name: {name}")
        self.check_formula(formula)
        if free_formula(formula):
            fail(f"foundation axiom {name} is not closed")
        self.axioms[name] = formula

    def fresh_name(self, name: str) -> None:
        if not name or name in self.functions or name in self.predicates or name in self.definitions:
            fail(f"duplicate logical symbol: {name}")

    def parameters(self, values: list[str]) -> None:
        if any(not value for value in values) or len(set(values)) != len(values):
            fail("malformed definition parameters")

    def check_term(self, term: dict[str, Any]) -> None:
        tag = term.get("tag")
        if tag == "var":
            if not isinstance(term.get("name"), str) or not term["name"]: fail("malformed variable")
        elif tag == "nat":
            if not isinstance(term.get("value"), str) or not machine.NAT.fullmatch(term["value"]): fail("malformed natural")
        elif tag == "app":
            args = term.get("args")
            if not isinstance(args, list) or self.functions.get(term.get("fn")) != len(args): fail("unknown or malformed function")
            for argument in args: self.check_term(argument)
        else:
            fail("malformed term")

    def check_formula(self, formula: dict[str, Any]) -> None:
        tag = formula.get("tag")
        if tag == "bottom": return
        if tag == "eq":
            self.check_term(formula["left"]); self.check_term(formula["right"]); return
        if tag == "pred":
            args = formula.get("args")
            if not isinstance(args, list) or self.predicates.get(formula.get("pred")) != len(args): fail("unknown or malformed predicate")
            for argument in args: self.check_term(argument)
            return
        if tag in ("imp", "and", "or", "iff"):
            self.check_formula(formula["left"]); self.check_formula(formula["right"]); return
        if tag in ("forall", "exists") and isinstance(formula.get("variable"), str) and formula["variable"]:
            self.check_formula(formula["body"]); return
        fail("malformed formula")

    def record_definition(self, name: str, kind: str, parameters: list[str],
                          properties: dict[str, dict[str, Any]]) -> None:
        for formula in properties.values():
            self.check_formula(formula)
            if free_formula(formula): fail("definition property is not closed")
        self.definitions[name] = {"kind": kind, "parameters": list(parameters), "properties": properties}

    def define_function(self, payload: dict[str, Any]) -> None:
        name, parameters, body = payload["name"], payload["parameters"], payload["body"]
        self.parameters(parameters); self.fresh_name(name); self.check_term(body)
        if name in functions_in_term(body) or not free_term(body) <= set(parameters): fail("bad function definition")
        self.functions[name] = len(parameters)
        self.bodies[name] = {"parameters": list(parameters), "body": body}
        self.record_definition(name, "function", parameters,
                               {"equation": foralls(parameters, eq(app(name, *(v(x) for x in parameters)), body))})

    def define_predicate(self, payload: dict[str, Any]) -> None:
        name, parameters, body = payload["name"], payload["parameters"], payload["body"]
        self.parameters(parameters); self.fresh_name(name); self.check_formula(body)
        if name in symbols_in_formula(body) or not free_formula(body) <= set(parameters): fail("bad predicate definition")
        self.predicates[name] = len(parameters)
        self.record_definition(name, "predicate", parameters,
                               {"equation": foralls(parameters, iff(pred(name, *(v(x) for x in parameters)), body))})

    def define_subset(self, payload: dict[str, Any]) -> None:
        if not self.capabilities.get("separation"): fail("foundation does not enable Separation")
        name, parameters = payload["name"], payload["parameters"]
        element, bound, condition = payload["element"], payload["bound"], payload["condition"]
        self.parameters(parameters); self.fresh_name(name); self.check_term(bound); self.check_formula(condition)
        if not element or element in parameters or not free_term(bound) <= set(parameters) or not free_formula(condition) <= {*parameters, element}:
            fail("malformed Separation instance")
        self.functions[name] = len(parameters)
        membership = foralls([*parameters, element], iff(
            pred("in", v(element), app(name, *(v(x) for x in parameters))),
            conjunction(pred("in", v(element), bound), condition)))
        self.record_definition(name, "separation", parameters, {"membership": membership})

    def declare_datatype(self, spec: dict[str, Any]) -> None:
        if not self.capabilities.get("inductiveDefinitions"): fail("foundation does not enable inductive definitions")
        name, predicate, constructors = spec.get("name"), spec.get("predicate"), spec.get("constructors")
        parameters = spec.get("parameters", [])
        if (not name or not predicate or not isinstance(constructors, list) or not constructors or
            type(spec.get("setTheoreticEncoding")) is not bool): fail("malformed datatype")
        self.parameters(parameters); self.fresh_name(name); self.fresh_name(predicate)
        if spec["setTheoreticEncoding"] and (self.functions.get("orderedPair") != 2 or
            self.functions.get("empty") != 0 or "Naturals" not in self.datatypes):
            fail("set-theoretic datatype prerequisites are absent")
        if name in self.datatypes: fail("duplicate datatype")
        seen: set[str] = set()
        for ctor in constructors:
            ctor_name, arity = ctor.get("name"), ctor.get("arity")
            self.fresh_name(ctor_name)
            if ctor_name in seen or not natural_int(arity): fail("malformed constructor")
            seen.add(ctor_name)
            recursive = ctor.get("recursiveFields", [])
            fields = ctor.get("parameterFields", [])
            if len(set(recursive)) != len(recursive) or any(not natural_int(x) or not 0 <= x < arity for x in recursive): fail("bad recursive fields")
            if len({x.get("field") for x in fields}) != len(fields) or any(
                not natural_int(x.get("field")) or not 0 <= x["field"] < arity or
                not natural_int(x.get("parameter")) or not 0 <= x["parameter"] < len(parameters) or
                x["field"] in recursive for x in fields): fail("bad parameter fields")
        self.predicates[predicate] = len(parameters) + 1
        for ctor in constructors: self.functions[ctor["name"]] = ctor["arity"]

        def names(prefix: str, count: int) -> list[str]:
            used = set(parameters); result: list[str] = []
            for index in range(count):
                candidate = f"{prefix}{index}"
                while candidate in used: candidate = "_" + candidate
                used.add(candidate); result.append(candidate)
            return result

        def combine(tag: str, items: list[dict[str, Any]]) -> dict[str, Any]:
            if not items: fail("empty datatype connective")
            result = items[0]
            for item in items[1:]: result = binary(tag, result, item)
            return result

        def sequence(items: list[dict[str, Any]]) -> dict[str, Any]:
            result = app("empty")
            for item in reversed(items): result = app("orderedPair", item, result)
            return result

        properties: dict[str, dict[str, Any]] = {}
        for ctor in constructors:
            local = ctor["name"].split(".")[-1]; fields = [f"field{x}" for x in range(ctor["arity"])]
            closure = pred(predicate, *(v(x) for x in parameters), app(ctor["name"], *(v(x) for x in fields)))
            for index in reversed(range(len(fields))):
                if index in ctor["recursiveFields"]:
                    closure = imp(pred(predicate, *(v(x) for x in parameters), v(fields[index])), closure)
                else:
                    item = next((x for x in ctor.get("parameterFields", []) if x["field"] == index), None)
                    if item is not None: closure = imp(pred("in", v(fields[index]), v(parameters[item["parameter"]])), closure)
            properties[f"constructor.{local}"] = foralls([*parameters, *fields], closure)
            if spec.get("setTheoreticEncoding"):
                tag = sequence([nat(ord(char)) for char in f"{name}.{ctor['name']}"])
                properties[f"representation.{local}"] = foralls([*parameters, *fields],
                    eq(app(ctor["name"], *(v(x) for x in fields)), app("orderedPair", tag, sequence([v(x) for x in fields]))))
        for ctor in constructors:
            if ctor["arity"] == 0: continue
            local = ctor["name"].split(".")[-1]
            left, right = names("left", ctor["arity"]), names("right", ctor["arity"])
            properties[f"injective.{local}"] = foralls([*left, *right], imp(
                eq(app(ctor["name"], *(v(x) for x in left)), app(ctor["name"], *(v(x) for x in right))),
                combine("and", [eq(v(x), v(right[index])) for index, x in enumerate(left)])))
        for left_index, left_ctor in enumerate(constructors):
            for right_ctor in constructors[left_index + 1:]:
                left, right = names("left", left_ctor["arity"]), names("right", right_ctor["arity"])
                properties[f"disjoint.{left_ctor['name'].split('.')[-1]}.{right_ctor['name'].split('.')[-1]}"] = foralls(
                    [*left, *right], neg(eq(app(left_ctor["name"], *(v(x) for x in left)), app(right_ctor["name"], *(v(x) for x in right)))))
        element = "_value" if "value" in parameters else "value"
        alternatives: list[dict[str, Any]] = []
        for ctor_index, ctor in enumerate(constructors):
            fields = names(f"case{ctor_index}_field", ctor["arity"]); guards: list[dict[str, Any]] = []
            for field_index, field in enumerate(fields):
                if field_index in ctor["recursiveFields"]:
                    guards.append(pred(predicate, *(v(x) for x in parameters), v(field)))
                else:
                    item = next((x for x in ctor.get("parameterFields", []) if x["field"] == field_index), None)
                    if item is not None: guards.append(pred("in", v(field), v(parameters[item["parameter"]])))
            guards.append(eq(v(element), app(ctor["name"], *(v(x) for x in fields))))
            alternative = combine("and", guards)
            for field in reversed(fields): alternative = exists(field, alternative)
            alternatives.append(alternative)
        properties["cases"] = foralls([*parameters, element], imp(
            pred(predicate, *(v(x) for x in parameters), v(element)), combine("or", alternatives)))
        self.datatypes[name] = spec
        self.record_definition(name, "datatype", [], properties)

    def register_natural_datatype(self) -> None:
        """Register computational Nat metadata only after checking its set interface."""
        if "Naturals" in self.datatypes:
            fail("Naturals datatype is already registered")
        zero = self.bodies.get("zero")
        successor = self.bodies.get("succ")
        natural = self.property("Nat", "equation")
        expected_successor = app("union", app("pair", v("n"), app("pair", v("n"), v("n"))))
        expected_natural = forall("n", iff(pred("Nat", v("n")), pred("in", v("n"), app("omega"))))
        minimality = forall("A", imp(conjunction(
            pred("in", app("empty"), v("A")),
            forall("n", imp(pred("in", v("n"), v("A")), pred("in", expected_successor, v("A")))),
        ), forall("n", imp(pred("in", v("n"), app("omega")), pred("in", v("n"), v("A"))))))
        if (zero != {"parameters": [], "body": app("empty")} or
                successor != {"parameters": ["n"], "body": expected_successor} or
                natural is None or not same_formula(natural, expected_natural) or
                self.axioms.get("set.infinity.minimal") is None or
                not same_formula(self.axioms["set.infinity.minimal"], minimality)):
            fail("Natural datatype registration requires the canonical von Neumann interface")
        self.datatypes["Naturals"] = {
            "name": "Naturals", "predicate": "Nat",
            "constructors": [
                {"name": "zero", "arity": 0, "recursiveFields": []},
                {"name": "succ", "arity": 1, "recursiveFields": [0]},
            ],
        }

    def define_structural(self, options: dict[str, Any]) -> None:
        name, parameters = options["name"], options["parameters"]
        datatype, position, equations = options["datatype"], options["decreasingParameter"], options["equations"]
        self.fresh_name(name); self.parameters(parameters)
        data = self.datatypes.get(datatype)
        if data is None or not natural_int(position) or not 0 <= position < len(parameters) or len(equations) != len(data["constructors"]):
            fail("malformed structural recursion")
        seen: set[str] = set(); properties: dict[str, dict[str, Any]] = {}
        for equation_index, equation in enumerate(equations):
            patterns = equation["patterns"]
            if len(patterns) != len(parameters) or any(index != position and pattern.get("tag") != "bind" for index, pattern in enumerate(patterns)):
                fail("malformed recursive equation")
            root = patterns[position]
            ctor = next((item for item in data["constructors"] if item["name"] == root.get("name")), None)
            if root.get("tag") != "ctor" or ctor is None or len(root.get("args", [])) != ctor["arity"] or root["name"] in seen:
                fail("bad constructor coverage")
            for pattern in patterns: self.check_pattern(pattern)
            seen.add(root["name"])
            bindings = pattern_bindings(patterns)
            if len(set(bindings)) != len(bindings) or not free_term(equation["body"]) <= set(bindings): fail("bad recursive bindings")
            smaller: set[str] = set()
            for field in ctor["recursiveFields"]: smaller.update(pattern_bindings([root["args"][field]]))
            self.check_recursive_body(equation["body"], name, len(parameters), position, smaller)
            lhs = app(name, *(pattern_term(pattern) for pattern in patterns))
            properties[f"equation.{equation_index}"] = foralls(bindings, eq(lhs, equation["body"]))
        if len(seen) != len(data["constructors"]): fail("nonexhaustive recursion")
        self.functions[name] = len(parameters)
        self.recursive[name] = {"name": name, "parameters": list(parameters), "datatype": datatype,
                                "decreasingParameter": position, "equations": equations, "admission": "structural"}
        self.record_definition(name, "recursive", parameters, properties)

    def check_pattern(self, pattern: dict[str, Any]) -> None:
        if pattern.get("tag") == "bind":
            if not pattern.get("name"): fail("empty pattern variable")
            return
        ctor = next((item for data in self.datatypes.values() for item in data["constructors"] if item["name"] == pattern.get("name")), None)
        if pattern.get("tag") != "ctor" or ctor is None or len(pattern.get("args", [])) != ctor["arity"]: fail("bad constructor pattern")
        for child in pattern["args"]: self.check_pattern(child)

    def check_recursive_body(self, term: dict[str, Any], name: str, arity: int, position: int, smaller: set[str]) -> None:
        if term.get("tag") in ("var", "nat"):
            self.check_term(term); return
        if term.get("tag") != "app": fail("malformed recursive body")
        if term["fn"] == name:
            if len(term["args"]) != arity or term["args"][position].get("tag") != "var" or term["args"][position].get("name") not in smaller:
                fail("recursive call is not structurally smaller")
        elif self.functions.get(term["fn"]) != len(term["args"]): fail("unknown function in recursive body")
        for argument in term["args"]: self.check_recursive_body(argument, name, arity, position, smaller)

    def define_well_founded(self, options: dict[str, Any]) -> None:
        """Recursion along a proved well-founded relation on a measure; mirrors kernel.defineWellFoundedFunction."""
        name, parameters = options["name"], options["parameters"]
        datatype, position, equations = options["coverageDatatype"], options["coverageParameter"], options["equations"]
        relation, domain, measure = options["relation"], options["domain"], options["measure"]
        self.fresh_name(name); self.parameters(parameters)
        self.check_term(relation); self.check_term(domain); self.check_term(measure)
        if free_term(relation) or free_term(domain) or not free_term(measure) <= set(parameters):
            fail("undeclared variable in termination data")
        data = self.datatypes.get(datatype)
        if data is None or not natural_int(position) or not 0 <= position < len(parameters) or len(equations) != len(data["constructors"]):
            fail("malformed well-founded recursion")
        expected_well_founded = pred("wellFoundedOn", relation, domain)
        if not same_formula(check_proof(self, decode_proof_dag(options["wellFounded"])), expected_well_founded):
            fail("wrong well-foundedness proof")
        expected_measure = foralls(parameters, pred("in", measure, domain))
        if not same_formula(check_proof(self, decode_proof_dag(options["measureInDomain"])), expected_measure):
            fail("wrong measure-domain proof")
        seen: set[str] = set(); properties: dict[str, dict[str, Any]] = {}; obligations: list[dict[str, Any]] = []
        for equation_index, equation in enumerate(equations):
            patterns = equation["patterns"]
            if len(patterns) != len(parameters) or any(index != position and pattern.get("tag") != "bind" for index, pattern in enumerate(patterns)):
                fail("malformed recursive equation")
            root = patterns[position]
            ctor = next((item for item in data["constructors"] if item["name"] == root.get("name")), None)
            if root.get("tag") != "ctor" or ctor is None or len(root.get("args", [])) != ctor["arity"] or root["name"] in seen:
                fail("bad constructor coverage")
            for pattern in patterns: self.check_pattern(pattern)
            seen.add(root["name"])
            bindings = pattern_bindings(patterns)
            if len(set(bindings)) != len(bindings) or not free_term(equation["body"]) <= set(bindings): fail("bad recursive bindings")
            calls = collect_calls(equation["body"], name, len(parameters), self)
            current = [pattern_term(pattern) for pattern in patterns]
            current_measure = substitute_simultaneous(measure, dict(zip(parameters, current)))
            for call in calls:
                next_measure = substitute_simultaneous(measure, dict(zip(parameters, call["args"])))
                obligations.append(foralls(bindings, pred("relates", relation, next_measure, current_measure)))
            properties[f"equation.{equation_index}"] = foralls(bindings, eq(app(name, *current), equation["body"]))
        if len(seen) != len(data["constructors"]): fail("nonexhaustive recursion")
        decreases = options["decreases"]
        if len(decreases) != len(obligations): fail("wrong number of decrease proofs")
        for index, expected in enumerate(obligations):
            if not same_formula(check_proof(self, decode_proof_dag(decreases[index])), expected): fail("wrong decrease proof")
            properties[f"termination.decrease.{index}"] = expected
        self.functions[name] = len(parameters)
        self.recursive[name] = {"name": name, "parameters": list(parameters), "datatype": datatype,
                                "decreasingParameter": position, "equations": equations, "admission": "well-founded",
                                "termination": {"relation": relation, "domain": domain, "measure": measure}}
        properties["termination.wellFounded"] = expected_well_founded
        properties["termination.measure"] = expected_measure
        self.record_definition(name, "well-founded-recursive", parameters, properties)

    def reify_unary_operation(self, options: dict[str, Any]) -> None:
        """The graph of a declared unary operation on a domain; mirrors kernel.reifyUnaryOperation."""
        if not self.capabilities.get("replacement"): fail("foundation does not enable Replacement")
        name, operation, variable = options["name"], options["operation"], options["variable"]
        domain, codomain = options["domain"], options["codomain"]
        self.fresh_name(name)
        if self.functions.get(operation) != 1: fail("reified operation is not a declared unary function")
        self.check_term(domain); self.check_term(codomain)
        if free_term(domain) or free_term(codomain) or not variable: fail("malformed reified operation")
        expected = forall(variable, imp(pred("in", v(variable), domain), pred("in", app(operation, v(variable)), codomain)))
        if not same_formula(check_proof(self, decode_proof_dag(options["closure"])), expected): fail("wrong closure proof")
        self.functions[name] = 0
        graph = app(name)
        pair_variable = "pair_" if variable == "p" else "p"
        membership = forall(pair_variable, iff(pred("in", v(pair_variable), graph),
            exists(variable, conjunction(pred("in", v(variable), domain),
                eq(v(pair_variable), app("orderedPair", v(variable), app(operation, v(variable))))))))
        function_on = pred("functionOn", graph, domain, codomain)
        application = forall(variable, imp(pred("in", v(variable), domain),
            eq(app("apply", graph, v(variable)), app(operation, v(variable)))))
        self.record_definition(name, "replacement", [], {"membership": membership, "functionOn": function_on, "application": application})

    def define_unique(self, options: dict[str, Any]) -> None:
        """A function by unique description; mirrors kernel.defineUniqueFunction."""
        name, parameters, value, relation = options["name"], options["parameters"], options["value"], options["relation"]
        self.fresh_name(name); self.parameters(parameters); self.check_formula(relation)
        if not value or value in parameters or not free_formula(relation) <= {*parameters, value}: fail("malformed unique description")
        other = fresh(f"{value}_other", {*parameters, value, *free_formula(relation)})
        other_relation = substitute_formula(relation, value, v(other))
        expected = foralls(parameters, exists(value, conjunction(relation,
            forall(other, imp(other_relation, eq(v(other), v(value)))))))
        if not same_formula(check_proof(self, decode_proof_dag(options["existsUnique"])), expected): fail("wrong unique-existence proof")
        self.functions[name] = len(parameters)
        characterization = foralls(parameters, substitute_formula(relation, value, app(name, *(v(x) for x in parameters))))
        self.record_definition(name, "unique-choice", parameters, {"existsUnique": expected, "characterization": characterization})

    def define_replacement(self, options: dict[str, Any]) -> None:
        if not self.capabilities.get("replacement"): fail("foundation does not enable Replacement")
        name, parameters, domain = options["name"], options["parameters"], options["domain"]
        input_name, output, relation = options["input"], options["output"], options["relation"]
        self.parameters(parameters); self.fresh_name(name); self.check_term(domain); self.check_formula(relation)
        if input_name == output or input_name in parameters or output in parameters or name in functions_in_term(domain) or name in symbols_in_formula(relation):
            fail("malformed Replacement instance")
        if not free_term(domain) <= set(parameters) or not free_formula(relation) <= {*parameters, input_name, output}:
            fail("undeclared Replacement variable")
        unique = fresh(f"{output}_other", {*parameters, input_name, output, *free_formula(relation)})
        at_unique = substitute_formula(relation, output, v(unique))
        expected = foralls(parameters, forall(input_name, imp(pred("in", v(input_name), domain),
            exists(output, conjunction(relation, forall(unique, imp(at_unique, eq(v(unique), v(output)))))))))
        actual = check_proof(self, decode_proof_dag(options["functionality"]))
        if not same_formula(actual, expected): fail("wrong Replacement functionality proof")
        self.functions[name] = len(parameters)
        member = fresh("member", {*parameters, input_name, output, *free_formula(relation)})
        at_member = substitute_formula(relation, output, v(member))
        membership = foralls([*parameters, member], iff(
            pred("in", v(member), app(name, *(v(x) for x in parameters))),
            exists(input_name, conjunction(pred("in", v(input_name), domain), at_member))))
        self.record_definition(name, "replacement", parameters, {"functionality": expected, "membership": membership})

    def define_membership_recursion(self, options: dict[str, Any]) -> None:
        name, parameters = options["name"], options["parameters"]
        variable, predecessor, history, step = options["variable"], options["predecessor"], options["history"], options["step"]
        if not self.capabilities.get("separation") or not self.capabilities.get("replacement") or "set.foundation" not in self.axioms:
            fail("foundation does not enable membership recursion")
        self.fresh_name(name); self.fresh_name(f"{name}.history"); self.parameters(parameters)
        if not variable or not predecessor or not history or len(set([*parameters, variable, predecessor, history])) != len(parameters) + 3:
            fail("bad membership recursion variables")
        self.check_term(step)
        if not free_term(step) <= {*parameters, variable, history}: fail("bad membership recursion step")
        arity = len(parameters) + 1; history_name = f"{name}.history"
        self.functions[name] = arity; self.functions[history_name] = arity
        pair_name = fresh("pair", {*parameters, variable, predecessor, history})
        history_term = app(history_name, *(v(x) for x in parameters), v(variable))
        value_at_predecessor = app(name, *(v(x) for x in parameters), v(predecessor))
        membership = foralls([*parameters, variable, pair_name], iff(
            pred("in", v(pair_name), history_term),
            exists(predecessor, conjunction(pred("in", v(predecessor), v(variable)),
                eq(v(pair_name), app("orderedPair", v(predecessor), value_at_predecessor))))))
        value = app(name, *(v(x) for x in parameters), v(variable))
        equation = foralls([*parameters, variable], eq(value, substitute_many(step, {history: history_term})))
        self.record_definition(name, "membership-recursive", [*parameters, variable],
                               {"history.membership": membership, "equation": equation})

    def define_well_founded_set_function(self, options: dict[str, Any]) -> None:
        name, parameters = options["name"], options["parameters"]
        variable, predecessor, history = options["variable"], options["predecessor"], options["history"]
        domain, precedes, step = options["domain"], options["precedes"], options["step"]
        if not self.capabilities.get("separation") or not self.capabilities.get("replacement") or "set.foundation" not in self.axioms:
            fail("foundation does not enable set well-founded recursion")
        solution_name, history_name = f"{name}.Solution", f"{name}.history"
        self.fresh_name(name); self.fresh_name(solution_name); self.fresh_name(history_name); self.parameters(parameters)
        if (not variable or not predecessor or not history or
                len(set([*parameters, variable, predecessor, history])) != len(parameters) + 3):
            fail("bad set-recursion variables")
        self.check_term(domain); self.check_formula(precedes); self.check_term(step)
        if (not free_term(domain) <= set(parameters) or
                not free_formula(precedes) <= {*parameters, predecessor, variable} or
                not free_term(step) <= {*parameters, variable, history}):
            fail("undeclared set-recursion variable")

        forbidden = {*parameters, variable, predecessor, history,
                     *free_term(domain), *free_formula(precedes), *free_term(step)}
        subset = fresh("subset", forbidden); forbidden.add(subset)
        minimum = fresh("minimum", forbidden); forbidden.add(minimum)
        member = fresh("member", forbidden); forbidden.add(member)
        graph = fresh("graph", forbidden); forbidden.add(graph)
        other_graph = fresh("otherGraph", forbidden); forbidden.add(other_graph)
        output = fresh("output", forbidden); forbidden.add(output)
        other_output = fresh("otherOutput", forbidden); forbidden.add(other_output)

        def at_relation(earlier: dict[str, Any], later: dict[str, Any]) -> dict[str, Any]:
            return substitute_formula(substitute_formula(precedes, predecessor, earlier), variable, later)

        domain_subset = forall(member, imp(pred("in", v(member), v(subset)), pred("in", v(member), domain)))
        minimal = exists(minimum, conjunction(
            pred("in", v(minimum), v(subset)),
            forall(predecessor, imp(at_relation(v(predecessor), v(minimum)),
                                    neg(pred("in", v(predecessor), v(subset)))))))
        expected_well_founded = foralls(parameters, forall(subset, imp(
            domain_subset, imp(neg(eq(v(subset), app("empty"))), minimal))))
        actual_well_founded = check_proof(self, decode_proof_dag(options["wellFounded"]))
        if not same_formula(actual_well_founded, expected_well_founded):
            fail("wrong set-well-foundedness proof")

        def history_formula(graph_term: dict[str, Any], point: dict[str, Any],
                            history_term: dict[str, Any]) -> dict[str, Any]:
            pair_value = fresh("pairValue", forbidden)
            earlier = fresh("earlier", {*forbidden, pair_value})
            earlier_value = fresh("earlierValue", {*forbidden, pair_value, earlier})
            prior_pair = exists(earlier, exists(earlier_value, conjunction(
                pred("in", v(earlier), domain), conjunction(
                    at_relation(v(earlier), point),
                    eq(v(pair_value), app("orderedPair", v(earlier), v(earlier_value)))))))
            return forall(pair_value, iff(
                pred("in", v(pair_value), history_term),
                conjunction(pred("in", v(pair_value), graph_term), prior_pair)))

        graph_shape = conjunction(
            forall(member, imp(pred("in", v(member), v(graph)), exists(variable, exists(output, conjunction(
                pred("in", v(variable), domain),
                eq(v(member), app("orderedPair", v(variable), v(output)))))))),
            conjunction(
                forall(variable, imp(pred("in", v(variable), domain), exists(output,
                    pred("in", app("orderedPair", v(variable), v(output)), v(graph))))),
                forall(variable, imp(pred("in", v(variable), domain), forall(output, forall(other_output, imp(conjunction(
                    pred("in", app("orderedPair", v(variable), v(output)), v(graph)),
                    pred("in", app("orderedPair", v(variable), v(other_output)), v(graph))),
                    eq(v(output), v(other_output)))))))))
        instantiated_step = substitute_many(step, {variable: v(variable), history: v(history)})
        solution_body = conjunction(graph_shape, forall(variable, imp(pred("in", v(variable), domain),
            exists(history, exists(output, conjunction(
                history_formula(v(graph), v(variable), v(history)), conjunction(
                    pred("in", app("orderedPair", v(variable), v(output)), v(graph)),
                    eq(v(output), instantiated_step))))))))
        self.predicates[solution_name] = len(parameters) + 1
        solution_equation = foralls([*parameters, graph], iff(
            pred(solution_name, *(v(x) for x in parameters), v(graph)), solution_body))
        self.record_definition(solution_name, "predicate", [*parameters, graph], {"equation": solution_equation})

        solution_at = lambda graph_term: pred(solution_name, *(v(x) for x in parameters), graph_term)
        existence_unique = foralls(parameters, exists(graph, conjunction(
            solution_at(v(graph)), forall(other_graph, imp(solution_at(v(other_graph)), eq(v(other_graph), v(graph)))))))
        arity = len(parameters) + 1
        self.functions[name] = arity; self.functions[history_name] = arity
        value_term = app(name, *(v(x) for x in parameters), v(variable))
        history_term = app(history_name, *(v(x) for x in parameters), v(variable))
        value_at_predecessor = app(name, *(v(x) for x in parameters), v(predecessor))
        history_member = fresh("historyMember", forbidden)
        history_membership = foralls([*parameters, variable, history_member], iff(
            pred("in", v(history_member), history_term),
            exists(predecessor, conjunction(pred("in", v(predecessor), domain), conjunction(
                at_relation(v(predecessor), v(variable)),
                eq(v(history_member), app("orderedPair", v(predecessor), value_at_predecessor)))))))
        value_property = foralls([*parameters, variable], imp(pred("in", v(variable), domain), exists(graph, conjunction(
            solution_at(v(graph)), pred("in", app("orderedPair", v(variable), value_term), v(graph))))))
        equation_property = foralls([*parameters, variable], imp(pred("in", v(variable), domain),
            exists(graph, exists(history, conjunction(solution_at(v(graph)), conjunction(
                history_formula(v(graph), v(variable), v(history)),
                eq(value_term, instantiated_step)))))))
        direct_step = substitute_many(step, {variable: v(variable), history: history_term})
        direct_equation = foralls([*parameters, variable], imp(
            pred("in", v(variable), domain), eq(value_term, direct_step)))
        outside = foralls([*parameters, variable], imp(
            neg(pred("in", v(variable), domain)), eq(value_term, app("empty"))))
        self.record_definition(name, "well-founded-set-recursive", [*parameters, variable], {
            "wellFounded": expected_well_founded,
            "solution.existsUnique": existence_unique,
            "history.membership": history_membership,
            "value": value_property,
            "equation": equation_property,
            "equation.direct": direct_equation,
            "outside": outside,
        })

    def normalize_term(self, term: dict[str, Any], fuel: int = 10_000) -> dict[str, Any]:
        if fuel < 1: fail("definitional normalization exhausted")
        if term.get("tag") != "app": return term
        args = [self.normalize_term(arg, fuel - 1) for arg in term["args"]]
        constructor = any(term["fn"] == item["name"]
                          for datatype in self.datatypes.values()
                          for item in datatype["constructors"])
        body = None if constructor else self.bodies.get(term["fn"])
        if body is not None:
            instance = substitute_many(body["body"], dict(zip(body["parameters"], args)))
            return self.normalize_term(instance, fuel - 1)
        return app(term["fn"], *args)

    def expand_formula(self, formula: dict[str, Any], fuel: int = 10_000) -> dict[str, Any]:
        if fuel < 1: fail("definitional expansion exhausted")
        tag = formula["tag"]
        if tag == "bottom": return formula
        if tag == "eq": return eq(self.normalize_term(formula["left"]), self.normalize_term(formula["right"]))
        if tag == "pred":
            definition = self.definitions.get(formula["pred"])
            equation = dict(definition["properties"]).get("equation") if definition and definition["kind"] == "predicate" else None
            if equation is not None:
                parameters: list[str] = []; body = equation
                while body["tag"] == "forall": parameters.append(body["variable"]); body = body["body"]
                if body["tag"] == "iff" and len(parameters) == len(formula["args"]):
                    if body["left"].get("tag") == "pred" and body["left"].get("pred") == formula["pred"]: instance = body["right"]
                    elif body["right"].get("tag") == "pred" and body["right"].get("pred") == formula["pred"]: instance = body["left"]
                    else: instance = None
                    if instance is not None:
                        for parameter, argument in zip(parameters, formula["args"]):
                            instance = substitute_formula(instance, parameter, argument)
                        return self.expand_formula(instance, fuel - 1)
            return pred(formula["pred"], *(self.normalize_term(x) for x in formula["args"]))
        if tag in ("imp", "and", "or", "iff"):
            return binary(tag, self.expand_formula(formula["left"], fuel - 1), self.expand_formula(formula["right"], fuel - 1))
        return quantify(tag, formula["variable"], self.expand_formula(formula["body"], fuel - 1))

    def define_transfinite(self, options: dict[str, Any]) -> None:
        name, parameters = options["name"], options["parameters"]
        ordinal, predecessor, history = options["ordinal"], options["predecessor"], options["history"]
        zero, successor, limit = options["zero"], options["successor"], options["limit"]
        if not self.capabilities.get("separation") or not self.capabilities.get("replacement") or "set.foundation" not in self.axioms:
            fail("foundation does not enable transfinite recursion")
        self.fresh_name(name); self.fresh_name(f"{name}.history"); self.parameters(parameters)
        if not ordinal or not predecessor or not history or len(set([*parameters, ordinal, predecessor, history])) != len(parameters) + 3:
            fail("bad transfinite recursion variables")
        arity = len(parameters) + 1; self.functions[name] = arity
        self.check_term(zero); self.check_term(successor); self.check_term(limit)
        if not free_term(zero) <= set(parameters) or not free_term(successor) <= {*parameters, predecessor} or not free_term(limit) <= {*parameters, ordinal, history}:
            fail("bad transfinite clause variables")
        calls = lambda term: collect_calls(term, name, arity, self)
        if calls(zero) or calls(limit): fail("recursion outside successor clause")
        expected_call = [*(v(x) for x in parameters), v(predecessor)]
        if any(len(call["args"]) != len(expected_call) or any(not same_term(x, expected_call[i]) for i, x in enumerate(call["args"])) for call in calls(successor)):
            fail("transfinite recursion does not call immediate predecessor")
        successor_index = options.get("successorIndex")
        if successor_index:
            if self.functions.get(successor_index) != 1: fail("bad ordinal successor")
            probe = v(fresh("ordinalProbe", {*parameters, ordinal, predecessor, history}))
            if not same_term(self.normalize_term(app(successor_index, probe)),
                             self.normalize_term(app("union2", probe, app("singleton", probe)))): fail("noncanonical ordinal successor")
        next_term = lambda term: app(successor_index, term) if successor_index else app("union2", term, app("singleton", term))
        canonical_ordinal = von_neumann_ordinal(v(ordinal))
        canonical_limit = von_neumann_limit(v(ordinal), next_term)
        ordinal_condition, limit_condition = options.get("ordinalCondition"), options.get("limitCondition")
        if ordinal_condition is not None and (not free_formula(ordinal_condition) <= {ordinal} or
            not same_formula(self.expand_formula(ordinal_condition), self.expand_formula(canonical_ordinal))): fail("noncanonical ordinal interface")
        if limit_condition is not None and (not free_formula(limit_condition) <= {ordinal} or
            not same_formula(self.expand_formula(limit_condition), self.expand_formula(canonical_limit))): fail("noncanonical limit interface")
        ordinal_at = lambda term: substitute_formula(ordinal_condition, ordinal, term) if ordinal_condition else von_neumann_ordinal(term)
        limit_at = lambda term: substitute_formula(limit_condition, ordinal, term) if limit_condition else von_neumann_limit(term, next_term)
        history_name = f"{name}.history"; self.functions[history_name] = arity
        pair_name = fresh("pair", {*parameters, ordinal, predecessor, history})
        earlier = fresh("earlier", {*parameters, ordinal, predecessor, history, pair_name})
        history_term = app(history_name, *(v(x) for x in parameters), v(ordinal))
        history_membership = foralls([*parameters, ordinal, pair_name], iff(
            pred("in", v(pair_name), history_term), exists(earlier, conjunction(
                pred("in", v(earlier), v(ordinal)), eq(v(pair_name), app("orderedPair", v(earlier), app(name, *(v(x) for x in parameters), v(earlier))))))))
        value = lambda index: app(name, *(v(x) for x in parameters), index)
        properties = {
            "history.membership": history_membership,
            "equation.zero": foralls(parameters, eq(value(nat(0)), zero)),
            "equation.successor": foralls([*parameters, predecessor], imp(ordinal_at(v(predecessor)), eq(value(next_term(v(predecessor))), successor))),
            "equation.limit": foralls([*parameters, ordinal], imp(limit_at(v(ordinal)), eq(value(v(ordinal)), substitute_many(limit, {history: history_term})))),
            "outside": foralls([*parameters, ordinal], imp(neg(ordinal_at(v(ordinal))), eq(value(v(ordinal)), app("empty")))),
        }
        self.record_definition(name, "transfinite-recursive", [*parameters, ordinal], properties)


def construct_foundation(profile: str) -> KernelEnvironment:
    """Construct the normative foundation; never deserialize trusted maps."""
    env = KernelEnvironment.empty_foundation(profile)

    for name, arity in (
        ("empty", 0), ("pair", 2), ("union", 1), ("powerset", 1),
        ("omega", 0), ("apply", 2), ("epsilon0", 0),
    ):
        env.fresh_name(name)
        env.functions[name] = arity
    env.fresh_name("in")
    env.predicates["in"] = 2

    x, y, z = v("x"), v("y"), v("z")
    empty_membership = forall("x", neg(pred("in", x, app("empty"))))
    env.add_axiom("set.empty", empty_membership)

    pair_membership = forall("x", forall("y", forall("z", iff(
        pred("in", z, app("pair", x, y)), disjunction(eq(z, x), eq(z, y))))))
    env.add_axiom("set.pairing", pair_membership)

    extensionality = forall("x", forall("y", imp(
        forall("z", iff(pred("in", z, x), pred("in", z, y))), eq(x, y))))
    env.add_axiom("set.extensionality", extensionality)

    env.define_predicate({
        "name": "subset", "parameters": ["x", "y"],
        "body": forall("z", imp(pred("in", v("z"), v("x")), pred("in", v("z"), v("y")))),
    })
    env.add_axiom("set.union", forall("A", forall("x", iff(
        pred("in", v("x"), app("union", v("A"))),
        exists("y", conjunction(pred("in", v("y"), v("A")), pred("in", v("x"), v("y"))))))))
    powerset_membership = forall("x", forall("y", iff(
        pred("in", x, app("powerset", y)),
        forall("z", imp(pred("in", v("z"), x), pred("in", v("z"), y))))))
    env.add_axiom("set.powerset", powerset_membership)

    env.define_function({"name": "singleton", "parameters": ["x"], "body": app("pair", v("x"), v("x"))})
    env.define_function({"name": "union2", "parameters": ["x", "y"],
                         "body": app("union", app("pair", v("x"), v("y")))})
    env.define_function({"name": "orderedPair", "parameters": ["x", "y"],
                         "body": app("pair", app("pair", v("x"), v("x")),
                                     app("pair", v("x"), v("y")))})
    env.define_function({"name": "cons", "parameters": ["x", "y"],
                         "body": app("orderedPair", v("x"), v("y"))})
    env.define_function({"name": "zero", "parameters": [], "body": app("empty")})
    env.define_function({"name": "succ", "parameters": ["n"],
                         "body": app("union", app("pair", v("n"), app("pair", v("n"), v("n"))))})
    env.define_predicate({"name": "Nat", "parameters": ["n"],
                          "body": pred("in", v("n"), app("omega"))})
    env.define_predicate({"name": "relates", "parameters": ["r", "x", "y"],
                          "body": pred("in", app("orderedPair", v("x"), v("y")), v("r"))})

    function_on = conjunction(
        forall("x", imp(pred("in", v("x"), v("A")), exists("y", conjunction(
            pred("in", v("y"), v("B")), conjunction(
                pred("relates", v("f"), v("x"), v("y")),
                forall("z", imp(pred("relates", v("f"), v("x"), v("z")), eq(v("z"), v("y"))))))))),
        forall("p", imp(pred("in", v("p"), v("f")), exists("x", exists("y", conjunction(
            pred("in", v("x"), v("A")), conjunction(
                pred("in", v("y"), v("B")), eq(v("p"), app("orderedPair", v("x"), v("y"))))))))))
    env.define_predicate({"name": "functionOn", "parameters": ["f", "A", "B"], "body": function_on})
    env.add_axiom("function.apply", foralls(["f", "A", "B", "x", "y"], imp(
        conjunction(pred("functionOn", v("f"), v("A"), v("B")), conjunction(
            pred("in", v("x"), v("A")), pred("relates", v("f"), v("x"), v("y")))),
        eq(app("apply", v("f"), v("x")), v("y")))))

    env.add_axiom("set.infinity", conjunction(
        pred("in", app("empty"), app("omega")),
        forall("n", imp(pred("in", v("n"), app("omega")), pred("in",
            app("union", app("pair", v("n"), app("pair", v("n"), v("n")))), app("omega"))))))
    env.add_axiom("set.infinity.minimal", forall("A", imp(conjunction(
        pred("in", app("empty"), v("A")),
        forall("n", imp(pred("in", v("n"), v("A")), pred("in",
            app("union", app("pair", v("n"), app("pair", v("n"), v("n")))), v("A")))),
    ), forall("n", imp(pred("in", v("n"), app("omega")), pred("in", v("n"), v("A")))))))

    foundation = forall("x", imp(neg(eq(v("x"), app("empty"))), exists("y", conjunction(
        pred("in", v("y"), v("x")), forall("z", imp(
            pred("in", v("z"), v("y")), neg(pred("in", v("z"), v("x")))))))))
    env.add_axiom("set.foundation", foundation)

    env.define_predicate({"name": "wellFoundedOn", "parameters": ["r", "A"], "body":
        forall("s", imp(conjunction(pred("subset", v("s"), v("A")), neg(eq(v("s"), app("empty")))),
            exists("m", conjunction(pred("in", v("m"), v("s")), forall("y", imp(
                pred("in", v("y"), v("s")), neg(pred("relates", v("r"), v("y"), v("m")))))))))})
    env.define_predicate({"name": "E0Ordinal", "parameters": ["x"],
                          "body": pred("in", v("x"), app("epsilon0"))})

    if profile in ("ZFC", "ZFG"):
        env.add_axiom("set.choice", forall("A", imp(
            forall("x", imp(pred("in", v("x"), v("A")), exists("y", pred("in", v("y"), v("x"))))),
            exists("f", conjunction(
                pred("functionOn", v("f"), v("A"), app("union", v("A"))),
                forall("x", imp(pred("in", v("x"), v("A")),
                    pred("in", app("apply", v("f"), v("x")), v("x")))))))))
    if profile == "ZFG":
        env.fresh_name("choose")
        env.functions["choose"] = 1
        env.add_axiom("set.globalChoice", forall("A", imp(
            neg(eq(v("A"), app("empty"))), pred("in", app("choose", v("A")), v("A")))))

    env.register_natural_datatype()
    env.refresh_digest()
    return env


def load_foundation(value: str) -> KernelEnvironment:
    if value in ("ZF", "ZFC", "ZFG"):
        return construct_foundation(value)
    path = Path(value)
    document = json.loads(path.read_text("utf-8"))
    if document.get("format") == "grace17.foundation":
        if (set(document) != {"format", "version", "profile", "environment"} or
                document.get("version") != 1 or document.get("profile") not in ("ZF", "ZFC", "ZFG") or
                not isinstance(document.get("environment"), str) or not DIGEST.fullmatch(document["environment"])):
            fail("malformed foundation bootstrap")
        env = construct_foundation(document["profile"])
        if env.digest != document["environment"]:
            fail("foundation bootstrap produced the wrong environment")
        return env
    fail("G17C foundations must be checker-constructed; trusted .g17env snapshots are not accepted")


def functions_in_term(term: dict[str, Any]) -> set[str]:
    if term.get("tag") != "app": return set()
    return {term["fn"]} | set().union(*(functions_in_term(arg) for arg in term["args"])) if term["args"] else {term["fn"]}


def pattern_bindings(patterns: list[dict[str, Any]]) -> list[str]:
    result: list[str] = []
    def visit(pattern: dict[str, Any]) -> None:
        if pattern.get("tag") == "bind": result.append(pattern["name"])
        else:
            for child in pattern.get("args", []): visit(child)
    for pattern in patterns: visit(pattern)
    return result


def pattern_term(pattern: dict[str, Any]) -> dict[str, Any]:
    return v(pattern["name"]) if pattern.get("tag") == "bind" else app(pattern["name"], *(pattern_term(x) for x in pattern["args"]))


def collect_calls(term: dict[str, Any], name: str, arity: int, env: KernelEnvironment) -> list[dict[str, Any]]:
    if term.get("tag") in ("var", "nat"): return []
    if term.get("tag") != "app": fail("malformed recursive clause")
    result: list[dict[str, Any]] = []
    if term["fn"] == name:
        if len(term["args"]) != arity: fail("bad recursive call arity")
        result.append(term)
    elif env.functions.get(term["fn"]) != len(term["args"]): fail("unknown function in recursive clause")
    for argument in term["args"]: result.extend(collect_calls(argument, name, arity, env))
    return result


def von_neumann_transitive(term: dict[str, Any]) -> dict[str, Any]:
    member = fresh("member", free_term(term))
    element = fresh("element", {*free_term(term), member})
    return forall(member, imp(pred("in", v(member), term), forall(element,
        imp(pred("in", v(element), v(member)), pred("in", v(element), term)))))


def von_neumann_ordinal(term: dict[str, Any]) -> dict[str, Any]:
    member = fresh("ordinalMember", free_term(term))
    return conjunction(von_neumann_transitive(term), forall(member,
        imp(pred("in", v(member), term), von_neumann_transitive(v(member)))))


def von_neumann_limit(term: dict[str, Any], successor: Any) -> dict[str, Any]:
    member = fresh("limitMember", free_term(term))
    return conjunction(von_neumann_ordinal(term), conjunction(neg(eq(term, app("empty"))), forall(member,
        imp(pred("in", v(member), term), pred("in", successor(v(member)), term)))))


def symbols_in_formula(formula: dict[str, Any]) -> set[str]:
    tag = formula.get("tag")
    if tag == "eq": return functions_in_term(formula["left"]) | functions_in_term(formula["right"])
    if tag == "pred": return {formula["pred"]} | set().union(*(functions_in_term(x) for x in formula["args"]))
    if tag in ("imp", "and", "or", "iff"): return symbols_in_formula(formula["left"]) | symbols_in_formula(formula["right"])
    if tag in ("forall", "exists"): return symbols_in_formula(formula["body"])
    return set()


def decode_proof_dag(wrapper: dict[str, Any]) -> dict[str, Any]:
    if set(wrapper) != {"$grace17ProofDag"}: fail("malformed encoded proof")
    dag = wrapper["$grace17ProofDag"]
    body = {"version": dag.get("version"), "nodes": dag.get("nodes"), "root": dag.get("root")}
    if dag.get("version") != 1 or hashlib.sha256(canonical(body).encode()).hexdigest() != dag.get("digest"):
        fail("malformed or corrupted proof DAG")
    nodes = dag.get("nodes")
    if not isinstance(nodes, list) or not isinstance(dag.get("root"), int) or not 0 <= dag["root"] < len(nodes):
        fail("malformed proof DAG")
    decoded: list[dict[str, Any]] = []

    def value(item: Any, current: int) -> Any:
        if isinstance(item, dict) and set(item) == {"$proof"}:
            reference = item["$proof"]
            if not isinstance(reference, int) or not 0 <= reference < current: fail("forward proof DAG reference")
            return decoded[reference]
        if isinstance(item, list): return [value(child, current) for child in item]
        if isinstance(item, dict): return {key: value(child, current) for key, child in item.items()}
        return item

    for index, node in enumerate(nodes):
        if not isinstance(node, dict) or set(node) != {"payload"}: fail("malformed proof DAG node")
        proof = value(node["payload"], index)
        if not isinstance(proof, dict) or not isinstance(proof.get("rule"), str): fail("malformed proof DAG proof")
        decoded.append(proof)
    return decoded[dag["root"]]


def check_ast_computation(env: KernelEnvironment, left: dict[str, Any], right: dict[str, Any], definitions: list[str]) -> None:
    if definitions != sorted(set(definitions)): fail("bad computation dependency list")
    left_eval = machine.Evaluator(env, set(definitions))
    right_eval = machine.Evaluator(env, set(definitions))
    if left_eval.evaluate(left) != right_eval.evaluate(right): fail("computed terms differ")
    if sorted(left_eval.used | right_eval.used) != definitions: fail("inexact computation dependency list")


def check_proof(env: KernelEnvironment, proof: dict[str, Any], assumptions: list[dict[str, Any]] | None = None) -> dict[str, Any]:
    assumptions = [] if assumptions is None else assumptions
    rule = proof.get("rule")
    if rule == "assumption":
        formula = proof["formula"]; env.check_formula(formula)
        if not any(same_formula(formula, item) for item in assumptions): fail("inactive assumption")
        return formula
    if rule == "axiom":
        if proof.get("name") not in env.axioms: fail("unknown axiom")
        return env.axioms[proof["name"]]
    if rule == "theorem":
        if proof.get("name") not in env.theorems: fail("unknown theorem")
        return env.theorems[proof["name"]]
    if rule == "definition":
        formula = env.property(proof.get("name"), proof.get("property", "equation"))
        if formula is None: fail("unknown definition property")
        return formula
    if rule == "refl":
        env.check_term(proof["term"]); return eq(proof["term"], proof["term"])
    if rule == "compute":
        env.check_term(proof["left"]); env.check_term(proof["right"])
        check_ast_computation(env, proof["left"], proof["right"], proof["definitions"])
        return eq(proof["left"], proof["right"])
    if rule == "rationalClassCompute":
        env.check_term(proof["left"]); env.check_term(proof["right"])
        machine.check_rational_class_equality(env, proof["left"], proof["right"])
        return eq(proof["left"], proof["right"])
    if rule == "symm":
        formula = check_proof(env, proof["proof"], assumptions)
        if formula["tag"] != "eq": fail("symmetry needs equality")
        return eq(formula["right"], formula["left"])
    if rule == "trans":
        left = check_proof(env, proof["left"], assumptions); right = check_proof(env, proof["right"], assumptions)
        if left["tag"] != "eq" or right["tag"] != "eq" or not same_term(left["right"], right["left"]): fail("bad transitivity")
        return eq(left["left"], right["right"])
    if rule == "congr":
        proofs = [check_proof(env, item, assumptions) for item in proof["proofs"]]
        if env.functions.get(proof.get("fn")) != len(proofs) or any(item["tag"] != "eq" for item in proofs): fail("bad congruence")
        return eq(app(proof["fn"], *(item["left"] for item in proofs)), app(proof["fn"], *(item["right"] for item in proofs)))
    if rule == "impIntro":
        env.check_formula(proof["assumption"])
        return imp(proof["assumption"], check_proof(env, proof["body"], [*assumptions, proof["assumption"]]))
    if rule == "impElim":
        implication = check_proof(env, proof["implication"], assumptions)
        argument = check_proof(env, proof["argument"], assumptions)
        if implication["tag"] != "imp" or not same_formula(implication["left"], argument): fail("bad implication elimination")
        return implication["right"]
    if rule == "forallIntro":
        variable = proof["variable"]
        if any(variable in free_formula(item) for item in assumptions): fail("generalized variable is free in assumptions")
        return forall(variable, check_proof(env, proof["body"], assumptions))
    if rule == "forallElim":
        universal = check_proof(env, proof["universal"], assumptions); env.check_term(proof["term"])
        if universal["tag"] != "forall": fail("universal elimination needs a universal")
        return substitute_formula(universal["body"], universal["variable"], proof["term"])
    if rule == "eqElim":
        equality = check_proof(env, proof["equality"], assumptions)
        evidence = check_proof(env, proof["evidence"], assumptions); motive = proof["motive"]
        if equality["tag"] != "eq": fail("equality elimination needs equality")
        source, target = (equality["right"], equality["left"]) if proof.get("reverse") else (equality["left"], equality["right"])
        if not same_formula(evidence, substitute_formula(motive, proof["variable"], source)): fail("bad equality evidence")
        return substitute_formula(motive, proof["variable"], target)
    if rule == "andIntro":
        return conjunction(check_proof(env, proof["left"], assumptions), check_proof(env, proof["right"], assumptions))
    if rule in ("andElimLeft", "andElimRight"):
        value = check_proof(env, proof["conjunction"], assumptions)
        if value["tag"] != "and": fail("conjunction elimination needs conjunction")
        return value["left" if rule == "andElimLeft" else "right"]
    if rule == "orIntroLeft":
        env.check_formula(proof["right"]); return disjunction(check_proof(env, proof["proof"], assumptions), proof["right"])
    if rule == "orIntroRight":
        env.check_formula(proof["left"]); return disjunction(proof["left"], check_proof(env, proof["proof"], assumptions))
    if rule == "orElim":
        value = check_proof(env, proof["disjunction"], assumptions)
        if value["tag"] != "or": fail("or elimination needs disjunction")
        left = check_proof(env, proof["left"], [*assumptions, value["left"]])
        right = check_proof(env, proof["right"], [*assumptions, value["right"]])
        if not same_formula(left, right): fail("or branches disagree")
        return left
    if rule == "iffIntro":
        forward = check_proof(env, proof["forward"], assumptions); backward = check_proof(env, proof["backward"], assumptions)
        if forward["tag"] != "imp" or backward["tag"] != "imp" or not same_formula(forward["left"], backward["right"]) or not same_formula(forward["right"], backward["left"]): fail("bad iff introduction")
        return iff(forward["left"], forward["right"])
    if rule in ("iffElimLeft", "iffElimRight"):
        value = check_proof(env, proof["equivalence"], assumptions)
        if value["tag"] != "iff": fail("iff elimination needs equivalence")
        return imp(value["left"], value["right"]) if rule == "iffElimLeft" else imp(value["right"], value["left"])
    if rule == "existsIntro":
        env.check_formula(proof["body"]); env.check_term(proof["witness"])
        expected = substitute_formula(proof["body"], proof["variable"], proof["witness"])
        if not same_formula(check_proof(env, proof["evidence"], assumptions), expected): fail("bad existential witness")
        return exists(proof["variable"], proof["body"])
    if rule == "existsElim":
        existential = check_proof(env, proof["existential"], assumptions)
        if existential["tag"] != "exists": fail("existential elimination needs existential")
        witness = proof["witness"]
        instance = substitute_formula(existential["body"], existential["variable"], v(witness))
        result = check_proof(env, proof["body"], [*assumptions, instance])
        if witness in free_formula(result) or any(witness in free_formula(item) for item in assumptions) or witness in free_formula(existential): fail("existential witness escapes")
        return result
    if rule == "falseElim":
        absurdity = check_proof(env, proof["absurdity"], assumptions)
        if absurdity["tag"] != "bottom": fail("false elimination needs bottom")
        env.check_formula(proof["conclusion"]); return proof["conclusion"]
    if rule == "dne":
        proposition = proof["proposition"]; env.check_formula(proposition)
        expected = neg(neg(proposition))
        if not same_formula(check_proof(env, proof["proof"], assumptions), expected): fail("bad DNE")
        return proposition
    fail(f"unsupported proof DAG rule: {rule}")


def program_from_json(value: dict[str, Any]) -> machine.Program:
    try:
        program = machine.Program(value["environment"], value["symbols"], value["terms"], value["formulas"],
                                  value["contexts"], value["code"], value["root"], value["theorems"])
    except (KeyError, TypeError) as error:
        raise CheckError("malformed embedded G17M program") from error
    if value.get("version") != machine.VERSION: fail("unsupported embedded G17M version")
    machine.validate_program(program)
    return program


def validate_module(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("format") != "grace17.compiled-module" or value.get("version") != 3:
        fail("unsupported G17C module")
    digest = value.get("digest")
    if not isinstance(digest, str) or not DIGEST.fullmatch(digest):
        fail("malformed G17C digest")
    body = {key: item for key, item in value.items() if key != "digest"}
    if hashlib.sha256(canonical(body).encode("utf-8")).hexdigest() != digest:
        fail("corrupted G17C module digest")
    if (not isinstance(value.get("module"), str) or not value["module"] or not isinstance(value.get("events"), list) or
        not isinstance(value.get("source"), str) or value["source"] and not DIGEST.fullmatch(value["source"]) or
        not DIGEST.fullmatch(str(value.get("baseEnvironment", ""))) or
        not DIGEST.fullmatch(str(value.get("resultEnvironment", "")))):
        fail("malformed G17C envelope")
    dependencies = value.get("dependencies")
    if (not isinstance(dependencies, list) or any(not isinstance(item, dict) or not isinstance(item.get("module"), str) or
        not item["module"] or not isinstance(item.get("digest"), str) or not DIGEST.fullmatch(item["digest"]) for item in dependencies) or
        len({item["module"] for item in dependencies}) != len(dependencies)):
        fail("malformed G17C dependencies")
    return value


def replay_admission(env: KernelEnvironment, event: dict[str, Any]) -> None:
    operation, payload = event.get("operation"), event.get("payload")
    if not isinstance(payload, dict): fail("malformed G17C admission")
    if operation == "declareFunction":
        env.fresh_name(payload["name"])
        if not natural_int(payload["arity"]): fail("bad function arity")
        env.functions[payload["name"]] = payload["arity"]
    elif operation == "declarePredicate":
        env.fresh_name(payload["name"])
        if not natural_int(payload["arity"]): fail("bad predicate arity")
        env.predicates[payload["name"]] = payload["arity"]
    elif operation == "defineFunction": env.define_function(payload)
    elif operation == "definePredicate": env.define_predicate(payload)
    elif operation == "defineSubset": env.define_subset(payload)
    elif operation == "declareDatatype": env.declare_datatype(payload["spec"])
    elif operation == "registerNaturalDatatype": env.register_natural_datatype()
    elif operation == "defineStructuralFunction": env.define_structural(payload["options"])
    elif operation == "defineReplacement": env.define_replacement(payload["options"])
    elif operation == "defineWellFoundedFunction": env.define_well_founded(payload["options"])
    elif operation == "reifyUnaryOperation": env.reify_unary_operation(payload["options"])
    elif operation == "defineUniqueFunction": env.define_unique(payload["options"])
    elif operation == "defineMembershipRecursiveFunction": env.define_membership_recursion(payload["options"])
    elif operation == "defineWellFoundedSetFunction": env.define_well_founded_set_function(payload["options"])
    elif operation == "defineTransfiniteFunction": env.define_transfinite(payload["options"])
    else:
        fail(f"unsupported G17C admission operation: {operation}")


def replay_module(env: KernelEnvironment, document: dict[str, Any]) -> None:
    module = validate_module(document)
    foundation = module.get("foundation")
    if not isinstance(foundation, dict) or foundation.get("profile") != env.capabilities.get("setTheory") or foundation.get("environment") != FOUNDATION_DIGEST:
        fail("G17C foundation mismatch")
    for dependency in module["dependencies"]:
        if env.receipts.get(dependency.get("module")) != dependency.get("digest"):
            fail(f"missing or stale G17C dependency {dependency.get('module')}")
    if env.digest != module.get("baseEnvironment"):
        fail("G17C exact dependency-prefix mismatch")
    for event_index, item in enumerate(module["events"]):
        if item.get("kind") == "admission":
            replay_admission(env, item["event"])
        elif item.get("kind") == "theoremBatch":
            statements = item.get("statements")
            if not isinstance(statements, list) or not statements: fail("malformed theorem batch")
            expected: dict[str, dict[str, Any]] = {}
            for statement in statements:
                name, formula = statement.get("name"), statement.get("statement")
                if not isinstance(name, str) or not name or name in expected or name in env.axioms or name in env.theorems:
                    fail("duplicate theorem boundary")
                env.check_formula(formula)
                if free_formula(formula): fail("theorem statement is not closed")
                expected[name] = formula
            program = program_from_json(item["machine"])
            # The containing authenticated G17C event order and final digest
            # bind the live environment. As in the TypeScript kernel, embedded
            # batches therefore avoid a quadratic whole-environment hash here.
            machine.verify(program, env, False, expected)
            if {program.symbols[name] for name, _ in program.theorems} != set(expected): fail("theorem boundary set mismatch")
            env.theorems.update(expected)
        else:
            fail("unknown G17C event")
    env.refresh_digest()
    if env.digest != module.get("resultEnvironment"):
        fail("G17C result-environment mismatch")
    env.receipts[module["module"]] = module["digest"]
    env.results[module["module"]] = module["resultEnvironment"]


FOUNDATION_DIGEST = ""


def main() -> int:
    parser = argparse.ArgumentParser(description="Independently check a strict GRACE17 G17C v3 module")
    parser.add_argument("certificate", type=Path, help="G17C compiled-module file (.g17c)")
    parser.add_argument("--foundation", required=True,
                        help="checker-constructed ZF, ZFC, or ZFG profile (or a tiny .g17f receipt)")
    parser.add_argument("--dependency", action="append", default=[], type=Path,
                        help="a dependency G17C artifact; repeat as needed")
    parser.add_argument("--json", action="store_true", help="print a JSON report instead of plain text")
    parser.add_argument("--fuel", type=int, default=machine.FUEL, metavar="STEPS",
                        help=f"ground evaluation steps per computation (default {machine.FUEL})")
    args = parser.parse_args()
    if args.fuel < 1: parser.error("--fuel must be positive")
    machine.FUEL = args.fuel
    try:
        env = load_foundation(args.foundation)
        global FOUNDATION_DIGEST
        FOUNDATION_DIGEST = env.digest
        root = validate_module(json.loads(args.certificate.read_text("utf-8")))
        supplied = [validate_module(json.loads(path.read_text("utf-8"))) for path in args.dependency]
        by_digest = {item["digest"]: item for item in supplied}
        for dependency in root["dependencies"]:
            artifact = by_digest.get(dependency["digest"])
            if artifact is None or artifact["module"] != dependency["module"]:
                fail(f"missing dependency artifact {dependency['module']}")
            replay_module(env, artifact)
        replay_module(env, root)
        result = {"ok": True, "checker": "grace17-python-g17c", "version": 3,
                  "module": root["module"], "events": len(root["events"]),
                  "theorems": len(env.theorems), "environment": env.digest}
        print(json.dumps(result, separators=(",", ":")) if args.json else
              f"checked {root['module']} ({len(root['events'])} events)")
        return 0
    except (CheckError, OSError, ValueError, KeyError, TypeError, json.JSONDecodeError) as error:
        result = {"ok": False, "checker": "grace17-python-g17c", "message": str(error)}
        print(json.dumps(result, separators=(",", ":")) if args.json else f"check failed: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
