#!/usr/bin/env python3
# Integration harness for the OCaml checkers; the checkers themselves never invoke Python.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Integration tests; neither OCaml checker invokes this Python harness."""
import copy
import hashlib
import json
from pathlib import Path
import random
import subprocess
import sys
import time

root = Path(__file__).resolve().parents[2]
fixtures = root / 'build/ocaml-fixtures'
checker = root / 'build/ocaml/g17check'
modules = root / 'build/ocaml/g17c_check'
units = root / 'build/ocaml/checker_tests'
checks = 0


def run(args, expected=0, contains=None):
    global checks
    result = subprocess.run([str(x) for x in args], cwd=root, text=True, capture_output=True, timeout=120)
    assert result.returncode == expected, (args, result.returncode, result.stdout, result.stderr)
    if contains:
        assert contains.lower() in result.stderr.lower(), (args, contains, result.stderr)
    checks += 1
    return result.stdout


def canonical(value):
    if isinstance(value, dict):
        keys = sorted(value, key=lambda s: s.encode('utf-16-be'))
        return '{' + ','.join(json.dumps(k, ensure_ascii=False) + ':' + canonical(value[k]) for k in keys) + '}'
    if isinstance(value, list):
        return '[' + ','.join(map(canonical, value)) + ']'
    return json.dumps(value, ensure_ascii=False, separators=(',', ':'))


def redigest(document):
    document = copy.deepcopy(document)
    document.pop('digest', None)
    document['digest'] = hashlib.sha256(canonical(document).encode()).hexdigest()
    return document


def save(name, value):
    path = fixtures / name
    path.write_text(canonical(value))
    return path


for profile in ('ZF', 'ZFC', 'ZFG'):
    for foundation in (profile, fixtures / f'{profile}.g17f'):
        run([modules, fixtures / f'{profile}.g17c', '--foundation', foundation])
run([modules, fixtures / 'Admissions.g17c', '--foundation', 'ZFG'])
run([units, 'admission', fixtures / 'unit-admission.json'])
print('All foundation profiles, unique description, graph reification, and well-founded admission checked.', flush=True)

rng = random.Random(170143)
cases = []
for a, b in [(0, 0), (1, 0), (0, 1), (10**500 - 1, 1), (10**500, 10**500 - 1)] + [
    (rng.randrange(10**rng.randrange(1, 280)), rng.randrange(10**rng.randrange(1, 280))) for _ in range(250)
]:
    cases.append({'a': str(a), 'b': str(b), 'add': str(a+b), 'mul': str(a*b), 'sub': str(max(0, a-b))})
run([units, 'arithmetic', save('arithmetic-values.json', cases)])
for name in ('huge', 'factorial', 'shifted', 'stack', 'advance'):
    run([checker, fixtures / f'{name}.g17m', '--environment', fixtures / 'Computation.g17env'])
    run([checker, fixtures / f'{name}-incorrect.g17m', '--environment', fixtures / 'Computation.g17env'], 1, 'different computed normal forms')
print('255 arithmetic reference cases and the 5 computation examples (correct and incorrect conclusions) checked.', flush=True)

admission = json.loads((fixtures / 'Admissions.g17c').read_text())

def changed_event(operation, transform):
    document = copy.deepcopy(admission)
    event = next(x['event'] for x in document['events'] if x['kind'] == 'admission' and x['event']['operation'] == operation)
    transform(event['payload'])
    return save('invalid-declaration.g17c', redigest(document))

path = changed_event('defineUniqueFunction', lambda p: p['options']['relation'].update(right={'tag':'app','fn':'omega','args':[]}))
run([modules, path, '--foundation', 'ZFG'], 1, 'wrong conclusion')
path = changed_event('reifyUnaryOperation', lambda p: p['options'].update(codomain={'tag':'app','fn':'empty','args':[]}))
run([modules, path, '--foundation', 'ZFG'], 1, 'wrong conclusion')
path = changed_event('defineStructuralFunction', lambda p: p['options']['equations'][1].update(body={
    'tag':'app','fn':'plus','args':[{'tag':'app','fn':'succ','args':[{'tag':'var','name':'x'}]},{'tag':'var','name':'y'}]}))
run([modules, path, '--foundation', 'ZFG'], 1, 'nondecreasing')
path = changed_event('defineStructuralFunction', lambda p: p['options']['equations'][0].update(body={'tag':'var','name':'undeclared'}))
run([modules, path, '--foundation', 'ZFG'], 1, 'undeclared')

# A local assumption is not an exported theorem, including through a citation.
for linked in (False, True):
    document = copy.deepcopy(admission)
    code = [[0,0,0,0,0]] + ([[2,0,1,0,0]] if linked else [])
    machine = {'version':4,'environment':document['baseEnvironment'],'symbols':['invalid.false'],
               'terms':[],'formulas':[[0]],'contexts':[[0],[]],'code':code,'root':len(code)-1,'theorems':[[0,0]]}
    document['events'] = [{'kind':'theoremBatch','machine':machine,'statements':[{'name':'invalid.false','statement':{'tag':'bottom'}}]}]
    run([modules, save('open-theorem.g17c', redigest(document)), '--foundation', 'ZFG'], 1, 'empty contexts')
print('Six incorrect declaration/proof obligations rejected for their logical side conditions.', flush=True)

if '--cumulus' in sys.argv:
    compiled = root / 'build/compiled'
    certificate = compiled / 'Cumulus.g17c'
    bootstrap = compiled / 'Bootstrap.g17c'
    started = time.monotonic()
    report = json.loads(run([modules, certificate, '--foundation', 'ZFG', '--dependency', bootstrap, '--json']))
    module_seconds = time.monotonic() - started
    document = json.loads(certificate.read_text())
    assert report['environment'] == document['resultEnvironment']
    started = time.monotonic()
    run([checker, root / 'build/Cumulus.g17m', '--environment', root / 'build/Cumulus.g17env'])
    machine_seconds = time.monotonic() - started
    environment = json.loads((root / 'build/Cumulus.g17env').read_text())
    assert report['environment'] == environment['digest']
    run([modules, certificate, '--foundation', 'ZFG'], 1, 'missing artifact')
    # A transfinite recursive call must be at the immediate predecessor.
    wrong = copy.deepcopy(document)
    event = next(x['event'] for x in wrong['events'] if x['kind']=='admission' and x['event']['operation']=='defineTransfiniteFunction')
    options = event['payload']['options']
    options['successor'] = {'tag':'app','fn':options['name'],'args':[
        *[{'tag':'var','name':n} for n in options['parameters']],
        {'tag':'app','fn':'succ','args':[{'tag':'var','name':options['predecessor']}]}]}
    run([modules, save('invalid-transfinite.g17c', redigest(wrong)), '--foundation', 'ZFG', '--dependency', bootstrap], 1, 'non-predecessor')
    print(f'Cumulus: {report["events"]} G17C events, exact environment {report["environment"]}; G17C {module_seconds:.3f}s, G17M {machine_seconds:.3f}s.', flush=True)
print(f'OCaml integration: {checks} command checks passed.', flush=True)
