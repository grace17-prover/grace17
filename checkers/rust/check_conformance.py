#!/usr/bin/env python3
# Test harness only; the Rust checker does not invoke Python.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Run the Rust G17M checker over the conformance corpus and three
authentication mutations. The checker binary is built by `npm run
build:rust` into build/rust/."""
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
manifest = json.loads((root / 'conformance/manifest.json').read_text())
env = root / 'conformance' / manifest['environment']['file']
assert hashlib.sha256(env.read_bytes()).hexdigest() == manifest['environment']['sha256']
checker = root / 'build/rust/g17check'
counts = {'accept': 0, 'reject': 0, 'unsupported': 0}
for vector in manifest['vectors']:
    path = root / 'conformance' / vector['certificate']
    assert hashlib.sha256(path.read_bytes()).hexdigest() == vector['sha256']
    result = subprocess.run([str(checker), str(path), '--environment', str(env)], capture_output=True, text=True)
    expected = 0 if vector['expected'] == 'accept' else 1
    assert result.returncode == expected, (vector['id'], result.stdout, result.stderr)
    counts[vector['expected']] += 1
assert counts == {'accept': 30, 'reject': 36, 'unsupported': 0}, counts
positive = next(v for v in manifest['vectors'] if v['expected'] == 'accept')
data = bytearray((root / 'conformance' / positive['certificate']).read_bytes())
with tempfile.TemporaryDirectory() as directory:
    path = Path(directory) / 'bad.g17m'
    for damaged in (bytes(data[:-1]), bytes(data) + b'junk', bytes([data[0] ^ 1]) + bytes(data[1:])):
        path.write_bytes(damaged)
        result = subprocess.run([str(checker), str(path), '--environment', str(env)], capture_output=True)
        assert result.returncode == 1
print(f'Rust: {counts["accept"]} accepted, {counts["reject"]} rejected, {counts["unsupported"]} unsupported; 3 authentication mutations rejected')
