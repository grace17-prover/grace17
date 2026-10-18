#!/usr/bin/env python3
# Run the language-neutral G17M conformance corpus with the Python checker.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Run the language-neutral G17M conformance corpus with the Python checker."""

import hashlib
import json
from pathlib import Path
import sys

from g17check import CheckError, Environment, decode, verify


def checksum(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    root = Path(__file__).resolve().parents[2]
    directory = root / "conformance"
    manifest = json.loads((directory / "manifest.json").read_text(encoding="utf-8"))
    if (manifest.get("format") != "grace17.conformance" or manifest.get("version") != 1 or manifest.get("g17m_version") != 4):
        raise ValueError("unsupported conformance manifest")
    environment_path = directory / manifest["environment"]["file"]
    if checksum(environment_path) != manifest["environment"]["sha256"]:
        raise ValueError("conformance environment checksum mismatch")
    environment = Environment(environment_path)
    if environment.digest != manifest["logical_environment_digest"]:
        raise ValueError("conformance logical environment digest mismatch")

    failures = []
    for vector in manifest["vectors"]:
        certificate = directory / vector["certificate"]
        if checksum(certificate) != vector["sha256"]:
            raise ValueError(f"checksum mismatch: {vector['id']}")
        accepted = False
        try:
            verify(decode(certificate), environment)
            accepted = True
        except (CheckError, OSError, ValueError, KeyError, TypeError, UnicodeError):
            accepted = False
        if accepted != (vector["expected"] == "accept"):
            failures.append(f"{vector['id']}: expected {vector['expected']}, checker {'accepted' if accepted else 'rejected'}")
    if failures:
        print("\n".join(failures), file=sys.stderr)
        return 1
    print(f"Python checker passed {len(manifest['vectors'])} conformance vectors")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
