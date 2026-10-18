#!/usr/bin/env python3
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore

"""Report every failing theorem of a module in one run.

The checker stops at the first failing proof. This script works on a scratch
copy: after each failure it replaces that theorem's proof by `sorry` and
checks again, so one run lists the first error of every theorem together with
the goal that remained. The file given is never modified.

    python3 scripts/all-errors.py lib/Grace/Cumulus/Real/PowerSums.g17
    python3 scripts/all-errors.py --module-root lib path/to/Draft.g17

Run it from the repository root. A draft outside the module roots is checked
as a standalone file; its imports still resolve against the roots.
"""
import os
import re
import shutil
import subprocess
import sys

args = sys.argv[1:]
roots = []
while "--module-root" in args:
    index = args.index("--module-root")
    roots.append(args[index + 1])
    del args[index:index + 2]
if len(args) != 1:
    print(__doc__)
    sys.exit(2)
roots = roots or ["lib"]
path = args[0]
original = open(path, encoding="utf8").read()

# The modified text is checked at the file's own path, so that a bare
# `module Name` keeps its place under the module root; the original text is
# kept in a backup beside it and restored whatever happens.
backup = os.path.join(os.path.dirname(os.path.abspath(path)), f".{os.path.basename(path)}.all-errors.bak")
shutil.copyfile(path, backup)
scratch = path
lines = original.split("\n")
errors = []
try:
    for _ in range(80):
        with open(scratch, "w", encoding="utf8") as out:
            out.write("\n".join(lines))
        command = ["node", "--disable-warning=ExperimentalWarning", "bin/g17.ts", "check"]
        for root in roots:
            command += ["--module-root", root]
        result = subprocess.run(command + [scratch], capture_output=True, text=True)
        output = result.stdout + result.stderr
        match = re.search(r"surface error: line (\d+): (.*)", output)
        if not match:
            break
        number, message = int(match.group(1)), match.group(2)
        start = number - 1
        while start > 0 and not re.match(r"^(theorem|lemma|def|defgraph|defunique|defchoose|predicate|instance)\b", lines[start]):
            start -= 1
        if not re.match(r"^(theorem|lemma)\b", lines[start]):
            errors.append((number, message, "(not in a theorem)", ""))
            break
        name = lines[start].split()[1]
        goal = re.search(r"\n(  \d+\. ⊢ [^\n]*)", output)
        errors.append((number, message, name, goal.group(1).strip() if goal else ""))
        cursor = start
        while cursor < len(lines) and lines[cursor].strip() != "proof":
            cursor += 1
        end = cursor + 1
        while end < len(lines) and (lines[end].startswith(" ") or lines[end] == ""):
            if lines[end] == "" and end + 1 < len(lines) and not lines[end + 1].startswith(" "):
                break
            end += 1
        lines[cursor + 1:end] = ["  sorry"]
finally:
    with open(path, "w", encoding="utf8") as out:
        out.write(original)
    if os.path.exists(backup):
        os.remove(backup)
for number, message, name, goal in errors:
    print(f"line {number} [{name}]: {message}" + (f"\n      {goal}" if goal else ""))
print(len(errors), "failures")
