#!/usr/bin/env python3
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
"""Check that every documentation page quotes current source and resolves local links."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
docs = sorted((root / 'docs').glob('*.md'))
total = 0
for doc in docs:
    text = doc.read_text()
    excerpts = re.findall(r'<!-- cumulus-source: ([^\n]+) -->\n```g17\n(.*?)\n```', text, re.S)
    if doc.name == 'introduction.md':
        assert excerpts, 'No mathematical tour excerpts found'
    for source, excerpt in excerpts:
        assert excerpt in (root / source).read_text(), f'Source excerpt drift in {doc.name}: {source}'
    total += len(excerpts)
    # Local links are checked on the introduction; the site build resolves
    # the other pages' links, some of which point at generated pages.
    links = re.findall(r'\]\(([^)]+)\)', text) if doc.name == 'introduction.md' else []
    for target in links:
        if '://' not in target and not target.startswith('#'):
            path = target.split('#')[0].split(' "')[0]  # an image link may carry a quoted title
            assert (doc.parent / path).is_file(), f'Broken local link in {doc.name}: {target}'
print(f'Checked {total} verbatim source excerpts and all local documentation links.')
