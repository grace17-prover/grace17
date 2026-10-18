#!/usr/bin/env bash
# Format or check the OCaml checker sources with ocamlformat.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
formatter=${OCAMLFORMAT_BIN:-ocamlformat}
case "${1:-write}" in
  write) "$formatter" --inplace "$root"/checkers/ocaml/*.ml ;;
  check) "$formatter" --check "$root"/checkers/ocaml/*.ml ;;
  *) echo 'usage: format.sh [write|check]' >&2; exit 1 ;;
esac
