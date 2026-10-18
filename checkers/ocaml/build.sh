#!/usr/bin/env bash
# Build the OCaml checker executables and run the support self-test.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
set -euo pipefail
root=$(cd "$(dirname "$0")/../.." && pwd)
compiler=${OCAMLOPT:-ocamlopt}
# Zarith is normally installed by opam/findlib; allow an explicit installation.
if [[ -n "${ZARITH_DIR:-}" ]]; then
  zarith_dir=$ZARITH_DIR
elif command -v ocamlfind >/dev/null 2>&1; then
  zarith_dir=$(ocamlfind query zarith)
else
  zarith_dir=$("$compiler" -where)/zarith
fi
if [[ ! -f "$zarith_dir/zarith.cmxa" ]]; then
  echo 'Zarith is required: opam install zarith (or set ZARITH_DIR).' >&2
  exit 1
fi
flags=(-w +a-4-40-42-44-70 -I "$zarith_dir" zarith.cmxa)
mkdir -p "$root/build/ocaml"
cp "$root/checkers/ocaml/"*.ml "$root/build/ocaml/"
cd "$root/build/ocaml"
machine_sources=(support.ml logic.ml compute.ml machine.ml)
declaration_sources=(named.ml environment.ml ast_proof.ml admissions.ml foundation.ml)
"$compiler" "${flags[@]}" -o g17check "${machine_sources[@]}" g17check.ml
"$compiler" "${flags[@]}" -o g17c_check \
  "${machine_sources[@]}" "${declaration_sources[@]}" compiled.ml g17c_check.ml
"$compiler" "${flags[@]}" -o checker_tests \
  "${machine_sources[@]}" "${declaration_sources[@]}" checker_tests.ml
"$compiler" "${flags[@]}" -o support_test support.ml support_test.ml
./support_test
