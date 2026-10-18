#!/usr/bin/env bash
# Build the Rust checkers into build/rust/.
# Part of the Grace17 proof assistant for mathematics based on set theory.
# Copyright (c) 2026 Grant Passmore.
# Released under the Apache License 2.0. See LICENSE in the repository root.
# Authors: Grant Passmore
set -euo pipefail
root="$(cd "$(dirname "$0")/../.." && pwd)"
cd "$root/checkers/rust"
if ! command -v cargo >/dev/null 2>&1; then
  echo "cargo is not installed; see https://rustup.rs" >&2
  exit 1
fi
cargo build --release --quiet
cargo test --release --quiet 2>&1 | grep -E "test result|FAILED" | head -1
mkdir -p "$root/build/rust"
cp target/release/g17check target/release/g17c_check "$root/build/rust/"
echo "built build/rust/g17check and build/rust/g17c_check"
