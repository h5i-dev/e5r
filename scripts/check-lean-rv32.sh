#!/usr/bin/env bash
# Serial builds and proof checking; never uses Cargo's dev profile.
set -euo pipefail
cd "$(dirname "$0")/.."
CARGO_BUILD_JOBS=1 cargo build --release -p e5r-verify
python3 verification/rv32/tools/check.py
