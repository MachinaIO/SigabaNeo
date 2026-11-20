#!/usr/bin/env bash
# All tests (docs/DESIGN.md). Run from anywhere; the core must be buildable.
#   ./tests/run.sh    build the core, then the Python tests (python/tests): the trusted check on
#                     the cases and on bad proofs, the Prove2Me client, the compatible platform
set -u
cd "$(dirname "$0")/.."
lake build >/dev/null || { echo "core build failed"; exit 2; }
python3 -m unittest discover -s python/tests -v
