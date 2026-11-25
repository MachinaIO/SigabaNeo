#!/usr/bin/env bash
# All tests (docs/DESIGN.md). Run from anywhere; the core must be buildable.
#   ./tests/run.sh    build the core, then the Python tests (python/tests): the trusted check on
#                     the cases and on bad proofs; the client on a DAG checkout; the DAG's
#                     verifier (statuses, semantic IDs, the syntactic filter); its tools (precheck,
#                     decisions, records, statuses, index, init); Formalpedia's conversion
set -u
cd "$(dirname "$0")/.."
lake build >/dev/null || { echo "core build failed"; exit 2; }
python3 -m unittest discover -s python/tests -v
