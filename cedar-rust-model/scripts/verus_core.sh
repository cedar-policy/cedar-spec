#!/bin/bash
# Verifies cedar-policy-core with Verus and prints errors and the result line.
# Extra arguments go to Verus, e.g. --verify-only-module evaluator --verify-function unary_app
# Environment: VERUS_DIR, BUILD_DIR (default ../.build), VLOG (full log path).
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
build=${BUILD_DIR:-$(cd "$here/.." && pwd)/.build}
mkdir -p "$build"
log=${VLOG:-$build/verus-core.log}
export PATH=${VERUS_DIR:-$HOME/tools/verus-dl/verus-x86-linux}:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$build/target-verus}
cd "$here/../cedar/cedar-policy-core" || exit 1
# partial verification (`--verify-only-module`, `--verify-function`) needs `focus`
mode=verify
case " $* " in *" --verify-only-module "*|*" --verify-function "*) mode=focus ;; esac
cargo verus $mode -p cedar-policy-core --features verus -- --no-lifetime "$@" > "$log" 2>&1
status=$?
grep -v GLIBC "$log" | awk '/^(error|warning)/{show=($0 ~ /^error/)} show' | grep -v "^ *|  *^*$" | head -${LINES_SHOWN:-80}
grep "verification results" "$log" | tail -1
exit $status
