#!/bin/bash
# Verifies cedar-policy with Verus; `focus` skips re-verifying cedar-policy-core.
# Extra arguments go to Verus. Environment: see verus_core.sh.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
build=${BUILD_DIR:-$(cd "$here/.." && pwd)/.build}
mkdir -p "$build"
log=${VLOG:-$build/verus-api.log}
export PATH=${VERUS_DIR:-$HOME/tools/verus-dl/verus-x86-linux}:$PATH
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$build/target-verus}
# cedar-policy-core as a dependency sees Verus's injected feature twice, and workspace lints on the model
export RUSTFLAGS="${RUSTFLAGS:-} -A duplicate_features -A missing_debug_implementations"
cd "$here/../cedar/cedar-policy" || exit 1
cargo verus focus --fwd-verus-args-to all -p cedar-policy --features verus -- --no-lifetime "$@" > "$log" 2>&1
status=$?
grep -v GLIBC "$log" | awk '/^(error|warning)/{show=($0 ~ /^error/)} show' | grep -v "^ *|  *^*$" | head -${LINES_SHOWN:-80}
grep "verification results" "$log" | tail -1
exit $status
