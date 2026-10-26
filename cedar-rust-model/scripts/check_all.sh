#!/bin/bash
# Runs every check: extraction is up to date, Lean builds, axioms, Verus,
# cargo test, clippy (set CLIPPY_BASELINE to an upstream checkout to diff).
# Environment: BUILD_DIR (default ../.build, holds the logs), VERUS_DIR, AENEAS_DIR.
set -uo pipefail
here=$(cd "$(dirname "$0")/.." && pwd)
root=$(cd "$here/.." && pwd)
build=${BUILD_DIR:-$root/.build}
mkdir -p "$build"
export PATH=${AENEAS_DIR:-$HOME/tools/aeneas-dl}:$PATH
failed=()
step() {
    local name=$1; shift
    local t0=$(date +%s)
    echo "== $name"
    if "$@"; then
        echo "   ok ($(( $(date +%s) - t0 ))s)"
    else
        echo "   FAILED ($(( $(date +%s) - t0 ))s)"
        failed+=("$name")
    fi
}

extract() {
    "$here/scripts/extract.sh" > "$build/extract.log" 2>&1 || { tail -20 "$build/extract.log"; return 1; }
    git -C "$here" diff --quiet -- lean/CedarRustModel/Types.lean lean/CedarRustModel/Extracted.lean \
        || { echo "   the extracted Lean files changed: commit them"; return 1; }
}
lean_cedar() {
    (cd "$root/cedar-lean" && lake build Cedar SymCC DiffTest UnitTest SymTest Protobuf CedarProto CedarFFI \
        CedarUnitTests CedarSymTests Cli) > "$build/lean-cedar.log" 2>&1 \
        || { grep -E 'error' "$build/lean-cedar.log" | head -20; return 1; }
    (cd "$root/cedar-lean" && .lake/build/bin/CedarUnitTests) > "$build/lean-unit.log" 2>&1 \
        || { tail -5 "$build/lean-unit.log"; return 1; }
    tail -1 "$build/lean-unit.log"
}
lean_model() {
    (cd "$here/lean" && lake build CedarRustModel) > "$build/lean-model.log" 2>&1 \
        || { grep -E 'error' "$build/lean-model.log" | head -20; return 1; }
    grep -q 'declaration uses .sorry.' "$build/lean-model.log" && { echo "   sorry found"; return 1; }
    return 0
}
verus_core() { "$here/scripts/verus_core.sh"; }
verus_api() { "$here/scripts/verus_api.sh"; }
cargo_test() {
    (cd "$root/cedar" && CARGO_TARGET_DIR="$build/target" cargo test -p cedar-policy-core --lib \
        && CARGO_TARGET_DIR="$build/target" cargo test -p cedar-policy --lib) > "$build/cargo-test.log" 2>&1 \
        || { grep -E 'FAILED|panicked|^error' "$build/cargo-test.log" | head -20; return 1; }
    grep '^test result' "$build/cargo-test.log"
}
clippy_warnings() {
    (cd "$1" && CARGO_TARGET_DIR="$2" cargo clippy -p cedar-policy-core -p cedar-policy --all-targets 2>&1) \
        | grep -E '^(warning|error)' | sort | uniq -c
}
clippy() {
    clippy_warnings "$root/cedar" "$build/target" > "$build/clippy.txt"
    if [ -n "${CLIPPY_BASELINE:-}" ]; then
        clippy_warnings "$CLIPPY_BASELINE" "$build/target-upstream" > "$build/clippy-baseline.txt"
        diff "$build/clippy-baseline.txt" "$build/clippy.txt" || { echo "   new clippy warnings"; return 1; }
    else
        cat "$build/clippy.txt"
    fi
}

step "extraction (Charon + Aeneas)" extract
step "Lean: cedar-lean" lean_cedar
step "Lean: CedarRustModel" lean_model
step "Lean: axioms" "$here/scripts/check_axioms.sh"
step "Verus: cedar-policy-core" verus_core
step "Verus: cedar-policy" verus_api
step "cargo test" cargo_test
step "clippy" clippy

if [ ${#failed[@]} -gt 0 ]; then
    echo "FAILED: ${failed[*]}"
    exit 1
fi
echo "all checks passed"
