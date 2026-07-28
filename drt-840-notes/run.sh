#!/bin/bash
# Build and test the #840 typed-expression DRT.
#   ./drt-840-notes/run.sh build   -- cargo build
#   ./drt-840-notes/run.sh test    -- cargo test --lib typed_expr (needs the Lean lib built)
#   ./drt-840-notes/run.sh lean    -- lake build CedarFFI:static
#   ./drt-840-notes/run.sh probe   -- dump Lean's derived ToJson for every TypedExpr ctor
set -euo pipefail
REPO="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$REPO"
source cedar-drt/set_env_vars.sh
case "${1:-test}" in
  build) cd cedar-drt && cargo build ;;
  test)  cd cedar-drt && cargo test --lib typed_expr -- --nocapture ;;
  lean)  cd cedar-lean && lake build CedarFFI:static ;;
  probe) cd cedar-lean && lake env lean ../drt-840-notes/probe_full.lean
         lake env lean ../drt-840-notes/probe_like.lean ;;
  *) echo "usage: $0 {build|test|lean|probe}" >&2; exit 2 ;;
esac
