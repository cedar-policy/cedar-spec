#!/bin/bash
# Translates src/*.rs to lean/CedarRustModel/{Types,Extracted}.lean.
# `char_lt` and `char_code` are opaque (Aeneas can't compare or cast `char`s);
# they are hand-written in lean/CedarRustModel/FunsExternal.lean.
# Requires `charon` and `aeneas` on the PATH (versions in README.md).
set -euo pipefail
cd "$(dirname "$0")/.."
build=${BUILD_DIR:-$(cd .. && pwd)/.build}
mkdir -p "$build"
export CARGO_TARGET_DIR=${CARGO_TARGET_DIR:-$build/target-model}
rm -f cedar_rust_model.llbc
charon cargo --preset=aeneas --opaque 'cedar_rust_model::value::char_lt' --opaque 'cedar_rust_model::ext::char_code'
out=$(mktemp -d -p "$build")
aeneas -backend lean cedar_rust_model.llbc -dest "$out" -split-files -abort-on-error
mkdir -p lean/CedarRustModel
mv "$out/Types.lean" lean/CedarRustModel/Types.lean
mv "$out/Funs.lean" lean/CedarRustModel/Extracted.lean
rm -rf "$out" cedar_rust_model.llbc
