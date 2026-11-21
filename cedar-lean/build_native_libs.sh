#!/usr/bin/env bash
# Copyright Cedar Contributors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# Build the compiled libraries that `nativeLibs` (lakefile.lean) loads into Lean when it elaborates
# CedarGen and CedarGenProof, so that Specimen's and Basalt's tactics run compiled. Optional: a
# library that is not built is left out, and its code is interpreted (the same results, more
# slowly). Run from cedar-lean, after `lake build Cedar` has fetched the dependencies.
#
#   ./build_native_libs.sh            # every library in the list
#   ./build_native_libs.sh --no-mathlib   # all but Mathlib's, which takes the longest to link
set -euo pipefail
cd "$(dirname "$0")"
skip_mathlib=0
[[ "${1:-}" == "--no-mathlib" ]] && skip_mathlib=1

targets=$(python3 - "$skip_mathlib" <<'PY'
import os, re, sys
skip_mathlib = sys.argv[1] == "1"
src = open("lakefile.lean").read()
block = src[src.index("def nativeLibs"):src.index("let mut args")]
out = []
for p in re.findall(r'"([^"]+\.so)"', block):
    pkg = p.split("/")[2]                      # .lake/packages/<pkg>/...
    root = os.path.join(".lake/packages", pkg)
    f = os.path.basename(p)[:-3]
    if f.startswith("lib"):                    # a library's shared facet: lib<pkg>_<Lib>.so
        lib = f[len("lib") + len(pkg) + 1:]
        if not (skip_mathlib and lib == "Mathlib"):
            out.append(f"@{pkg}/{lib}:shared")
        continue
    # a module's dynlib: <pkg>_<A>_<B>_<C>.so for module A.B.C (a component may contain `_`)
    parts = f[len(pkg) + 1:].split("_")
    cur, mod, i = root, [], 0
    while i < len(parts):
        for j in range(len(parts), i, -1):
            name = "_".join(parts[i:j])
            if j < len(parts) and os.path.isdir(os.path.join(cur, name)):
                cur = os.path.join(cur, name); mod.append(name); i = j; break
            if j == len(parts) and os.path.exists(os.path.join(cur, name + ".lean")):
                mod.append(name); i = j; break
        else:
            # a library for a module this checkout does not have (an older Specimen): left out, its
            # stale file removed so that `lakefile.lean` does not load it
            print(f"no module for {p}: skipped", file=sys.stderr)
            if os.path.exists(p): os.remove(p)
            break
    else:
        out.append("+" + ".".join(mod) + ":dynlib")
print(" ".join(out))
PY
)
# shellcheck disable=SC2086
lake build $targets
