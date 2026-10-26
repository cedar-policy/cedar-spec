#!/bin/bash
# Checks that the theorems in lean/CheckAxioms.lean use only `propext`,
# `Classical.choice` and `Quot.sound`. Run after `lake build CedarRustModel`.
set -euo pipefail
cd "$(dirname "$0")/../lean"
lake env lean CheckAxioms.lean > ../../.build/axioms.out 2>&1 || { cat ../../.build/axioms.out; exit 1; }
python3 -I - ../../.build/axioms.out CheckAxioms.lean <<'PY'
import re, sys
out = open(sys.argv[1]).read()
expected = re.findall(r'^#print axioms (\S+)', open(sys.argv[2]).read(), re.M)
allowed = {'propext', 'Classical.choice', 'Quot.sound'}
found = {}
for m in re.finditer(r"'([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", out):
    found[m.group(1)] = set(a.strip() for a in (m.group(3) or '').split(',') if a.strip())
bad = [t for t in expected if t not in found or not found[t] <= allowed]
for t in expected:
    print(f"  {t}: {', '.join(sorted(found.get(t, {'<missing>'}))) or 'none'}")
if bad:
    print('axiom check FAILED for: ' + ', '.join(bad)); sys.exit(1)
print(f'axiom check: all {len(expected)} theorems use only propext, Classical.choice, Quot.sound')
PY
