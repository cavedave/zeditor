#!/bin/sh
# Run every test in the repository. From the repository root:  sh tests/run_all.sh
#
#   1. lake build        the specification, its proofs, and the claims (ZEditor/Claims.lean)
#   2. Check.lean        exhaustive checks over all small documents, with recorded results
#   3. tests/*.sh        the running editor, driven by key scripts
set -e
echo "== 1. Build: specification, proofs and claims"
lake build 2>&1 | tail -1
echo "== 2. Exhaustive checks (ZEditor/Check.lean)"
lake build ZEditor.Check > /dev/null 2>&1
if lake env lean ZEditor/Check.lean > /dev/null 2>&1; then echo "PASS  all recorded results hold"
else echo "FAIL  a recorded result changed:"; lake env lean ZEditor/Check.lean 2>&1 | grep -i "guard\|error" | head; exit 1; fi
echo "== 3. The running editor"
fail=0
for t in tests/save.sh tests/final_newline.sh tests/mark.sh tests/changed.sh; do sh "$t" || fail=1; done
exit $fail
