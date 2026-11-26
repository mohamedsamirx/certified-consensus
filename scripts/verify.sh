#!/usr/bin/env bash
# End-to-end verification: build, axiom audit, executable demo.
set -euo pipefail
cd "$(dirname "$0")/.."
export PATH="$HOME/.elan/bin:$PATH"

echo "== build =="
lake build

echo
echo "== axiom audit =="
out=$(lake env lean scripts/check_axioms.lean)
echo "$out"
bad=$(echo "$out" | grep "depends on axioms" \
  | grep -v "\[propext, Classical.choice, Quot.sound\]" || true)
if [ -n "$bad" ]; then
  echo "FAIL: unexpected axioms"
  echo "$bad"
  exit 1
fi
if echo "$out" | grep -q "sorryAx"; then
  echo "FAIL: proof depends on sorryAx"
  exit 1
fi
echo "OK: only propext, Classical.choice, Quot.sound"

echo
echo "== certificate demo (exact) =="
lake exe certify data/stereo_certificate.txt

echo
echo "== certificate demo (tolerance) =="
lake exe certify data/noisy_certificate.txt

echo
echo "== elaborator command (kernel-time check) =="
lake env lean Examples.lean

echo
echo "== elaborator command (source-relative paths) =="
lake env lean tests/PathResolve.lean

echo
echo "== elaborator command rejects an invalid certificate =="
if lake env lean tests/Reject.lean > /tmp/cc-reject.log 2>&1; then
  echo "FAIL: tests/Reject.lean compiled but should have been rejected"
  exit 1
fi
grep -q "REJECTED — F is not rank two" /tmp/cc-reject.log || {
  echo "FAIL: rejection message missing"
  cat /tmp/cc-reject.log
  exit 1
}
echo "OK: invalid certificate rejected at elaboration time"

echo
echo "OK: build, axioms, both certificates, and the elaborator command verified"
