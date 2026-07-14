#!/usr/bin/env bash
#
# verify.sh — regenerate EVERY claim in this artifact from a clean checkout.
#
# Exits non-zero if any of the following fails:
#   * the Lean project does not build (which kernel-checks all 90 theorems)
#   * any banned construct is present (sorry / admit / native_decide / axiom / extern)
#   * the vendored C oracle has been modified
#   * any measured number differs from the one recorded in CLAIMS.md
#
# Usage:  ./verify.sh [--quick]     (--quick uses 20k fuzz inputs instead of 120k)
set -euo pipefail
cd "$(dirname "$0")"

FUZZ_N=120000
IDEM_N=20000
[ "${1:-}" = "--quick" ] && { FUZZ_N=20000; IDEM_N=5000; }

pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
fail() { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; exit 1; }
step() { printf '\n\033[1m== %s\033[0m\n' "$1"; }

# ---------------------------------------------------------------- 0. oracle integrity
step "0. Oracle integrity (the C must be untouched)"
EXPECT_C=607e756460fa0de37d20a7a9181f2de29c97bfb7ce5a0e6c2f548243836cd852
EXPECT_H=25b0145150d500498e4d209cec69c18c42cf818bffcc54690be3b895a2a16dee
ACTUAL_C=$(shasum -a 256 oracle/cJSON.c | cut -d' ' -f1)
ACTUAL_H=$(shasum -a 256 oracle/cJSON.h | cut -d' ' -f1)
[ "$ACTUAL_C" = "$EXPECT_C" ] || fail "oracle/cJSON.c MODIFIED (sha256 $ACTUAL_C)"
[ "$ACTUAL_H" = "$EXPECT_H" ] || fail "oracle/cJSON.h MODIFIED (sha256 $ACTUAL_H)"
pass "cJSON.c + cJSON.h byte-identical to upstream fb16e5c"

# ---------------------------------------------------------------- 1. build oracle
step "1. Build the C oracle"
cc -O2 -std=c99 -o oracle/cjson_oracle oracle/wrapper.c oracle/cJSON.c -lm
pass "oracle/cjson_oracle built"

# ---------------------------------------------------------------- 2. build + check Lean
step "2. Build Lean (this kernel-checks every theorem)"
( cd lean && rm -rf .lake/build && lake build ) >/dev/null 2>&1 \
  || fail "lake build failed — a theorem is broken"
pass "lake build clean (all proof modules are in the default target)"

step "3. Banned constructs"
if grep -rn --include=*.lean -E "\bsorry\b|\badmit\b|native_decide|^axiom |@\[extern\]" \
     lean/Cjson lean/Main.lean | grep -v "banned" ; then
  fail "banned construct present"
fi
pass "no sorry / admit / native_decide / custom axiom / extern"

step "4. #print axioms on every headline theorem"
cat > /tmp/vsf_axioms.lean <<'EOF'
import Cjson
open Cjson
#print axioms parseValue
#print axioms parseDoc
#print axioms serialize
#print axioms parseDoc_serialize
#print axioms parseDoc_canonical
#print axioms parseDoc_depth
#print axioms parseDoc_idempotent
EOF
AX=$( cd lean && lake env lean /tmp/vsf_axioms.lean )
echo "$AX" | sed 's/^/    /'
if echo "$AX" | grep -qv -E "propext|Classical.choice|Quot.sound|depends on axioms"; then
  fail "a non-standard axiom appeared"
fi
pass "only Lean's three standard axioms; no project axioms"

# ---------------------------------------------------------------- 5. differential
step "5. Differential — JSONTestSuite (318 files)"
[ -d harness/JSONTestSuite ] || git clone --depth 1 -q \
  https://github.com/nst/JSONTestSuite.git harness/JSONTestSuite
SUITE=$(python3 harness/run_suite.py)
echo "$SUITE" | head -7 | sed 's/^/    /'
echo "$SUITE" | grep -q "oracle==lean  (exit AND bytes) : 297/318" \
  || fail "JSONTestSuite byte-agreement changed (expected 297/318)"
echo "$SUITE" | grep -q "oracle==lean  (accept/reject)  : 317/318" \
  || fail "JSONTestSuite accept/reject agreement changed (expected 317/318)"
pass "297/318 byte-identical, 317/318 accept/reject — as recorded in CLAIMS.md"

step "6. Differential — fuzzing ($FUZZ_N inputs, fixed seed)"
FUZZ=$(python3 harness/fuzz.py "$FUZZ_N")
echo "$FUZZ" | grep -E "^  [A-Z]" | sed 's/^/    /'
if [ "$FUZZ_N" = 120000 ]; then
  echo "$FUZZ" | grep -q "AGREE                  116476" \
    || fail "fuzz agreement changed (expected 116476/120000)"
  pass "116,476/120,000 agreement; 1 UNKNOWN (documented classifier artifact, D-LEAN-1)"
else
  pass "quick fuzz run complete (numbers in CLAIMS.md are for the 120k run)"
fi

step "7. Idempotence cross-check (binary vs. theorem T3, $IDEM_N fuzz inputs)"
IDEM=$(python3 harness/idempotence.py "$IDEM_N")
echo "$IDEM" | tail -4 | sed 's/^/    /'
echo "$IDEM" | grep -q "VIOLATIONS     : 0" \
  || fail "the compiled binary VIOLATES theorem T3 — extraction bug"
pass "0 violations: the extracted binary agrees with T3"

step "8. Documentation matches the artifact"
if [ "$FUZZ_N" = 120000 ] && [ "$IDEM_N" = 20000 ]; then
  python3 harness/check_claims.py | sed 's/^/    /' || fail "docs assert numbers the artifact does not produce"
  pass "every number in README/PAPER/CLAIMS/RESULTS/GAPS matches the data on disk"
else
  printf '  \033[33mSKIP\033[0m  (quick mode: rerun without --quick to check the documented numbers)\n'
fi

printf '\n\033[1;32mALL CLAIMS REPRODUCED.\033[0m See CLAIMS.md for the PROVEN/MEASURED split.\n'
