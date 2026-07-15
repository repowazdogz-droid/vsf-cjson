#!/usr/bin/env bash
#
# verify.sh — regenerate and re-check EVERY claim in this artifact from a clean checkout.
#
# WHAT EACH GATE ACTUALLY ESTABLISHES (v1.0.0's messages overstated this; see CHANGELOG):
#
#   lake build              elaboration + type-correctness. It does NOT reject `sorry`
#                           (Lean emits a warning, not an error). Do not rely on it for that.
#   sorry gate              scans a FRESH build's output for Lean's `declaration uses `sorry``
#                           warning (note the backticks; the v1.0.0-era pattern used quotes
#                           and silently never fired).
#   axiom gate              parses `#print axioms` for every attested declaration and compares
#                           the axiom SET against an allow-list. THIS is what rejects `sorry`
#                           (as sorryAx) and any custom axiom. Fails closed.
#   manifest gate           the attested set cannot shrink with the source; proof modules must
#                           be in the default build target; pins must match.
#   figure gate             figures are regenerated into a temp dir and BYTE-COMPARED.
#   docs gate               documented numbers are parsed out of the .md files and compared to
#                           values GENERATED from the measurements. Non-circular.
#
# Usage:  ./verify.sh [--quick]
#   --quick  smaller fuzz/idempotence runs, written to results/quick/ (gitignored).
#            Quick mode CANNOT establish the documented numbers and says so; it never touches
#            results/canonical/, so it leaves the tree clean.
set -uo pipefail
cd "$(dirname "$0")"

FUZZ_N=120000; IDEM_N=20000; MODE=full; RESULTS=results/canonical
if [ "${1:-}" = "--quick" ]; then FUZZ_N=20000; IDEM_N=5000; MODE=quick; RESULTS=results/quick; fi

FAILED=0
pass() { printf '  \033[32mPASS\033[0m  %s\n' "$1"; }
fail() { printf '  \033[31mFAIL\033[0m  %s\n' "$1"; FAILED=1; }
step() { printf '\n\033[1m== %s\033[0m\n' "$1"; }
die()  { printf '\n\033[1;31mVERIFICATION FAILED\033[0m\n'; exit 1; }

SHA256=$(command -v sha256sum >/dev/null 2>&1 && echo "sha256sum" || echo "shasum -a 256")

step "1. Pinned inputs — oracle (must be byte-identical upstream C)"
python3 - <<'PY' || fail "oracle hash mismatch"
import json,hashlib,sys
m=json.load(open("release/manifest.json"))["pinned_inputs"]["oracle"]
bad=False
for rel,want in m["files"].items():
    got=hashlib.sha256(open(rel,'rb').read()).hexdigest()
    print(f"    {rel}: {'ok' if got==want else 'MISMATCH'} {got[:16]}…")
    bad |= got!=want
sys.exit(1 if bad else 0)
PY
[ $FAILED -eq 0 ] && pass "oracle C is the pinned upstream source, unmodified" || die

step "2. Pinned inputs — JSONTestSuite corpus (fail closed if the exact commit is unavailable)"
PIN=$(python3 -c "import json;print(json.load(open('release/manifest.json'))['pinned_inputs']['jsontestsuite']['commit'])")
if [ ! -d harness/JSONTestSuite/.git ]; then
  rm -rf harness/JSONTestSuite
  git clone -q https://github.com/nst/JSONTestSuite.git harness/JSONTestSuite || { fail "clone failed"; die; }
fi
( cd harness/JSONTestSuite && git fetch -q origin && git checkout -q "$PIN" ) 2>/dev/null \
  || { fail "cannot check out pinned corpus commit $PIN (failing closed)"; die; }
GOT=$(cd harness/JSONTestSuite && git rev-parse HEAD)
[ "$GOT" = "$PIN" ] || { fail "corpus HEAD $GOT != pin $PIN"; die; }
pass "JSONTestSuite pinned at $PIN"

step "3. Build the C oracle"
cc -O2 -std=c99 -o oracle/cjson_oracle oracle/wrapper.c oracle/cJSON.c -lm || { fail "oracle build"; die; }
pass "oracle/cjson_oracle built"

step "4. Build Lean from a clean .lake (elaboration + type-correctness only)"
BUILD_LOG=$(mktemp)
( cd lean && rm -rf .lake/build && lake build ) >"$BUILD_LOG" 2>&1 || { fail "lake build failed"; sed 's/^/    /' "$BUILD_LOG" | tail -20; die; }
pass "lake build clean — NOTE: this does not reject \`sorry\`; gates 5 and 6 do"

step "5. sorry gate (build-output scan — independent of source grep)"
# NB: Lean 4.32 renders this with BACKTICKS -- "declaration uses `sorry`" -- not quotes.
# The first version of this gate grepped for 'sorry' and silently never fired. The mutation
# suite caught it. Match either quoting.
if grep -Eq "declaration uses .?sorry.?" "$BUILD_LOG"; then
  grep -E "declaration uses .?sorry.?" "$BUILD_LOG" | sed 's/^/    /'
  fail "a declaration uses sorry"; die
fi
pass "no declaration uses sorry"
rm -f "$BUILD_LOG"

step "6. Axiom gate (structural #print axioms parse; fails closed)"
python3 harness/check_axioms.py | sed 's/^/  /' || { fail "axiom verification"; die; }
pass "every attested declaration depends only on the allow-listed axioms"

step "7. Banned-construct scan (belt and braces; NOT the primary gate)"
if grep -rn --include='*.lean' -E "\bsorry\b|\badmit\b|native_decide|@\[extern\]" lean/Cjson lean/Main.lean \
     | grep -v "banned\|@attested" ; then
  fail "banned construct in source"; die
fi
pass "no sorry / admit / native_decide / extern in source"

step "8. Coverage manifest"
python3 harness/check_manifest.py | sed 's/^/  /' || { fail "manifest"; die; }
pass "attested set, proof modules, pins and toolchain all match the manifest"

step "8b. GAP-2 adequacy — build the spec chain + statement pins (Cjson.Spec.Checks)"
# Cjson.Spec.Checks re-asserts the exact Grammar.lean C2/C4 Props and `adequacy = C2 ∧ C4`;
# if any of those statements is weakened or restated it STOPS COMPILING here.
( cd lean && lake build Cjson.Spec.Checks ) >/dev/null 2>&1 \
  || { fail "Cjson.Spec.Checks failed — a C2/C4/adequacy statement changed, or a proof broke"; die; }
pass "Cjson.Spec.Checks compiles — C2, C4 and adequacy statements are unchanged"

step "8c. GAP-2 axiom / attestation / grammar-freeze gate (fails closed)"
# Rebuilds the spec chain, runs #print axioms on all 10 attested GAP-2 declarations, checks the
# @attested-gap2 markers against release/gap2_manifest.json (both directions), pins the frozen
# Grammar Props by hash, and asserts the released artifact is byte-identical to v1.0.1.
python3 harness/gap2/check_gap2.py | sed 's/^/  /' || { fail "GAP-2 adequacy verification"; die; }
pass "C2 ∧ C4 (adequacy): axiom-clean, attested, Grammar frozen, released artifact = v1.0.1"

step "8d. ADEQUACY_SUMMARY.md is a faithful regeneration of the compiled theorems (byte-compare)"
python3 harness/gap2/gen_adequacy_summary.py --check | sed 's/^/  /' \
  || { fail "ADEQUACY_SUMMARY.md out of date — run harness/gap2/gen_adequacy_summary.py and commit"; die; }
pass "ADEQUACY_SUMMARY.md byte-matches a fresh regeneration"

step "9. Differential — JSONTestSuite (pinned corpus)"
VSF_RESULTS=$RESULTS python3 harness/run_suite.py | sed -n '1,17p' | sed 's/^/    /' || { fail "suite"; die; }
pass "suite run complete -> $RESULTS/suite_results.json"

step "10. Differential — fuzzing ($FUZZ_N inputs, fixed seed)"
VSF_RESULTS=$RESULTS python3 harness/fuzz.py "$FUZZ_N" | grep -E "^  [A-Z_]|PORT_WRONG" | sed 's/^/    /' || { fail "fuzz"; die; }
pass "fuzz run complete -> $RESULTS/fuzz_results.json"

step "11. Idempotence cross-check (compiled binary vs. theorem T3)"
VSF_RESULTS=$RESULTS python3 harness/idempotence.py "$IDEM_N" | tail -4 | sed 's/^/    /' || { fail "idempotence"; die; }
pass "idempotence run complete -> $RESULTS/idempotence_results.json"

step "12. PORT_WRONG / UNCLASSIFIED must be zero (directly counted)"
python3 - "$RESULTS" <<'PY' || { fail "a divergence was classified PORT_WRONG or UNCLASSIFIED"; die; }
import json,sys
r=sys.argv[1]
f=json.load(open(f"{r}/fuzz_results.json"))["counts"]
s=json.load(open(f"{r}/suite_results.json"))
sp=sum(x["cls"]=="PORT_WRONG" for x in s); su=sum(x["cls"]=="UNCLASSIFIED" for x in s)
print(f"    fuzz  PORT_WRONG={f['PORT_WRONG']}  UNCLASSIFIED={f['UNCLASSIFIED']}")
print(f"    suite PORT_WRONG={sp}  UNCLASSIFIED={su}")
sys.exit(0 if f['PORT_WRONG']==0 and f['UNCLASSIFIED']==0 and sp==0 and su==0 else 1)
PY
pass "PORT_WRONG = 0 and UNCLASSIFIED = 0 on both corpora"

if [ "$MODE" = quick ]; then
  printf '\n\033[33m== QUICK MODE ==\033[0m\n'
  printf '  Quick mode used %s inputs and wrote to %s/ (gitignored).\n' "$FUZZ_N" "$RESULTS"
  printf '  It CANNOT establish the documented numbers: gates 13-15 (canonical claims,\n'
  printf '  figures, documentation) are SKIPPED. Run ./verify.sh with no flag for those.\n'
  printf '\n\033[1;32mQUICK CHECKS PASSED\033[0m (proofs, axioms, manifest, pins, PORT_WRONG=0)\n'
  git diff --quiet && git diff --cached --quiet || { printf '\n'; fail "quick mode dirtied the tree"; git status --porcelain; die; }
  printf '  Tree is clean.\n'
  exit 0
fi

step "13. Regenerate canonical claims from the measurements"
python3 harness/gen_claims.py >/dev/null || { fail "gen_claims"; die; }
pass "results/canonical/claims.json regenerated FROM the measurement outputs"

step "14. Figure gate — regenerate into a temp dir and BYTE-COMPARE"
TMPFIG=$(mktemp -d)
python3 figures/make_figures.py "$TMPFIG" >/dev/null || { fail "figure generation"; die; }
for f in figures/*.svg; do
  if ! cmp -s "$f" "$TMPFIG/$(basename "$f")"; then
    fail "figure out of date or hand-edited: $f"
    diff <(fold -w100 "$f") <(fold -w100 "$TMPFIG/$(basename "$f")") | head -6 | sed 's/^/    /'
    rm -rf "$TMPFIG"; die
  fi
done
rm -rf "$TMPFIG"
pass "all $(ls figures/*.svg | wc -l | tr -d ' ') committed figures byte-match a fresh regeneration"

step "15. Documentation gate — parse the .md files, compare to generated claims"
python3 harness/check_claims.py | tail -3 | sed 's/^/  /' || { fail "documentation"; die; }
pass "every documented number is marked and matches the measurement (non-circular)"

step "16. Working tree must be clean"
if ! git diff --quiet || ! git diff --cached --quiet; then
  fail "verification modified tracked files:"; git status --porcelain | sed 's/^/    /'
  printf '  (if only results/canonical changed, the measurements moved — commit them deliberately)\n'
  die
fi
pass "git tree clean — verification is idempotent"

printf '\n\033[1;32mALL CLAIMS REPRODUCED.\033[0m See CLAIMS.md for the PROVEN / MEASURED / OBSERVED / NOT PROVEN split.\n'
