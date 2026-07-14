#!/usr/bin/env bash
#
# mutation_tests.sh — prove that every gate in verify.sh actually FIRES.
#
# A verification pipeline that has never been shown to fail is not evidence of anything.
# v1.0.0 shipped an axiom gate that could not fire, a `lake build` that did not reject sorry,
# and a documentation check that never read the documentation. All three showed green.
#
# Each attack below mutates the repository, runs the EXACT gate command verify.sh runs, and
# requires it to FAIL. The repository is restored automatically (git checkout) after each,
# including on error.
#
# Run from the repo root, on a CLEAN tree:  ./harness/mutation_tests.sh
set -uo pipefail
cd "$(dirname "$0")/.."

if ! git diff --quiet || ! git diff --cached --quiet; then
  echo "refusing to run: working tree is dirty (mutations must start from a clean tree)"; exit 1
fi

PASS=0; FAIL=0
restore() { git checkout -q -- . ; rm -rf /tmp/vsf_mut; }
trap restore EXIT

expect_fail() {   # expect_fail <name> <cmd...>
  local name="$1"; shift
  if "$@" >/tmp/vsf_mut.log 2>&1; then
    printf '  \033[31mBYPASS\033[0m  %s — the gate PASSED a mutated artifact\n' "$name"
    sed 's/^/          /' /tmp/vsf_mut.log | tail -4
    FAIL=$((FAIL+1))
  else
    printf '  \033[32mBLOCKED\033[0m %s\n' "$name"
    grep -m1 -E "FAIL|DISALLOWED|PHANTOM|FALSIFIED|UNATTESTED|error|sorry|MISMATCH|out of date|CONTRADICT|NOT ADJACENT|not in manifest|NOT marked" /tmp/vsf_mut.log \
      | sed 's/^ *//' | cut -c1-105 | sed 's/^/          /'
    PASS=$((PASS+1))
  fi
  restore
}

expect_pass() {   # expect_pass <name> <cmd...>
  local name="$1"; shift
  if "$@" >/tmp/vsf_mut.log 2>&1; then
    printf '  \033[32mPASS\033[0m    %s\n' "$name"; PASS=$((PASS+1))
  else
    printf '  \033[31mFAIL\033[0m    %s — expected to pass\n' "$name"
    tail -5 /tmp/vsf_mut.log | sed 's/^/          /'; FAIL=$((FAIL+1))
  fi
}

# the gate commands, exactly as verify.sh invokes them
gate_axioms()   { python3 harness/check_axioms.py; }
gate_manifest() { python3 harness/check_manifest.py; }
gate_docs()     { python3 harness/gen_claims.py >/dev/null && python3 harness/check_claims.py; }
gate_build()    { ( cd lean && lake build ); }
# a CACHED lake build does not re-emit warnings, so the scan must run on a FRESH build
# (verify.sh gate 4 wipes .lake/build before gate 5 for exactly this reason)
gate_sorry()    { ( cd lean && rm -rf .lake/build && lake build 2>&1 ) | grep -Eq "declaration uses .?sorry.?" && return 1 || return 0; }
gate_figures()  { rm -rf /tmp/vsf_mut && python3 figures/make_figures.py /tmp/vsf_mut >/dev/null \
                  && for f in figures/*.svg; do cmp -s "$f" "/tmp/vsf_mut/$(basename "$f")" || return 1; done; }
gate_pins()     { python3 harness/check_manifest.py >/dev/null; }

inject_axiom() {  # $1 = indentation prefix, $2 = wrap in section?
  python3 - "$1" "$2" <<'PY'
import sys
ind, sect = sys.argv[1], sys.argv[2] == "yes"
p = 'lean/Cjson/Proofs/Str.lean'
s = open(p).read()
ax = f"{ind}axiom evilAxiom : ∀ (n : Nat), n < 128 → utf8Enc n = [UInt8.ofNat n]\n"
block = f"\nsection\n{ax}end\n" if sect else f"\n{ax}\n"
s = s.replace("namespace Cjson\n", "namespace Cjson\n" + block, 1)
s = s.replace(
  "theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by\n  unfold utf8Enc\n  rw [if_pos (by omega)]",
  "theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := evilAxiom n h")
open(p,'w').write(s)
PY
}

echo "== Mutation suite: every gate must FIRE =="
echo

echo "1. indented custom axiom, threaded into a dependency of parseDoc_idempotent"
inject_axiom "  " no
expect_fail "   axiom gate rejects an indented custom axiom" gate_axioms

echo "2. section-scoped custom axiom"
inject_axiom "  " yes
expect_fail "   axiom gate rejects a section-scoped custom axiom" gate_axioms

echo "3. sorry injected into a dependency of parseDoc_idempotent"
python3 - <<'PY'
p='lean/Cjson/Proofs/Str.lean'; s=open(p).read()
s=s.replace("theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by\n  unfold utf8Enc\n  rw [if_pos (by omega)]",
            "theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by\n  sorry")
open(p,'w').write(s)
PY
if ( cd lean && lake build ) >/dev/null 2>&1; then
  printf '  \033[33mNOTE\033[0m    `lake build` SUCCEEDS on a sorry (Lean warns, it does not error)\n'
  printf '          -> this is exactly why gates 5 and 6 exist and why the docs say so.\n'
fi
expect_fail "   sorry gate (build-output scan) rejects it" gate_sorry
python3 - <<'PY'
p='lean/Cjson/Proofs/Str.lean'; s=open(p).read()
s=s.replace("theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by\n  unfold utf8Enc\n  rw [if_pos (by omega)]",
            "theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by\n  sorry")
open(p,'w').write(s)
PY
( cd lean && lake build ) >/dev/null 2>&1
expect_fail "   axiom gate independently rejects it (sorryAx)" gate_axioms
( cd lean && lake build ) >/dev/null 2>&1

echo "4. falsify documented numbers (data untouched)"
sed -i.bak 's/116,476/999,999/g' README.md && rm -f README.md.bak
expect_fail "   docs gate rejects a falsified README" gate_docs
sed -i.bak 's/116,476/999,999/g' PAPER.md && rm -f PAPER.md.bak
expect_fail "   docs gate rejects a falsified PAPER" gate_docs
sed -i.bak 's/claim:fuzz_agree=116476/claim:fuzz_agree=999999/' CLAIMS.md && rm -f CLAIMS.md.bak
expect_fail "   docs gate rejects a falsified CLAIMS marker" gate_docs
python3 - <<'PY'
# wrapper_c_lines is attested in exactly one file; removing it must make the claim unattested
s=open('CLAIMS.md').read().replace("<!-- claim:wrapper_c_lines=62 -->","")
open('CLAIMS.md','w').write(s)
PY
expect_fail "   docs gate rejects a REMOVED claim marker (unattested)" gate_docs

echo "5. tamper with a committed figure"
printf '<!-- tampered -->' >> figures/fig2-divergences.svg
expect_fail "   figure gate rejects a hand-edited SVG" gate_figures

echo "6. change the underlying data without regenerating figures/docs"
python3 - <<'PY'
import json
p='results/canonical/fuzz_results.json'; d=json.load(open(p))
d['counts']['AGREE'] = 999999
json.dump(d, open(p,'w'), indent=1)
PY
expect_fail "   figure gate rejects stale figures after a data change" gate_figures
python3 - <<'PY'
import json
p='results/canonical/fuzz_results.json'; d=json.load(open(p))
d['counts']['AGREE'] = 999999
json.dump(d, open(p,'w'), indent=1)
PY
expect_fail "   docs gate rejects docs stale w.r.t. changed data" gate_docs

echo "7. break the JSONTestSuite pin"
python3 - <<'PY'
import json
p='release/manifest.json'; m=json.load(open(p))
m['pinned_inputs']['jsontestsuite']['commit'] = '0'*40
json.dump(m, open(p,'w'), indent=2)
PY
expect_fail "   manifest gate rejects a corpus at the wrong commit" gate_pins

echo "8. break a real theorem (no sorry)"
python3 - <<'PY'
p='lean/Cjson/Proofs/RoundTrip.lean'; s=open(p).read()
s=s.replace("  rw [parseDoc_eq, pv_congr hbom, h]", "  rw [parseDoc_eq]")
open(p,'w').write(s)
PY
expect_fail "   lake build rejects a genuinely broken proof" gate_build
( cd lean && lake build ) >/dev/null 2>&1

echo "9. drop a headline theorem from the attestation manifest"
python3 - <<'PY'
import json
p='release/manifest.json'; m=json.load(open(p))
m['attested_declarations'].remove('Cjson.parseDoc_idempotent')
json.dump(m, open(p,'w'), indent=2)
PY
expect_fail "   axiom gate rejects an attested theorem missing from the manifest" gate_axioms

echo "10. add a new claimed theorem without attesting it"
python3 - <<'PY'
p='lean/Cjson/Proofs/Str.lean'; s=open(p).read()
s=s.replace("end Cjson", "-- @attested brandNewTheorem\ntheorem brandNewTheorem : True := trivial\n\nend Cjson")
open(p,'w').write(s)
PY
( cd lean && lake build ) >/dev/null 2>&1
expect_fail "   axiom gate rejects an unattested new theorem" gate_axioms
python3 - <<'PY'
p='lean/Cjson/Proofs/Str.lean'; s=open(p).read()
s=s.replace("end Cjson", "theorem brandNewTheorem : True := trivial\n\nend Cjson")
open(p,'w').write(s)
PY
( cd lean && lake build ) >/dev/null 2>&1
expect_fail "   manifest gate rejects a theorem-count drift" gate_manifest
( cd lean && lake build ) >/dev/null 2>&1

echo
echo "11. control: unmutated tree must PASS every gate"
expect_pass "   axiom gate"    gate_axioms
expect_pass "   manifest gate" gate_manifest
expect_pass "   docs gate"     gate_docs
expect_pass "   figure gate"   gate_figures

echo
printf '== %d gate(s) fired correctly, %d BYPASS ==\n' "$PASS" "$FAIL"
[ "$FAIL" -eq 0 ] || { echo "*** A GATE CAN BE BYPASSED ***"; exit 1; }
echo "Every gate fires. No bypass found."
