#!/usr/bin/env bash
#
# reproduce.sh — ONE command to rebuild and verify the entire GAP-2 adequacy proof from a
# clean checkout. No arguments. Exits non-zero on any failure.
#
#   ./reproduce.sh
#
# What it does, in order:
#   1. clean the Lean build tree                     (no reliance on stale .lake/build oleans)
#   2. build the released artifact                   (byte-identical to tag v1.0.1)
#   3. build the whole GAP-2 spec chain + statement pins  (Cjson.Spec.Checks)
#   4. run the GAP-2 gate                            (axioms, attestation, grammar freeze,
#                                                      Spec theorem count, released byte-identity)
#   5. confirm ADEQUACY_SUMMARY.md is a faithful regeneration of the compiled theorems
#
# The mathematics is not touched; this is reproducibility, not proof. See ADEQUACY_SUMMARY.md.
set -euo pipefail
cd "$(dirname "$0")"

hr() { printf '\n\033[1m== %s\033[0m\n' "$1"; }

hr "1/5  clean Lean build tree"
rm -rf lean/.lake/build
echo "  removed lean/.lake/build"

hr "2/5  build released artifact (v1.0.1, does not import the spec chain)"
( cd lean && lake build )

hr "3/5  build GAP-2 spec chain + statement pins (Cjson.Spec.Checks)"
( cd lean && lake build Cjson.Spec.Checks )

hr "4/5  GAP-2 gate — axioms, attestation, grammar freeze, released byte-identity"
python3 harness/gap2/check_gap2.py

hr "5/5  ADEQUACY_SUMMARY.md faithfully regenerates from the compiled theorems"
python3 harness/gap2/gen_adequacy_summary.py --check

printf '\n\033[1;32mGAP-2 ADEQUACY REPRODUCED.\033[0m  C2 ∧ C4 compiled, axiom-clean, statements pinned.\n'
printf 'See ADEQUACY_SUMMARY.md for the exact statements and axiom dependencies.\n'
