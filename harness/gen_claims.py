#!/usr/bin/env python3
"""Derive results/canonical/claims.json from the ACTUAL measurement outputs.

This is the single source of truth for every number that appears in the documentation.
Nothing here is hardcoded: every value is computed from the canonical result JSONs, the Lean
sources, or the oracle sources.

Pair with check_claims.py, which parses `<!-- claim:key=value -->` markers out of the docs
and compares them against this file. Neither script contains a documented number as a
literal, which is what makes the check non-circular.
"""
import json, glob, os, subprocess, pathlib

ROOT = pathlib.Path(__file__).resolve().parent.parent
CANON = ROOT / "results/canonical"
MAN = json.load(open(ROOT / "release/manifest.json"))

suite = json.load(open(CANON / "suite_results.json"))
fuzz = json.load(open(CANON / "fuzz_results.json"))
idem = json.load(open(CANON / "idempotence_results.json"))

y = [r for r in suite if r["kind"] == "y"]
n = [r for r in suite if r["kind"] == "n"]
fc = fuzz["counts"]

lean_files = sorted(glob.glob(str(ROOT / "lean/Cjson/**/*.lean"), recursive=True)) + \
             [str(ROOT / "lean/Main.lean")]
lean_lines = sum(len(open(f).readlines()) for f in lean_files)
theorem_count = sum(
    1 for f in lean_files for ln in open(f)
    if ln.startswith("theorem ") or ln.startswith("@[simp] theorem "))

claims = {
    # --- artifact size
    "lean_lines": lean_lines,
    "theorem_count": theorem_count,
    "oracle_c_lines": len(open(ROOT / "oracle/cJSON.c").readlines()),
    "wrapper_c_lines": len(open(ROOT / "oracle/wrapper.c").readlines()),
    "attested_decls": len(MAN["attested_declarations"]),

    # --- JSONTestSuite
    "suite_files": len(suite),
    "suite_byte_agree": sum(r["agree"] for r in suite),
    "suite_accept_agree": sum(r["agree_accept"] for r in suite),
    "suite_y_total": len(y),
    "suite_n_total": len(n),
    "suite_oracle_y_accept": sum(r["oracle_exit"] == 0 for r in y),
    "suite_lean_y_accept": sum(r["lean_exit"] == 0 for r in y),
    "suite_oracle_n_reject": sum(r["oracle_exit"] != 0 for r in n),
    "suite_lean_n_reject": sum(r["lean_exit"] != 0 for r in n),
    "suite_port_wrong": sum(r["cls"] == "PORT_WRONG" for r in suite),
    "suite_unclassified": sum(r["cls"] == "UNCLASSIFIED" for r in suite),

    # --- fuzz (every case carries exactly one label; see harness/classify.py)
    "fuzz_n": fuzz["n"],
    "fuzz_seed": fuzz["seed"],
    "fuzz_agree": fc["AGREE"],
    "fuzz_agree_pct": f"{100.0 * fc['AGREE'] / fuzz['n']:.2f}",
    "fuzz_port_wrong": fc["PORT_WRONG"],
    "fuzz_target_wrong": fc["TARGET_WRONG_OR_DIFFERENT"],
    "fuzz_intentional": fc["INTENTIONAL_SEMANTIC_CHANGE"],
    "fuzz_harness_error": fc["HARNESS_ERROR"],
    "fuzz_unclassified": fc["UNCLASSIFIED"],

    # --- idempotence cross-check
    "idem_checked": idem["checked"],
    "idem_accepted": idem["accepted"],
    "idem_violations": idem["violations"],

    # --- pinned inputs
    "jsontestsuite_commit": MAN["pinned_inputs"]["jsontestsuite"]["commit"],
    "oracle_commit": MAN["pinned_inputs"]["oracle"]["commit"],
    "lean_toolchain": MAN["lean_toolchain"],
}

CANON.mkdir(parents=True, exist_ok=True)
out = CANON / "claims.json"
json.dump(claims, open(out, "w"), indent=1, sort_keys=True)
print(f"wrote {out} — {len(claims)} canonical claims")
for k, v in sorted(claims.items()):
    print(f"  {k:26s} {v}")
