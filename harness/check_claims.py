#!/usr/bin/env python3
"""Cross-check every number asserted in the documentation against the artifact on disk.

This exists because the docs and the data drift, and a reviewer has no way to tell. It caught
a real one during the v1.0 release: a --quick run had overwritten the idempotence results with
a 5,318-input figure while CLAIMS.md still asserted 20,318.

Run from the repo root. Exits non-zero on any mismatch. Wired into verify.sh.
"""
import json, subprocess, glob, sys

FAILED = []


def chk(name, actual, claimed):
    good = str(actual) == str(claimed)
    if not good:
        FAILED.append(name)
    print(f"  {'ok  ' if good else 'FAIL'}  {name:34s} artifact={actual!s:<10} docs={claimed}")


def sh(cmd):
    return subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout.strip()


# ---- artifact size (asserted in README, PAPER, CLAIMS, REPORT)
loc = sum(len(open(f).readlines()) for f in
          glob.glob("lean/Cjson/*.lean") + glob.glob("lean/Cjson/Proofs/*.lean") + ["lean/Main.lean"])
chk("Lean lines", loc, 2229)
chk("theorems", int(sh(r"grep -h '^theorem \|^@\[simp\] theorem ' "
                       r"lean/Cjson/*.lean lean/Cjson/Proofs/*.lean | wc -l")), 90)
chk("cJSON.c lines (oracle)", len(open("oracle/cJSON.c").readlines()), 3206)
chk("wrapper.c lines", len(open("oracle/wrapper.c").readlines()), 62)

# ---- JSONTestSuite (RESULTS.md, CLAIMS.md, README)
rows = json.load(open("harness/suite_results.json"))
y = [r for r in rows if r["kind"] == "y"]
n = [r for r in rows if r["kind"] == "n"]
chk("suite: files", len(rows), 318)
chk("suite: byte-identical", sum(r["agree"] for r in rows), 297)
chk("suite: accept/reject agree", sum(r["agree_accept"] for r in rows), 317)
chk("suite: oracle y_ accept", sum(r["oracle_exit"] == 0 for r in y), 95)
chk("suite: lean   y_ accept", sum(r["lean_exit"] == 0 for r in y), 95)
chk("suite: oracle n_ reject", sum(r["oracle_exit"] != 0 for r in n), 155)
chk("suite: lean   n_ reject", sum(r["lean_exit"] != 0 for r in n), 156)
chk("suite: n_ total", len(n), 188)

# ---- fuzz (RESULTS.md, CLAIMS.md, README, figure 2)
f = json.load(open("harness/fuzz_results.json"))
c = f["counts"]
chk("fuzz: inputs", f["n"], 120000)
chk("fuzz: agreement", c["AGREE"], 116476)
chk("fuzz: agreement %", f"{100 * c['AGREE'] / f['n']:.2f}", "97.06")
chk("fuzz: D-STR-1", c["D-STR-1"], 2594)
chk("fuzz: D-FMT", c["D-FMT"], 408)
chk("fuzz: D-STR-2", c["D-STR-2"], 388)
chk("fuzz: D-NUM", c["D-NUM"], 133)
chk("fuzz: UNKNOWN", c.get("UNKNOWN-unparseable", 0), 1)
chk("fuzz: class (a) port-wrong", c.get("UNKNOWN-exit", 0), 0)

# ---- idempotence (RESULTS.md, CLAIMS.md, GAPS.md)
i = json.load(open("harness/idempotence_results.json"))
chk("idempotence: inputs", i["checked"], 20318)
chk("idempotence: violations", i["violations"], 0)

if FAILED:
    print(f"\n*** {len(FAILED)} DOC/ARTIFACT MISMATCH: {', '.join(FAILED)}")
    print("*** The documentation asserts numbers the artifact does not produce. Fix one of them.")
    sys.exit(1)
print("\nAll documented numbers match the artifact on disk.")
