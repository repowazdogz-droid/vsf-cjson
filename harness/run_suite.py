#!/usr/bin/env python3
"""Phase 3a: run BOTH binaries over the full JSONTestSuite corpus.

Reports two independent things, which must not be conflated:
  (1) ORACLE-vs-LEAN agreement  -- the differential test proper. This is what measures
      whether the Lean port faithfully replaces cJSON.
  (2) RFC conformance of EACH binary -- how each fares against JSONTestSuite's intent
      (y_ = must accept, n_ = must reject, i_ = implementation-defined). cJSON is a lax
      parser by design (SPEC S5.1 etc), so its n_ failures are NOT Lean bugs.
"""
import subprocess, sys, os, glob, json, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from classify import classify, LABELS

OUT = os.environ.get("VSF_RESULTS", "results/canonical")

ORACLE = "./oracle/cjson_oracle"
LEAN   = "./lean/.lake/build/bin/cjson"
SUITE  = "harness/JSONTestSuite/test_parsing"

def run(binary, data):
    try:
        p = subprocess.run([binary], input=data, capture_output=True, timeout=20)
        return p.returncode, p.stdout
    except subprocess.TimeoutExpired:
        return "TIMEOUT", b""

rows = []
for path in sorted(glob.glob(os.path.join(SUITE, "*.json"))):
    name = os.path.basename(path)
    data = open(path, "rb").read()
    oe, oo = run(ORACLE, data)
    le, lo = run(LEAN, data)
    rows.append(dict(name=name, kind=name[0], data=data.hex(),
                     oracle_exit=oe, oracle_out=oo.hex(),
                     lean_exit=le, lean_out=lo.hex(),
                     cls=classify(data, oe, oo, le, lo),
                     agree=(oe == le and oo == lo),
                     agree_accept=(oe == 0) == (le == 0)))

os.makedirs(OUT, exist_ok=True)
json.dump(rows, open(os.path.join(OUT, "suite_results.json"), "w"))

n = len(rows)
agree = sum(r["agree"] for r in rows)
agree_acc = sum(r["agree_accept"] for r in rows)
print(f"JSONTestSuite: {n} files")
print(f"  oracle==lean  (exit AND bytes) : {agree}/{n}")
print(f"  oracle==lean  (accept/reject)  : {agree_acc}/{n}")
print()

# RFC conformance of each binary, per class
def conforms(kind, exit_code):
    if kind == "y": return exit_code == 0
    if kind == "n": return exit_code != 0
    return None  # i_: either is allowed

for label, key in (("oracle (cJSON)", "oracle_exit"), ("lean port", "lean_exit")):
    c = collections.Counter()
    for r in rows:
        v = conforms(r["kind"], r[key])
        if v is None: c[f'{r["kind"]}_either'] += 1
        else: c[f'{r["kind"]}_{"pass" if v else "FAIL"}'] += 1
    ytot = c["y_pass"] + c["y_FAIL"]; ntot = c["n_pass"] + c["n_FAIL"]
    print(f'{label:16s} y_ accept {c["y_pass"]}/{ytot}   n_ reject {c["n_pass"]}/{ntot}')

print()
cls = collections.Counter(r["cls"] for r in rows)
print("classification (exactly one label per file):")
for L in LABELS:
    print(f'  {L:28s} {cls[L]}')
print(f'\nPORT_WRONG = {cls["PORT_WRONG"]}   UNCLASSIFIED = {cls["UNCLASSIFIED"]}')
div = [r for r in rows if not r["agree"]]
print(f"\nDIVERGENCES (oracle != lean): {len(div)}")
for r in div:
    print(f'  {r["kind"]}  {r["cls"]:28s} {r["name"]}')
