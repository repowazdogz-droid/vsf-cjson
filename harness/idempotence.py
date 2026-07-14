#!/usr/bin/env python3
"""Empirical stand-in for the ONE theorem we did not finish mechanizing.

We proved:
  T1  Canonical v  ∧  jdepth v ≤ 1000  →  parseDoc (serialize v) = some v
  T2  every number the scanner builds is canonical
but NOT the structural lifting of T2 (that every number *inside* a parsed tree is
canonical). Without it, the composite

  T3   parseDoc s = some v  →  parseDoc (serialize v) = some v

is not mechanized. T3 is exactly observable at the CLI: running the Lean binary twice
must be the same as running it once. This script measures that on every corpus we have.

A pass here is EVIDENCE, not proof. It is reported as such in REPORT.md.
"""
import subprocess, sys, os, glob, json, random

LEAN = os.path.abspath("./lean/.lake/build/bin/cjson")


def run(data):
    p = subprocess.run([LEAN], input=data, capture_output=True, timeout=20)
    return p.returncode, p.stdout


def check(data):
    """Return None if idempotent, else a description of the failure."""
    e1, o1 = run(data)
    if e1 != 0:
        return None                       # rejected: nothing to re-serialize
    e2, o2 = run(o1)
    if e2 != 0:
        return f"second parse REJECTED its own output: {o1[:80]!r}"
    if o1 != o2:
        return f"not idempotent: {o1[:60]!r} -> {o2[:60]!r}"
    return None


def main():
    inputs = []
    for p in sorted(glob.glob("harness/JSONTestSuite/test_parsing/*.json")):
        inputs.append(open(p, "rb").read())

    # replay the fuzz corpus deterministically (same seed//generator as fuzz.py)
    sys.path.insert(0, "harness")
    import fuzz
    n_fuzz = int(sys.argv[1]) if len(sys.argv) > 1 else 20000
    inputs += [fuzz.gen(i) for i in range(n_fuzz)]

    fails = []
    for i, data in enumerate(inputs):
        r = check(data)
        if r:
            fails.append((data, r))
        if (i + 1) % 5000 == 0:
            print(f"  {i+1}/{len(inputs)} ...", flush=True)

    print(f"\n=== idempotence (parse . serialize . parse == parse) ===")
    print(f"  inputs checked : {len(inputs)}")
    print(f"  accepted       : {sum(1 for d in inputs if run(d)[0] == 0)}")
    print(f"  VIOLATIONS     : {len(fails)}")
    for d, r in fails[:10]:
        print(f"    {d[:60]!r}: {r}")
    json.dump({"checked": len(inputs), "violations": len(fails),
               "examples": [[d.hex(), r] for d, r in fails[:20]]},
              open("harness/idempotence_results.json", "w"), indent=1)


if __name__ == "__main__":
    main()
