# REPRODUCE.md — Reproducibility

**Stop condition for this experiment:** an independent researcher can clone, build, rerun,
reproduce every theorem, every divergence, and every measurement, and understand every
remaining gap — **without asking the author a single question.**

This document is the checklist for that.

---

## 0. One command

```bash
./verify.sh              # ~15 min  (full: 120k fuzz)
./verify.sh --quick      # ~3 min   (20k fuzz; the 120k numbers in CLAIMS.md need the full run)
```

`verify.sh` **exits non-zero** if any of the following is true:

| check | fails when |
|---|---|
| 0. oracle integrity | `oracle/cJSON.c` or `cJSON.h` differs from upstream `fb16e5c` (sha256) |
| 1. oracle builds | the C wrapper does not compile |
| 2. Lean builds | any of the 90 theorems breaks (built from a **clean** `.lake/`) |
| 3. banned constructs | a `sorry`, `admit`, `native_decide`, custom `axiom`, or `@[extern]` appears |
| 4. axioms | any theorem depends on an axiom other than Lean's standard three |
| 5. JSONTestSuite | agreement is not 297/318 (bytes) and 317/318 (accept/reject) |
| 6. fuzz | agreement is not 116,476/120,000 |
| 7. idempotence | the compiled binary violates theorem T3 even once |

If it prints `ALL CLAIMS REPRODUCED`, every number in `CLAIMS.md` has just been regenerated on
your machine.

---

## 1. Environment

| | |
|---|---|
| Lean | **4.32.0** — pinned in `lean/lean-toolchain`; `elan` will fetch it |
| Lean deps | **Std only.** No Mathlib, no Batteries. `lean/lakefile.toml` has no `require`. |
| C compiler | any C99 (`cc`). Developed with Apple clang 17. |
| Python | 3.8+ for the harness. **Standard library only** — no pip install. |
| git | to clone JSONTestSuite (done automatically by `verify.sh`) |
| Platform | developed on macOS/arm64. Nothing is platform-specific; `verify.sh` uses `shasum` (use `sha256sum` on Linux — see §6). |

Disk: ~500 MB (mostly the Lean toolchain). Time: ~15 min for the full run, of which ~2 min is
Lean and ~10 min is the 120k fuzz (240,000 subprocess spawns).

## 2. From scratch

```bash
git clone <repo> && cd vsf-cjson
./verify.sh
```

That is all. `verify.sh` builds the oracle, wipes `lean/.lake/build` and rebuilds Lean from
source, clones JSONTestSuite if absent, and reruns every measurement.

## 3. Reproducing individual claims

**Theorems.** `cd lean && lake build`. The proof modules are imported by the default target on
purpose — `lake build` **fails** if any theorem breaks. (In v0.x they were *not*, and stale
`.olean` files masked four broken proofs while the build stayed green. That was a real bug; see
`REPORT.md` §5.)

**Axioms.**
```bash
cd lean && cat > /tmp/ax.lean <<'EOF'
import Cjson
open Cjson
#print axioms parseDoc_idempotent
EOF
lake env lean /tmp/ax.lean
```

**Differential vs. the oracle.**
```bash
python3 harness/run_suite.py       # JSONTestSuite, both binaries -> harness/suite_results.json
python3 harness/fuzz.py 120000     # -> harness/fuzz_results.json
python3 harness/idempotence.py     # -> harness/idempotence_results.json
python3 harness/diff.py            # 28 hand-picked probes, side by side
```

**Any single divergence in `DIVERGENCES.md`.** Every entry gives the exact input. E.g.:
```bash
printf '0.30000000000000004' | ./oracle/cjson_oracle          # 0.3   <- cJSON bug D-NUM-2
printf '0.30000000000000004' | ./lean/.lake/build/bin/cjson   # 0.30000000000000004
printf '"\\uZZZZ"'           | ./oracle/cjson_oracle; echo "exit=$?"   # ""   exit=0  <- bug D-STR-1
printf '"\\uZZZZ"'           | ./lean/.lake/build/bin/cjson;  echo "exit=$?"   #      exit=1
```

**Figures.** `python3 figures/make_figures.py` — they are drawn *from* `harness/fuzz_results.json`,
so they cannot drift from the numbers in `CLAIMS.md`.

## 4. Determinism

The fuzzer is seeded (`SEED = 20260714` in `harness/fuzz.py`) and its corpus is a pure function
of `(seed, index)`. Re-running gives byte-identical results. If your counts differ from
`CLAIMS.md`, something in the artifact changed — that is the point of the check.

The only nondeterminism is subprocess scheduling, which cannot affect the compared values (exit
code + stdout bytes).

## 5. What reproduction does **not** establish

Please read `GAPS.md` before drawing conclusions. In particular:

* A green `verify.sh` does **not** mean the parser accepts the right language. **No theorem in
  this artifact constrains the accept-set** (GAP-2). That is measured against a *buggy oracle*,
  and where the port and cJSON are wrong in the same way, the differential test is blind by
  construction.
* The **theorems are about Lean functions**; the **measurements are about a compiled binary**.
  The bridge between them is the idempotence cross-check, and nothing else (GAP-EXTRACT).

## 6. Linux / non-macOS

`verify.sh` uses `shasum -a 256`. On most Linux distributions:

```bash
sed -i 's/shasum -a 256/sha256sum/' verify.sh
```

Everything else is portable. If `cc` is not present, set `CC` and edit step 1.

## 7. Provenance

| | |
|---|---|
| oracle | `github.com/DaveGamble/cJSON` @ `fb16e5cf358798aabb049655975cde8427101056` |
| `oracle/cJSON.c` | sha256 `607e756460fa0de37d20a7a9181f2de29c97bfb7ce5a0e6c2f548243836cd852` |
| `oracle/cJSON.h` | sha256 `25b0145150d500498e4d209cec69c18c42cf818bffcc54690be3b895a2a16dee` |
| test corpus | `github.com/nst/JSONTestSuite` (cloned by `verify.sh`; not vendored) |

The C source is **never modified**. `verify.sh` step 0 fails if it has been.
