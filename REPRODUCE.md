# REPRODUCE.md — Reproducibility

**Stop condition for this experiment:** an independent researcher can clone, build, rerun,
reproduce every theorem, every divergence, and every measurement, and understand every
remaining gap — **without asking the author a single question.**

This document is the checklist for that.

---

## 0. One command

```bash
./verify.sh                    # ~20 min  (full: 120k fuzz; establishes the documented numbers)
./verify.sh --quick            # ~4 min   (proof/axiom/manifest gates; writes to results/quick/,
                               #           leaves the tree clean; CANNOT establish the numbers)
./harness/mutation_tests.sh    # ~15 min  (proves every gate fires; restores the tree itself)
```

`verify.sh` **exits non-zero** if any of the following is true:

| gate | what it ACTUALLY establishes | fails when |
|---|---|---|
| 1. oracle pin | the C is the pinned upstream source | sha256 of `cJSON.c`/`cJSON.h` differs |
| 2. corpus pin | JSONTestSuite is at the pinned commit | the exact commit cannot be checked out (**fails closed**) |
| 3. oracle builds | — | the wrapper does not compile |
| 4. `lake build` | **elaboration + type-correctness only.** It does **NOT** reject `sorry`. | a proof genuinely fails to elaborate |
| 5. sorry gate | a *fresh* build emits no ``declaration uses `sorry` `` | any declaration uses `sorry` |
| 6. **axiom gate** | **`#print axioms` for all 11 attested declarations, parsed, set-compared to an allow-list.** This is what rejects `sorry` (as `sorryAx`) and any custom axiom. Fails closed. | a disallowed axiom, a missing declaration, or unparseable output |
| 7. banned constructs | belt-and-braces source scan; **not** the primary gate | textual `sorry`/`admit`/`native_decide`/`@[extern]` |
| 8. manifest | the attested set cannot shrink with the source; proof modules are in the default build target; pins/toolchain match | any drift |
| 9–11. differential | suite / fuzz / idempotence runs | a run errors |
| 12. PORT_WRONG | **directly counted**, not inferred | any case is `PORT_WRONG` or `UNCLASSIFIED` |
| 13. claims | `claims.json` regenerated **from** the measurements | — |
| 14. figures | figures regenerated to a temp dir and **byte-compared** | a figure is hand-edited or stale |
| 15. docs | every number is parsed **out of the .md files** and compared to the generated claims | a documented number is falsified, unattested, phantom, self-contradictory, or not adjacent to its marker |
| 16. clean tree | verification is idempotent | verification modified tracked files |

**Prove the gates actually fire:** `./harness/mutation_tests.sh` runs 20 attacks (custom axiom
indented and section-scoped, `sorry`, falsified README/PAPER/CLAIMS, removed marker, tampered
SVG, stale figures, stale docs, broken corpus pin, broken theorem, manifest drift) and requires
every gate to FAIL. It restores the repository automatically. v1.0.0's gates had never been
shown to fail; three of them could not.

---

## 1. Environment

| | |
|---|---|
| Lean | **4.32.0** — pinned in `lean/lean-toolchain`; `elan` will fetch it |
| Lean deps | **Std only.** No Mathlib, no Batteries. `lean/lakefile.toml` has no `require`. |
| C compiler | any C99 (`cc`). Developed with Apple clang 17. |
| Python | 3.8+ for the harness. **Standard library only** — no pip install. |
| git | to clone JSONTestSuite (done automatically by `verify.sh`) |
| Platform | developed on macOS/arm64. Nothing is platform-specific (hashing is done in Python). |

Disk: ~500 MB (mostly the Lean toolchain). Time: ~20 min for the full run, of which ~2 min is
Lean and ~13 min is the 120k fuzz (240,000 subprocess spawns).

## 2. From scratch

```bash
git clone <repo> && cd vsf-cjson
./verify.sh
```

That is all. `verify.sh` builds the oracle, wipes `lean/.lake/build` and rebuilds Lean from
source, clones JSONTestSuite if absent, and reruns every measurement.

## 3. Reproducing individual claims

**Theorems.** `cd lean && lake build` — this establishes elaboration and type-correctness, and
it **fails on a broken proof**. It does **not** reject `sorry`. For that, and for custom axioms,
run `python3 harness/check_axioms.py`, which rebuilds first (so it cannot read stale `.olean`s),
then parses `#print axioms` for all 11 attested declarations and set-compares against the
allow-list. Both gates are in `verify.sh`.

**Axioms.**
```bash
cd lean && cat > /tmp/ax.lean <<'EOF'
import Cjson
open Cjson
#print axioms parseDoc_idempotent
EOF
lake env lean /tmp/ax.lean
```

**Differential vs. the oracle.** All runners honour `VSF_RESULTS` (default `results/canonical`).
```bash
python3 harness/run_suite.py                     # -> results/canonical/suite_results.json
python3 harness/fuzz.py 120000                   # -> results/canonical/fuzz_results.json
python3 harness/idempotence.py 20000             # -> results/canonical/idempotence_results.json
python3 harness/gen_claims.py                    # -> results/canonical/claims.json (from the above)
VSF_RESULTS=/tmp/x python3 harness/fuzz.py 5000  # scratch run; touches nothing tracked
```
Every case carries exactly one label (`harness/classify.py`); `PORT_WRONG` is directly counted.

**Any single divergence in `DIVERGENCES.md`.** Every entry gives the exact input. E.g.:
```bash
printf '0.30000000000000004' | ./oracle/cjson_oracle          # 0.3   <- cJSON bug D-NUM-2
printf '0.30000000000000004' | ./lean/.lake/build/bin/cjson   # 0.30000000000000004
printf '"\\uZZZZ"'           | ./oracle/cjson_oracle; echo "exit=$?"   # ""   exit=0  <- bug D-STR-1
printf '"\\uZZZZ"'           | ./lean/.lake/build/bin/cjson;  echo "exit=$?"   #      exit=1
```

**Figures.** `python3 figures/make_figures.py [OUTDIR]` — drawn from `results/canonical/*.json`
and **deterministic**. `verify.sh` gate 14 regenerates them into a temp dir and byte-compares
against the committed SVGs, so a hand-edited or stale figure fails the release.

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

Hashing is done in Python (`hashlib`), not `shasum`, so `verify.sh` is portable as written.
Requirements are `bash`, `git`, `cc` (any C99), `python3` (stdlib only) and `elan`/`lake`.

## 7. Provenance

| | |
|---|---|
| oracle | `github.com/DaveGamble/cJSON` @ `fb16e5cf358798aabb049655975cde8427101056` |
| `oracle/cJSON.c` | sha256 `607e756460fa0de37d20a7a9181f2de29c97bfb7ce5a0e6c2f548243836cd852` |
| `oracle/cJSON.h` | sha256 `25b0145150d500498e4d209cec69c18c42cf818bffcc54690be3b895a2a16dee` |
| test corpus | `github.com/nst/JSONTestSuite` @ `1ef36fa01286573e846ac449e8683f8833c5b26a` (**pinned**; cloned and checked out by `verify.sh`, which **fails closed** if that exact commit cannot be fetched) |
| Lean toolchain | `leanprover/lean4:v4.32.0` (`lean/lean-toolchain`) |
| Lean packages | none (`lake-manifest.json` packages == `[]`) |
| Python packages | none (stdlib only) |

All pins live in `release/manifest.json` and are enforced by `harness/check_manifest.py`.
The C source is **never modified**; gate 1 fails if it has been.
