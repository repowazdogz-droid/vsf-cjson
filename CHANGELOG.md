# CHANGELOG

## v1.0.1 — verification-harness repair

**The mathematics is unchanged. The evidence pipeline was broken and has been rebuilt.**

v1.0.0 was **rejected by hostile audit**. Not one theorem was wrong — but the harness that
certified them could not detect an axiom-contaminated build, and said so in green. For an
artifact whose thesis is *"the harness is the weak link"*, that was disqualifying on its own
terms. **v1.0.0 is superseded and must not be cited.**

### What was actually broken (all six confirmed by injection)

| # | defect | v1.0.0 behaviour |
|---|---|---|
| B1 | **axiom gate could not fire** | `grep -qv -E "…\|depends on axioms"` — every line contains that substring, so the inverted match never matched. A custom axiom, and even `sorryAx`, **passed**. The source grep was anchored `^axiom `, so indentation evaded it too. Demonstrated: `evilAxiom` threaded into `parseDoc_idempotent`, printed on screen, then *"PASS — no project axioms."* |
| B2 | **`lake build` does not reject `sorry`** | Lean emits a *warning*, not an error. README/CHANGELOG/REPORT/REPRODUCE all claimed it did. Only a textual grep caught it. |
| B3 | **documentation check was circular** | `check_claims.py` never opened a `.md` file; its "docs=" column was hardcoded literals in the script. Falsifying README/PAPER/CLAIMS left it passing. |
| B4 | **figures could drift** | `make_figures.py` was never run by `verify.sh`, while README claimed the figures *"cannot drift"*. |
| B5 | **corpus unpinned** | JSONTestSuite cloned at upstream HEAD. Every differential number depended on a repository that can change without notice. |
| B6 | **`--quick` dirtied tracked results** | The advertised first command overwrote the committed canonical JSONs. |
| 2nd | **`PORT_WRONG` was never measured** | The headline "zero cases where the Lean port is wrong" was inferred from a `UNKNOWN-exit` counter that no classifier ever emitted. |

### What replaces them

* **`harness/check_axioms.py`** — rebuilds first (so it cannot read stale `.olean`s), runs
  `#print axioms` for all 11 attested declarations, **parses** the output, set-compares against
  an allow-list, and **fails closed** on a missing declaration or unparseable line.
* **`release/manifest.json` + `harness/check_manifest.py`** — the attested set is cross-checked
  against `-- @attested` markers in the Lean source **in both directions**, so it cannot shrink
  with the source and a new claimed theorem cannot go unattested. Theorem count, proof modules
  in the default build target, pins and toolchain are all fixed points.
* **`harness/gen_claims.py` + `check_claims.py`** — documented numbers carry machine-readable
  markers; `claims.json` is *generated from the measurements*; the checker *parses the `.md`
  files*. Neither script contains a documented number as a literal. Markers must be **adjacent**
  to the prose number they attest, so falsifying the prose alone fails.
* **Figure gate** — figures regenerate deterministically into a temp dir and are **byte-compared**.
* **Pinned corpus** — JSONTestSuite `1ef36fa01286573e846ac449e8683f8833c5b26a`, **fail-closed**.
* **`results/canonical/` vs `results/quick/`** — `--quick` cannot touch the canonical data and
  says plainly that it cannot establish the documented numbers.
* **`harness/classify.py`** — every differential case gets exactly one of `AGREE`, `PORT_WRONG`,
  `TARGET_WRONG_OR_DIFFERENT`, `INTENTIONAL_SEMANTIC_CHANGE`, `HARNESS_ERROR`, `UNCLASSIFIED`.
  The public claim now derives from a **directly-counted `PORT_WRONG`**. `PORT_WRONG` is decided
  by rules that do *not* use any signature we chose, so a port bug cannot be laundered into the
  "intentional" bucket. The rules encode human judgement and say so.
* **`harness/mutation_tests.sh`** — **20 attacks; every gate must FAIL.** This is the real
  deliverable of v1.0.1: *a gate that has never been shown to fail is not evidence.*

### Found by the mutation suite while building it

Two further defects, caught only because the attacks were actually run:

* `check_axioms.py` read **stale `.olean` files** — a mutated proof sailed through because
  nothing rebuilt. It now rebuilds and fails closed.
* the `sorry` scan grepped for `'sorry'`; **Lean renders it with backticks** — `` declaration
  uses `sorry` `` — so the gate silently never fired. Fixed at all three call sites.

### Measurements

Re-run from the pinned corpus. Agreement figures are unchanged (`116,476/120,000`, `297/318`,
`317/318`, 0 idempotence violations). The fuzz *breakdown* is re-expressed under the new
classification, and `HARNESS_ERROR` is now a named bucket (22) instead of a silent one.
`lean_lines` rose from 2,229 to 2,240 (the `@attested` markers).

**Public behaviour of the binaries is unchanged.** Hence a patch release, not a minor one.

---

## v1.0.0 — SUPERSEDED (do not cite)

Rejected by final release audit: six release blockers in the verification harness. The
mathematics was sound — `#print axioms` on the unmodified tree genuinely returned only Lean's
three standard axioms, and there genuinely was no `sorry` — but nothing in the pipeline could
have *established* that, and several checks that appeared to establish it could not fire.

GAP-1 was closed in this release (structural canonicity carried in the parser's return type,
making T3 unconditional); that work is retained unchanged in v1.0.1.

## v0.x — pre-release
Phases 0–4: oracle vendored, SPEC written and oracle-verified, Lean port, differential testing,
proofs of totality / round-trip / number-canonicity. GAP-1 and GAP-2 shipped open and honest.
