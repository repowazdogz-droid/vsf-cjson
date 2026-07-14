# Verified Software Factory — cJSON → Lean 4

**v1.0.1** · Lean leanprover/lean4:v4.32.0 (Std only, no Mathlib) <!-- claim:lean_toolchain=leanprover/lean4:v4.32.0 -->
· oracle: [cJSON](https://github.com/DaveGamble/cJSON) @ `fb16e5cf358798aabb049655975cde8427101056`, **unmodified** <!-- claim:oracle_commit=fb16e5cf358798aabb049655975cde8427101056 -->
· corpus: [JSONTestSuite](https://github.com/nst/JSONTestSuite) @ `1ef36fa01286573e846ac449e8683f8833c5b26a` (pinned) <!-- claim:jsontestsuite_commit=1ef36fa01286573e846ac449e8683f8833c5b26a -->

An instrumented experiment, not a product. The question is not *"can we build a verified JSON
parser"* — people have. The question is:

> **How far can an AI agent translate a real C library into Lean while preserving semantics,
> and where does the process actually break?**

So the C source is the **oracle**: never edited, sha256-checked on every run. Every behavioural
difference between it and the Lean port is recorded as a **finding**, not patched away.

```bash
./verify.sh                    # ~20 min. 16 gates. Fails if anything drifts.
./verify.sh --quick            # ~4 min. Proof/axiom/manifest gates only; leaves the tree clean.
./harness/mutation_tests.sh    # ~15 min. Proves every gate actually FIRES (20 attacks).
```

**Read this before trusting any green check here.** `lake build` does **not** reject `sorry` —
Lean emits a warning, not an error. The gates that reject it are (a) a scan of a *fresh* build's
output for ``declaration uses `sorry` `` and (b) the **axiom gate**, which parses
`#print axioms` for all 11 attested declarations and compares the axiom *set* against an
allow-list, catching `sorryAx` and any custom axiom structurally. v1.0.0 shipped an axiom gate
that **could not fire** — `harness/mutation_tests.sh` exists so that never goes unnoticed
again: it injects axioms, `sorry`s, falsified numbers, tampered figures and manifest drift, and
requires every gate to fail.

---

## The one-paragraph result

The port is **2,240 lines of Lean, 90 theorems, zero `sorry`, zero project axioms**. <!-- claim:lean_lines=2240 --><!-- claim:theorem_count=90 -->
We prove totality (with *no fuel parameter*), a round-trip theorem, a canonicity invariant, and
— unconditionally — that anything the parser produces re-parses to itself. Differential testing
over JSONTestSuite (318 files) and 120,000 fuzzed inputs measured **PORT_WRONG = 0** — zero cases <!-- claim:suite_files=318 --><!-- claim:fuzz_n=120000 --><!-- claim:fuzz_port_wrong=0 -->
where the Lean port is wrong — and found **four genuine bugs in cJSON**.

But the headline finding is not a theorem. It is that **cJSON's round-trip is lossy by its own
evident intent**, which means the property we were asked to prove in Phase 4 was *false of the
target*. We found that in the specification phase. Had we found it in the proof phase, the
locally-rational move — weaken the theorem until it compiles — would have produced a green
build that certified nothing.

**And: we prove nothing about which inputs the parser accepts.** That is most of what our own
specification says, and it is measured, not proved. See [`GAPS.md`](GAPS.md) §GAP-2. This
artifact should **not** be described as "a verified JSON parser" without that qualification.

---

## Claim discipline

Every claim in this repo carries exactly one tag. Nothing blurs them.

| tag | meaning | where |
|---|---|---|
| **PROVEN** | kernel-checked in Lean. `lake build` catches a broken *proof*; the **axiom gate** (`harness/check_axioms.py`) is what rejects `sorry` and custom axioms — see below | [`CLAIMS.md`](CLAIMS.md) §1 |
| **MEASURED** | produced by a script in `harness/`, deterministic seed | [`CLAIMS.md`](CLAIMS.md) §2 |
| **OBSERVED** | fact about the C, established by probing the compiled oracle | [`CLAIMS.md`](CLAIMS.md) §3 |
| **NOT PROVEN** | explicitly outside the proofs' reach | [`CLAIMS.md`](CLAIMS.md) §4, [`GAPS.md`](GAPS.md) |

### PROVEN

| | theorem |
|---|---|
| **T0** | `parseValue`/`parseElems`/`parseMembers` are total. **No fuel parameter exists.** |
| **T1** | `Canonical v → jdepth v ≤ 1000 → parseDoc (serialize v) = some v` |
| **T2** | `parseDoc s = some v → Canonical v ∧ jdepth v ≤ 1000` (carried in the parser's *type*) |
| **T3** | `parseDoc s = some v → parseDoc (serialize v) = some v` — **unconditional** |

Axioms: `propext`, `Classical.choice`, `Quot.sound` — Lean's standard three, no project axioms.

### MEASURED

| | | |
|---|---|---|
| JSONTestSuite, byte-identical output | **297 / 318** | <!-- claim:suite_byte_agree=297 --> |
| JSONTestSuite, identical accept/reject | **317 / 318** | <!-- claim:suite_accept_agree=317 --> |
| RFC conformance (`n_` reject): cJSON vs. Lean | 155/188 vs. **156/188** | <!-- claim:suite_oracle_n_reject=155 --><!-- claim:suite_lean_n_reject=156 --><!-- claim:suite_n_total=188 --> |
| Fuzz, 120,000 inputs: exact agreement | **116,476 (97.06%)** | <!-- claim:fuzz_agree=116476 --><!-- claim:fuzz_agree_pct=97.06 --> |
| Fuzz: **PORT_WRONG** (directly counted, not inferred) | **0** | <!-- claim:fuzz_port_wrong=0 --> |
| Fuzz: **UNCLASSIFIED** (a finding if nonzero) | **0** | <!-- claim:fuzz_unclassified=0 --> |
| Idempotence cross-check, 20,318 inputs | **0 violations** | <!-- claim:idem_checked=20318 --><!-- claim:idem_violations=0 --> |

### OBSERVED — four genuine cJSON bugs

| | |
|---|---|
| `1e400` → `null` | a number silently changes its JSON **type** (`strtod`'s `errno` never checked) |
| `0.30000000000000004` → `0.3` | a **different IEEE double** — `compare_double` uses a ~1-ULP tolerance |
| `"\uZZZZ"` → `""` | **invalid input accepted as valid** — `parse_hex4` cannot distinguish `0000` from garbage |
| `{"foo\0bar":42}` → `{"foo":42}` | content **silently discarded** at an embedded NUL |

### NOT PROVEN

* **GAP-2** — soundness against the SPEC grammar. *No theorem here says which inputs the parser
  accepts.* The accept-set is measured, and the differential test is blind by construction to
  bugs the port and cJSON *share*.
* **GAP-EXTRACT** — the compiled binary is not the verified object (Lean's compiler/runtime are
  unverified).
* **GAP-3** — no exponent bound; exact numbers can emit output most JSON consumers choke on.
  *The one finding against our own port.*

---

## Where the process broke

Not in the mathematics. Every real proof obligation went through once stated correctly.

**Our instruments broke three times.** Bash's `printf` silently ate `\uXXXX` in our probe
scripts (killing three early "findings"); our fuzz classifier conflated `json.loads("null") →
None` with parse failure (mis-flagging 22 real divergences); Python's `Decimal` then overflowed
on a huge exponent. In an AI-driven pipeline the harness is code too — written with the same
fluency and the same overconfidence — and it is **not** protected by a kernel.

**Lean's ergonomics cost more than its logic.** Seven documented failures, several with error
messages pointing nowhere near the cause. The sharpest: `omega` silently refuses to unfold
`abbrev Digit := Nat`, so a one-line cosmetic type alias disabled the main arithmetic tactic
across the whole development, reporting only *"No usable constraints found."*

Full account: [`PAPER.md`](PAPER.md) §5, [`REPORT.md`](REPORT.md).

---

## Method note worth stealing

For a recursive-descent parser defined by **well-founded recursion**, put the invariant in the
**return type**:

```lean
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }
```

That one device gave us, in sequence: fuel-free **totality** (the decrease is in scope at each
call site), then **canonicity**, then the **depth bound** — each discharged at ~8 construction
sites. The alternative, `parseValue.induct` (the induction principle Lean generates for the
WF-recursive mutual block), has **26 minor premises** and we abandoned it. The type-strengthening
route took about an hour.

The invariants are `Prop`s, so they are erased at runtime: we re-ran the full differential suite
and the emitted bytes are **identical**.

---

## Layout

```
oracle/         cJSON fb16e5c, UNMODIFIED + a 62-line CLI wrapper
lean/           Lean 4.32.0 lake project — 2,229 lines, 90 theorems, 0 sorry
harness/        run_suite.py · fuzz.py · idempotence.py · diff.py
figures/        SVGs; verify.sh regenerates them into a temp dir and byte-compares
verify.sh       regenerates and re-checks every claim in this repo

PAPER.md        the write-up (6–10pp)
CLAIMS.md       every claim, tagged PROVEN / MEASURED / OBSERVED / NOT PROVEN
SPEC.md         the contract — written BEFORE any Lean; every clause oracle-probed
DIVERGENCES.md  every divergence, classified (a) port wrong / (b) cJSON bug / (c) ambiguity / (d) deliberate
GAPS.md         what this artifact does NOT establish
LEDGER.md       preserved / changed / assumed / unproved
REPORT.md       wall-clock narrative of failures and recoveries
```

Both binaries share an identical CLI contract — bytes on stdin, serialization on stdout, exit
code distinguishes accept/reject — so they are drop-in comparable:

```bash
printf '0.30000000000000004' | ./oracle/cjson_oracle          # 0.3          <- cJSON bug
printf '0.30000000000000004' | ./lean/.lake/build/bin/cjson   # 0.30000000000000004
```

## Licence

cJSON in `oracle/` is MIT (Dave Gamble and contributors) — see `oracle/LICENSE`, unmodified.
Everything else in this repository: MIT.
