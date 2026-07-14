# REPORT.md — Verified Software Factory: cJSON → Lean 4

> **v1.0 update.** GAP-1 is **closed**. The structural canonicity lifting is now proven, and
> with it the headline theorem **T3** — `parseDoc s = some v → parseDoc (serialize v) = some v`,
> **unconditional**. See §5 for how, and why the route that worked was not the route that
> failed. GAP-2 (soundness against the grammar) remains open and is still the honest limit.

**Bottom line.** I produced a total, Mathlib-free Lean 4 replacement for cJSON's core
parse/serialize path, with machine-checked totality, round-trip, canonicity, and idempotence
theorems, and zero `sorry`. The differential test found **no bug in the Lean port** across 318
JSONTestSuite files and 120,000 fuzz inputs, and found **four real bugs in cJSON**. But the
proofs certify **something narrower than SPEC.md promises**: I proved the parser is *total* and
*self-consistent*, and I did **not** prove anything about which inputs the parser accepts —
which is most of what the spec actually says. The accept-set is tested, not proved. Details
in §6.

The single most useful result is not a theorem. It is that cJSON's round-trip is **lossy by
its own evident intent**, which means the property I was asked to prove in Phase 4b is *false
of the target*, and no amount of formalization effort could have made it true. Finding that
in Phase 1 rather than Phase 4 is the difference between an experiment and a waste of time.

---

## 1. What is in the box

```
oracle/       cJSON fb16e5c, UNMODIFIED, + a 62-line CLI wrapper
lean/         Lean 4.32.0 lake project, 2,229 lines, 90 theorems, 0 sorry
harness/      diff.py, run_suite.py, fuzz.py, idempotence.py
verify.sh     regenerates and re-checks EVERY claim; fails if any number moved
CLAIMS.md     every claim tagged PROVEN / MEASURED / OBSERVED / NOT PROVEN
SPEC.md       the contract, written before any Lean, every clause oracle-verified
DIVERGENCES.md  every observed difference, classified (a)/(b)/(c)/(d)
GAPS.md       what this artifact does NOT establish
LEDGER.md     preserved / changed / assumed / UNPROVED  ← read this one
```

Both binaries share an identical CLI contract (bytes on stdin, serialization on stdout, exit
code distinguishes accept/reject), so they are drop-in comparable.

## 2. Wall-clock narrative: what broke, in order

### Phase 0–1. My instruments broke before the subject did.

I read `cJSON.c` and wrote down seven predicted quirks. Then I probed the compiled binary
instead of trusting the reading. **Three of the seven were wrong**, and the way they were
wrong is the most honest thing in this report:

* *"`+1` and `.5` parse, because the number scanner accepts `+` and `.`"* — **wrong.** The
  scanner does, but `parse_value`'s dispatch gate requires `-` or a digit first. I had read
  the scanner in isolation and missed the caller's guard.
* *"A BOM followed by a 1-byte document fails (off-by-one in `skip_utf8_bom`)"* — **wrong
  under the chosen entry point.** The off-by-one is real in `cJSON_ParseWithLength(buf, len)`,
  but the NUL that `cJSON_Parse` appends to the length hides it. A latent bug, not a reachable
  one. I did not report it as a finding.
* *"A lone high surrogate `\ud800` is accepted"* — **wrong.** It is correctly rejected.

Two of those three refutations came from bugs **in my own probe scripts**: bash's `printf`
was silently interpreting `\uXXXX` escapes, so I was feeding the oracle actual UTF-8 bytes
instead of the literal backslash-u text I thought I was sending. I only caught it because the
results were *surprising* and I re-ran with byte-exact Python.

That pattern — the measurement apparatus failing before the thing being measured — repeated
twice more (§4). It is, I think, the main practical finding of this experiment.

### Phase 1. The crux, and why it changed everything.

Reading `print_number`, I found `compare_double`:

```c
static cJSON_bool compare_double(double a, double b) {
    double maxVal = fabs(a) > fabs(b) ? fabs(a) : fabs(b);
    return (fabs(a - b) <= maxVal * DBL_EPSILON);   /* ~1 ULP relative tolerance */
}
```

cJSON prints a number with `%1.15g`, re-reads it, and only falls back to 17 digits if the
re-read value "differs". But "differs" is that ~1-ULP tolerance, **not equality**. So:

| input | cJSON output | same IEEE double? |
|---|---|---|
| `0.30000000000000004` | `0.3` | **no** |
| `1.0000000000000002` | `1` | **no** |
| `9007199254740993` | `9.00719925474099e+15` | **no** |

`print(parse(x))` **is not value-preserving in the oracle.** The round-trip theorem I was
asked to prove in Phase 4b is *false of cJSON*. That is not a proof difficulty; it is a
property the target lacks.

I stopped and asked. Given the choice between (A) a bit-faithful clone with a hand-rolled
`strtod` — which would have made theorem (b) false of my port too, and put the single most
likely source of a silent bug at the centre of the artifact — and (B) modelling numbers
**exactly**, we took (B). The consequence is honest and legible: the proofs certify a clean
artifact, and every number divergence against the oracle becomes a *measurement* of how far
the real C is from anything provable.

The design decision that made the proofs tractable was choosing the AST's number
representation as a **canonical digit list** (`± digits × 10^exp`, no leading/trailing zeros)
rather than a `Nat` mantissa. This kept the round-trip theorem a *real normalisation
statement* — `100`, `1e2` and `1.0e2` all parse to the same node and must print back to one
canonical spelling — while eliminating an entire `Nat ↔ digits` inverse proof that would
otherwise have been the largest hidden cost.

### Phase 2. Totality came out better than expected.

I expected to need a fuel parameter and to have to declare a fuel bound in the ledger.
Instead: make every parser return a **subtype carrying the proof that it consumed at least
one byte**, and the decrease is available at each recursive call site. Lean's termination
checker then accepts the mutual block on the lexicographic measure
`(remaining bytes, 0 for parseValue / 1 for the loops)`.

**No fuel exists, so there is no fuel to exhaust and no bound to declare.** The 1000-deep
nesting limit is a semantic limit from the spec, not a termination device.

That subtype is also what caused most of the Lean pain later (§4). It was still the right
call.

### Phase 3. Differential testing, and my second broken instrument.

The first 120k fuzz run reported **22 UNKNOWN divergences** — the only category I actually
cared about. All 22 were a bug in my classifier: `json.loads(b"null")` legitimately returns
Python `None`, and I had used `None` as my "parse failed" sentinel. Twenty-two perfectly
ordinary D-NUM cases (`1e400` → `null`) were being reported as unclassifiable. Fixed with a
real sentinel object; re-ran.

The second run left exactly **one** UNKNOWN. It was also my classifier: Python's `Decimal`
caps exponents at ~1e999999 and *raises* on `1e400030000000000000004`. Both binaries had
behaved exactly as specified.

But chasing it surfaced a genuine finding **against my own port** — the only one — which is
now DIVERGENCES.md **D-LEAN-1**: modelling numbers exactly means the serializer will
faithfully emit an exponent of *any* magnitude. That output satisfies the RFC 8259 grammar,
but Python's `json` silently turns it into `inf` and `Decimal` refuses it outright. Exactness
has an interop cost, and I would not have found it without an instrument that broke.

### Phase 4. Proofs.

The number round-trip (`scanNumber_renderNum`) was the crux and took the longest. It needed:
a `SafeTail` precondition that is **load-bearing, not cosmetic** (the theorem is false without
it: `renderNum 1 = "1"`, and `scanNumber("1" ++ "2") = 12`); a printer refactored twice so its
four branches share one scanning lemma; and a clean separation of the *arithmetic* (which
digit lists each branch picks — `numParts_spec`) from the *byte-level scanning*
(`scanNumber_shape`). Both refactors were verified byte-identical against the oracle before
proceeding, so no behaviour was traded for provability.

The full structural round-trip then went through by mutual induction on `JSON.rec`.

Then I ran out of budget on the last mile, and stopped (§5).

## 3. Results

**JSONTestSuite (318 files)**

| | |
|---|---|
| identical exit code AND bytes | 297 / 318 |
| identical accept/reject | 317 / 318 |

| binary | `y_` accept | `n_` reject |
|---|---|---|
| oracle (cJSON) | 95/95 | 155/188 |
| Lean port | 95/95 | **156/188** |

The Lean port rejects one *more* invalid input than cJSON. The 32 shared `n_` failures are
cJSON's documented laxity (trailing garbage, lax numbers, control chars), replicated on
purpose.

**Differential fuzzing (120,000 inputs)**

| | count | share |
|---|---|---|
| agreement | 116,476 | 97.06% |
| D-STR-1 (invalid `\u` — cJSON bug) | 2,594 | 2.16% |
| D-FMT (same value, different spelling) | 408 | 0.34% |
| D-STR-2 (NUL truncation — cJSON bug) | 388 | 0.32% |
| D-NUM (cJSON double pipeline) | 133 | 0.11% |
| UNKNOWN | 1 | classifier artifact (§2) |

**Zero divergences in class (a) "Lean port is wrong".** Four real cJSON bugs found:
`1e400` → `null` (a number silently changes JSON *type*); 1-ULP precision loss; invalid
`\uXXXX` accepted as U+0000; embedded NUL truncates strings. Two of them
(`y_object_escaped_null_in_key`, `y_string_null_escape`) are JSONTestSuite files that cJSON
*accepts but answers wrong*.

**`#print axioms`** — all ten headline theorems return only Lean's three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`). Full output in `CLAIMS.md` §5, regenerated by
`./verify.sh` step 4, which **fails** if a non-standard axiom appears.

Those three are **Lean's standard axioms**, not project-specific ones. No `sorry`, no
`admit`, no `native_decide`, no custom axiom, no FFI, no dependency beyond Std.

## 4. Where AI formalization actually broke

This is what the experiment was for. The failures were **not** where I expected (the hard
mathematics); they were in tooling ergonomics, and several produced error messages that
pointed nowhere near the cause.

1. **`omega` silently refuses to unfold a reducible type abbreviation.** I wrote
   `abbrev Digit := Nat` for readability. Every `omega` call on a `Digit` then failed with
   *"No usable constraints found"* — a message that says nothing about type aliases. A
   one-line cosmetic definition disabled the main arithmetic tactic across the whole
   development. I lost real time before isolating it with a two-line repro. Deleting the
   alias fixed everything.

2. **The same abbreviation trick failed to unify in a mutual block's return type**, but
   worked fine standalone. `abbrev Bytes := List UInt8` would not unify with `List UInt8` in
   `Res JSON s` inside `mutual`. Same code compiled outside it. I did not diagnose the root
   cause; I worked around it.

3. **`ring`, `push_cast`, `set`, `interval_cases` are Mathlib, not core.** Hard Rule 5 forbade
   Mathlib, so I had to hand-roll the `Int` algebra. The fix was to restructure the proof to
   avoid `10^n` entirely (fold one digit at a time: `ofDigits (ds ++ [x]) = ofDigits ds * 10 + x`),
   which was *better* than the version that needed `ring`. Constraint improved the proof.

4. **Dependent match + subtype = "motive is not type correct", repeatedly.** The subtype that
   bought me fuel-free totality (§2) means `parseValue d s : Res JSON s` — the *return type
   depends on the argument*. Every attempt to rewrite `skipWs r → r` inside the parser's match
   failed. The fix, learned the hard way and applied five times: **keep `skipWs` in the
   lemma's statement and push the rewrite out to the caller**, where it is an ordinary
   hypothesis rewrite. Plus two helper lemmas (`pv_congr`, `parseDoc_eq`) whose entire purpose
   is to keep rewriting at the non-dependent `Option (JSON × Bytes)` level.

5. **`JSON.rec` emits two alternatives both named `nil` and two both named `cons`**, because
   the nested inductive has `List JSON` and `List (Bytes × JSON)`. `induction ... with |nil =>`
   is therefore ambiguous and rejected. Positional `refine ... ?_ ?_ ...` with ordered bullets
   was the way through.

6. **I appended a block of code after `end Cjson`**, so the entire parser core silently landed
   *outside its namespace*. The result was ~10 "unknown identifier `skipWs`" errors that read
   like a type error and sent me hunting in completely the wrong place for several iterations.

7. **`split` on a variable-headed match against eight literal patterns is a fight.** For
   `parseValue (c :: cs)` where `c` is a *variable* known to be `-` or a digit, the clean move
   turned out to be: prove `c` is one of **eleven concrete literals**, then `rcases` on them so
   the match reduces definitionally. Making the head literal was worth more than any tactic.

The honest generalization: **nothing broke in the mathematics.** Every genuine proof
obligation — the number normalisation, the four printer branches, the escape/unescape
identity, the mutual induction — went through once stated correctly. What broke was
(a) my measurement instruments, three times, and (b) the interaction between Lean's dependent
types and its tactic ergonomics. If you are budgeting for a project like this, budget for the
second, and do not trust the first.

## 5. GAP-1: the route that failed, and the route that worked

In v0.x I stopped short of the last mile and shipped an honest gap. That gap is now closed, and
*how* it closed is the most transferable engineering result in this project.

**The route that failed.** The obvious move is a mutual induction over `parseValue.induct` — the
functional-induction principle Lean generates for the WF-recursive mutual block. It exists. It
has **26 minor premises**, each carrying dependent-subtype hypotheses of the form
`parseValue depth s = some ⟨(v, r), hr⟩`, and each case then requires the same "motive is not
type correct" plumbing catalogued in §4.4. I abandoned it.

**The route that worked.** Put the invariant in the return type — the *same device* that had
already bought fuel-free totality:

```lean
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }

def parseValue (depth : Nat) (s : List UInt8) :
    Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s
```

The obligation is now discharged at ~8 construction sites inside the parser, using
`scanNumber_canonical` for the number node and the children's carried proofs for arrays and
objects. `parseDoc_canonical` and `parseDoc_depth` become one-line projections. Roughly an hour,
versus hours-and-abandoned for the induction principle.

**Two things I checked before believing it.**

1. *Did the behaviour change?* The invariants are `Prop`s, so they are erased at runtime — but
   "should be" is not "is". I re-ran the **entire** measurement suite. JSONTestSuite: 297/318
   and 317/318. Fuzz 120k: 116,476 agreements. Idempotence: 0 violations. **Byte-for-byte
   identical to the pre-change numbers.**

2. *Were the proofs actually being checked?* Closing GAP-1 surfaced a **release-critical bug in
   my own build**: `Cjson.lean` imported only `Basic`/`Parser`/`Printer`, so `lake build` was
   **not building the proof modules at all**. A reviewer running `lake build` would have checked
   zero theorems and seen a green light. Stale `.olean` files had been masking four broken
   rewrites (`if_neg` → `dif_neg`) introduced by the dependent-`if` change. Fixed by importing
   the proof modules into the default target — so `lake build` now *fails* if any theorem breaks
   — and by making `verify.sh` build from a clean `.lake/`.

   That is a fourth instrument failure (§2), and the most dangerous kind: it manufactured
   **false confidence** rather than a false alarm. It is exactly the failure mode a reviewer
   should assume is present in any "we have N theorems and zero sorry" claim.

**What GAP-1's closure bought:** T1's two hypotheses (`Canonical v`, `jdepth v ≤ 1000`) are now
*discharged*, not assumed, for anything the parser produced. So **T3** — *anything this parser
produces re-parses to itself* — is unconditional, and it is the theorem a user actually wants.

**What it did not buy:** T3 is a statement about the Lean function. The compiled binary is
produced by an unverified compiler and runtime. The 20,318-input idempotence run — which used to
be a *stand-in for an unproved theorem* — is now something different and still necessary: a
**cross-check that the extraction preserved the theorem**. It is the only evidence we have about
that step (GAP-EXTRACT).

## 6. Do the proofs certify what SPEC.md promises?

**No. They certify something distinctly narrower, and the gap is not small.**

SPEC.md is overwhelmingly a document about **which byte strings are accepted and what they
mean**: whitespace is any byte ≤ 32; trailing garbage is accepted; the number scanner is
`strtod`'s longest-valid prefix; `\uXXXX` must have four hex digits; the nesting limit is
1000; duplicate keys are preserved. That is the *accept-set* and the *value-map*.

What I proved:

* **Totality** (T0) — fully. Real, unconditional, and stronger than asked: no fuel at all.
* **Round-trip** (T1) — fully, within two stated hypotheses (canonical value; depth ≤ 1000).
* **Canonicity** (T2) — fully, structurally. Both of T1's hypotheses hold of anything parsed.
* **Idempotence** (T3) — fully, **unconditionally**. `parse ∘ serialize ∘ parse = parse`.

What I did **not** prove:

* **Anything about the accept-set.** Not one theorem in this deliverable says the parser
  rejects `[1,]`, or accepts `007`, or stops at 1000 levels of nesting. T1 runs in the *other*
  direction: it shows that things the serializer emits are accepted. That is a completeness
  statement about a subset of inputs, and it says nothing about inputs the serializer never
  produces — which is *all* the interesting ones.

So the load-bearing content of SPEC.md — sections S1, S2, S3.1, S4.1–S4.5, S5 — is **entirely
supported by testing, not by proof.** The evidence there is good (317/318 agreement on
accept/reject with the oracle; 119,999/120,000 on fuzz), but it is evidence.

Two further honest notes on the *testing*:

* The fuzz corpus is seeded from JSONTestSuite's `y_` files, whose maximum nesting depth is
  shallow. **The depth-limit boundary is essentially unfuzzed.** It is covered by exactly
  three hand-written probes (999 / 1000 / 1001 levels, all matching the oracle). If there is a
  bug in the port's depth accounting at, say, 500 levels inside an object-in-array chain, this
  corpus would very likely not find it.
* "No class-(a) divergence found" is a statement about **agreement with cJSON**, which is
  itself buggy. Where the Lean port and cJSON *both* do something wrong in the same way, the
  differential test is blind by construction. Both, for instance, accept trailing garbage and
  treat NUL as whitespace. The corpus cannot see that; only the RFC comparison in
  DIVERGENCES.md can, and that is a manual reading.

**A parser that accepted every byte string and returned `null` would satisfy T0, T1, T2 and T3
exactly as well as this one does.** That sentence is the honest measure of what four theorems and
zero `sorry` are worth without GAP-2, and it is the sentence I would lead with under hostile
review.

**The one-sentence version:** I can prove this parser always terminates and that it is faithfully
self-consistent; I *cannot yet prove* that it reads the language SPEC.md says it reads, and that
is the half of the spec that matters most.

## 7. Reproducing

```bash
cd oracle && cc -O2 -std=c99 -o cjson_oracle wrapper.c cJSON.c -lm
cd ../lean  && lake build                       # 0 errors, 0 sorry
python3 harness/run_suite.py                    # JSONTestSuite, both binaries
python3 harness/fuzz.py 120000                  # differential fuzz
python3 harness/idempotence.py 20000            # the GAP-1 stand-in
```

Skills applied: **operating-discipline** and **honest-claims** throughout (the proven /
tested / assumed separation in LEDGER §1 vs §4, and the §6 self-assessment);
**the-engine-method** at the Phase-1 crux (stopped at the conceptual decision rather than
pushing through a modelling choice); **comfortable-check-is-blind** on the clean fuzz result
(which is what prompted §6's note that a differential test against a buggy oracle is blind to
shared bugs); **propext-free-lean** for the axiom audit; **taste-and-anti-slop** on these
documents. **five-gate-novelty-check** did not fire — nothing here is claimed as novel.
