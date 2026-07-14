# GAPS.md — Known Gaps

What this artifact does **not** establish. Written so a hostile reviewer finds nothing here
they could have used against us that we did not say first.

Each gap states: the precise unproved statement, why it is not proved, what evidence (if any)
stands in its place, and what it would take to close.

---

## GAP-1 — CLOSED (v1.0)

*Was:* the structural lifting of canonicity — that every number *inside* a parsed tree is
canonical, not merely every number the scanner returns.

**Closed.** Rather than the 26-case mutual induction over `parseValue.induct` that defeated
the first attempt, the parser's **return type now carries the canonicity proof**:

```lean
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }

def parseValue (depth : Nat) (s : List UInt8) :
    Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s
```

This is the same device that already gave the parser fuel-free totality. The obligation is
discharged at the ~8 construction sites inside `parseValue`/`parseElems`/`parseMembers`, and
`parseDoc_canonical` / `parseDoc_depth` are then projections. Both properties are `Prop`s and
are erased at runtime; the emitted bytes were re-verified unchanged (JSONTestSuite 297/318 and
fuzz 116,476/120,000 agreement reproduced *exactly*, before and after).

Closing GAP-1 made **T3** unconditional:
`parseDoc s = some v → parseDoc (serialize v) = some v`.

**Method note worth recording:** the induction principle Lean generates for a WF-recursive
mutual parser (`parseValue.induct`, 26 minor premises, each carrying dependent-subtype
hypotheses) is *substantially harder to use* than strengthening the function's return type.
The second route took roughly an hour; the first was abandoned. If you are formalizing a
recursive descent parser, put the invariant in the type.

---

## GAP-2 — Soundness against the SPEC grammar — **OPEN, and the important one**

**Not proved:**
```lean
-- neither this predicate nor this theorem exists in the artifact
inductive Grammar : Bytes → Prop := ...        -- mirroring SPEC §S2
theorem parseDoc_sound : parseDoc s = some v → Grammar s
```

**There is no theorem in this artifact about which inputs the parser accepts.**

### Why this is the important gap

SPEC.md is *overwhelmingly* a document about the accept-set and the value-map:

* whitespace is any byte ≤ 32 (§S1.1);
* trailing bytes after a complete value are accepted (§S5.1);
* the number scanner is `strtod`'s longest-valid prefix over `[0-9+-eE.]` (§S3.1);
* a value may only begin a number with `-` or a digit (§S2);
* `\uXXXX` requires four hex digits (§S4.3);
* the nesting limit is 1000 (§S2);
* duplicate keys are preserved in source order (§S2).

**Not one of those is proved.** All of them are MEASURED.

T1 and T3 run in the *other* direction: they say that what the serializer emits is accepted.
That is a completeness statement restricted to the image of `serialize`, and it says nothing
about the inputs the serializer never produces — which is all the interesting ones. A parser
that accepted *every* byte string and returned `null` would satisfy T1 and T3 exactly as
well as this one does.

### What stands in its place

Differential agreement with the oracle on accept/reject: 317/318 (JSONTestSuite) and
119,999/120,000 (fuzz). That is good evidence and it is not proof, and it has a **blind spot
by construction**: where the Lean port and cJSON are wrong *in the same way*, a differential
test cannot see it. Both accept trailing garbage. Both treat NUL as whitespace. Both skip
UTF-8 validation. Only the manual RFC comparison in SPEC §S1–S5 catches those, and that is a
human reading.

### What it would take to close

State `Grammar` as an inductive predicate over `Bytes` mirroring SPEC §S2, then prove
soundness (`parse s = some v → Grammar s`) and completeness (`Grammar s → ∃ v, parse s = some v`).
This is a substantial piece of work — comparable to everything else in this artifact
combined — largely because the grammar has to encode `strtod`'s longest-valid-prefix rule and
the trailing-garbage allowance, both of which are awkward to state declaratively.

**Estimated: the single highest-value next step, and the reason this artifact should not be
described as "a verified JSON parser" without qualification.**

---

## GAP-EXTRACT — the compiled binary is not the verified artifact — **OPEN**

The theorems are about Lean functions. The binary in `lean/.lake/build/bin/cjson` is produced
by Lean's compiler and linked against its runtime. **Neither is verified here.**

Everything in `DIVERGENCES.md` and every MEASURED number is a statement about *the binary*.
Everything in `CLAIMS.md §1` is a statement about *the Lean functions*. The bridge between
them is:

* the 20,318-input idempotence run (0 violations), which cross-checks that the binary behaves
  as T3 says the function does;
* nothing else.

This is a real and standard gap for Lean/Coq extraction. It is stated, not hidden.

---

## GAP-3 — no exponent bound — **OPEN, by deliberate choice**

The exact-number model will faithfully emit an exponent of any magnitude:

```
in   : 1e400030000000000000004
lean : 1e400030000000000000004      <- syntactically valid RFC 8259
```

RFC 8259's number grammar has unbounded exponent digits, so this is *legal JSON*. But:

* Python's `json.loads` returns `inf` (silently lossy);
* Python's `Decimal` **raises `InvalidOperation`**;
* most consumers will not round-trip it.

**This is the one finding against my own port**, not against cJSON (which collapses it to
`null` — its own bug, D-NUM-1). It is a real interop cost of exactness.

I did not add a limit because inventing one that neither RFC 8259 nor cJSON has would be a
silent third semantics — and SPEC.md would then be describing a language that no reference
implementation speaks. A production port should add a bound **and say so in its spec**.

Ironically, this is also how I found a bug in my own fuzz classifier: `Decimal` raising made
the classifier report the case as `UNKNOWN-unparseable` when both binaries had behaved exactly
as specified.

---

## GAP-4 — the oracle's entry point is a choice — **OPEN, scoped out**

The wrapper uses `cJSON_ParseWithLength(buf, len + 1)` over a NUL-appended copy. This is
byte-for-byte the buffer `cJSON_Parse()` constructs for any NUL-free input
(`cJSON_ParseWithOpts` sets `buffer_length = strlen(value) + 1`).

**Every measurement in this artifact is relative to that choice.**
`cJSON_ParseWithLength(buf, len)` — without the appended byte — has a *different and buggier*
BOM behaviour (an off-by-one in `skip_utf8_bom` becomes reachable). See SPEC §S7. Not in
scope, not tested, not claimed.

---

## Coverage limit — the fuzz corpus barely explores depth

The corpus is seeded from JSONTestSuite's `y_` files, whose maximum nesting is shallow, and
mutated byte-wise. **It essentially never produces deeply-nested documents.** The depth-limit
boundary is covered by exactly three hand-written probes (999 / 1000 / 1001 levels, all
matching the oracle).

Since v1.0, `parseDoc_depth` **proves** that any value the Lean parser produces has
`jdepth ≤ 1000`, which removes the Lean side of this exposure. What remains untested is the C
oracle's behaviour in that regime, and therefore the *agreement* claim at depth.

---

## Things a reviewer might expect that are deliberately out of scope

* **`cJSON_Utils`, pretty-printing, the cJSON C API surface, in-place mutation.** SPEC §Scope.
  Never claimed.
* **Performance.** Not measured, not claimed, not optimised. The Lean parser works over
  `List UInt8` and will be slow. That was a proof-ergonomics choice, and it is a real cost.
* **Memory safety of the oracle.** We did not run the C under ASan/valgrind. We are not
  claiming cJSON has no memory bugs; we are claiming it has the four *semantic* bugs in
  `DIVERGENCES.md`.
* **IEEE-754 semantics.** The Lean port models numbers exactly and proves nothing about
  `Float`. Converting to `Float` is a separate, explicitly lossy projection we prove nothing
  about (LEDGER §2, `NUM-EXACT`).
