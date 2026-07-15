# C4_ARCHITECTURE.md — completeness proof design (branch `gap2-adequacy-proof`)

**Design-only run.** No C4 proof code was written. v1.0.1 untouched; grammar and parser untouched.
Empirical probes below are cited as *confidence*, never as proof.

---

## 1. Exact C4 statement

From `lean/Cjson/Spec/Grammar.lean:243–246`, C4 is stated (as an elaborating `example : Prop`,
not asserted):

```lean
∀ p v rest, SValue p v → DepthOk v →
  (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
  ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩
```

The inline tail condition is **definitionally `SafeTail rest`** (`Cjson/Proofs/Num.lean:133–135`):

```lean
def SafeTail (t : Bytes) : Prop :=
  ∀ c t', t = c :: t' → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69
```

`DepthOk v := jdepth v ≤ nestingLimit` (`= 1000`). So C4 reads: *every grammatical value `v`
with spelling `p`, within the depth limit, is parsed by `parseValue 0` from `p ++ rest` — it
selects the right branch, consumes exactly `p`, returns `v`, and leaves `rest` — provided `rest`
cannot lexically continue a number token.*

### Grammar definitions the proof is against (`Grammar.lean:170–198`)

```lean
mutual
  inductive SValue : Bytes → JSON → Prop where
    | null | true_ | false_                                  -- fixed 4/5-byte literals
    | str  : SStr p out → SValue p (.str out)
    | num  : (c = 45 ∨ isDigitB c = true) → SNumTok (c :: p) n → SValue (c :: p) (.num n)
    | arr0 : Ws w → SValue (91 :: (w ++ [93])) (.arr [])
    | arr  : Ws w → SElems p xs → SValue (91 :: (w ++ p)) (.arr xs)
    | obj0 : Ws w → SValue (123 :: (w ++ [125])) (.obj [])
    | obj  : Ws w → SMembers p kvs → SValue (123 :: (w ++ p)) (.obj kvs)
  inductive SElems : Bytes → List JSON → Prop where
    | last : SValue p v → Ws w → SElems (p ++ w ++ [93]) [v]
    | cons : SValue p v → Ws w1 → Ws w2 → SElems q vs → SElems (p ++ w1 ++ [44] ++ w2 ++ q) (v::vs)
  inductive SMembers : Bytes → List (Bytes × JSON) → Prop where
    | last : SStr k out → Ws w1 → Ws w2 → SValue p v → Ws w3 →
             SMembers (k ++ w1 ++ [58] ++ w2 ++ p ++ w3 ++ [125]) [(out, v)]
    | cons : SStr k out → Ws w1 → Ws w2 → SValue p v → Ws w3 → Ws w4 → SMembers q kvs →
             SMembers (k ++ w1 ++ [58] ++ w2 ++ p ++ w3 ++ [44] ++ w4 ++ q) ((out,v)::kvs)
end
```

`Ws w := ∀ c ∈ w, c.toNat ≤ 32`. `SStr`, `SChars`, `SNumTok` per `Grammar.lean`.

---

## 2. Truth / ill-posedness assessment

**C4 is TRUE and well-posed, as stated. No premise is missing; nothing must be weakened.**
Each sub-claim, with the reasoning and a confidence probe:

**(a) `SafeTail` is exactly strong enough to stop number extension — verified structurally.**
`scanNumber` after a complete token can only continue on a digit, a `.` (if no dot yet), or
`e`/`E` (if no exponent yet); a mid-token `+`/`-` is consumed *only* immediately after `e`/`E`.
`SafeTail` excludes exactly `{digit, '.', 'e', 'E'}` as the first byte of `rest`, so a `SafeTail`
tail can never extend the token. Confidence (parser binary; `parseDoc` discards `rest`, so the
printed value = the value of the consumed token):

| input | output | reading |
|---|---|---|
| `1-5` | `1` | `-` (45) is SafeTail; not consumed mid-token |
| `1+5` | `1` | `+` (43) is SafeTail |
| `1x`  | `1` | letter is SafeTail |
| `1.5.3` | `1.5` | 2nd `.` not part of the grammar; **`rest=".3"` is NOT SafeTail, so C4 makes no claim — and the parser still stopped** |
| `01` | `1` | non-canonical spelling → canonical `1` (see A10, §5) |

SafeTail is *stronger than strictly necessary* (it excludes some tails the parser handles, e.g.
`p="1.5", rest=".3"`), which only makes C4 a weaker (still true) statement. Recorded, not a bug.

**(b) Depth: `DepthOk` (≤1000) is EXACTLY the right bound — verified.** The parser increments
depth by one per array/object level and rejects at `depth ≥ 1000`; the value at grammar level `i`
(0-indexed) is parsed at parser depth `i`. So `jdepth v ≤ 1000` ⟺ `parseValue 0` accepts.
Confidence: `[`×1000 accepts (exit 0), `[`×1001 rejects (exit 1). C4 fixes root depth 0; the
proof must GENERALISE over depth with the invariant `d + jdepth v ≤ nestingLimit` (§8) — the
same form `roundtrip_value` uses and the same bound the parser carries in its result subtype.

**(c) The `∃ h` subtype form is discharged for free.** `h : rest.length < (p++rest).length ∧
JSON.Canonical v ∧ jdepth v ≤ nestingLimit − 0`. The proof plan proves the `pv`-view equality
`pv 0 (p ++ rest) = some (v, rest)` and extracts `h` from the fact that `parseValue` succeeded
(`pv d s = some (v,r) ⟺ ∃ h, parseValue d s = some ⟨(v,r),h⟩` by definition of `pv`). So the
subtype proof is *recovered from the parser having accepted*, never reconstructed.

**No `C4_COUNTEREXAMPLE.md` is warranted.** Every adversarial case probed either satisfies C4 or
is correctly excluded by `SafeTail`/`DepthOk`.

---

## 3. Dependency graph

```
                           ┌─ literal completeness (null/true/false)   [trivial, fixed patterns]
                           │
 scanNumber_complete ◄── SNumTok  ── uses A10 (canonical_unique) + SameNum      [HARD leaf]
                           │
 parseStrBody_complete ◄─ SChars  ── uses hex4_complete, enc/utf8Enc bridge      [HARD leaf]
                           │
 skipWs_consume  ◄── Ws            ── whitespace completeness (reverse of skipWs_split)
 safeTail_ws_delim ◄── Ws + {44,93,125}                                          [discharge SafeTail]
 jdepth monotonicity (jdepth e ≤ jdepthL xs, etc.)                               [max-facts]
                           │
                           ▼
    Vcomp / Ecomp / Mcomp  ── ONE mutual structural induction on SValue.rec  (depth threaded)
                           │
                           ▼
                         C4  (specialise d := 0, DepthOk gives the invariant, extract ∃h)
```

The three-motive mutual recursor `SValue.rec` **exists** (checked) and is the induction vehicle.

---

## 4. Required helper lemmas (inventory — none assumed to exist; status noted)

Signatures derived from the real code/grammar. "reverse of X" = the converse of a soundness lemma.

| lemma | statement (schematic) | status | note |
|---|---|---|---|
| **`scanNumber_complete`** | `SNumTok p n → SafeTail rest → scanNumber (p ++ rest) = some (n, rest)` | **new, HARD** | reverse of `scanNumber_sound`; the crux leaf. Sub-lemmas: `scanSign`/`scanDigits`/`scanFrac`/`scanExp` each consume exactly their grammatical piece; final value = `n` via `SameNum` + **A10**. |
| **`parseStrBody_complete`** | `SChars body out → parseStrBody (body ++ 34 :: rest) = some (out, rest)` | **new, HARD** | reverse of `parseStrBody_sound`; structural induction on `SChars`. |
| `hex4_complete` | `IsHex a→IsHex b→IsHex c→IsHex d → hex4 a b c d = some (hex4v a b c d)` | new, easy | reverse of `hex4_isHex` |
| `skipWs_consume` | `Ws w → (NonWsHead t) → skipWs (w ++ t) = t` | new, easy | reverse of `skipWs_split` |
| `safeTail_ws_delim` | `Ws w → (c=44 ∨ c=93 ∨ c=125) → SafeTail (w ++ c :: t)` | new, easy | discharges the `SafeTail` obligation for every interior value (ws-bytes ≤32 and 44/93/125 are all SafeTail) |
| literal completeness | `pv d (110::117::108::108::rest) = some (.null, rest)` (×3) | ~have | analogues `pv_null/true/false` already exist in `RoundTrip.lean` |
| `pv_arr_empty`/`pv_obj_empty`/`pv_arr_cons`/`pv_obj_cons` | forward branch equations | **HAVE (v1.0.1)** | `RoundTrip.lean:220–276`; these are exactly the reverse-direction constructors, already proven |
| `pe_last`/`pe_cons`/`pm_last`/`pm_cons` | loop branch equations | **HAVE (v1.0.1)** | `RoundTrip.lean:290–420` — the element/member assembly lemmas, already proven |
| `SValue_ne_nil` | `SValue p v → p ≠ []` | **HAVE** (StructSound) | for the subtype length component |
| jdepth monotonicity | `jdepth e ≤ jdepthL (e::…)`, `jdepthL xs ≤ jdepthL (x::xs)`, … | new, trivial | `simp [jdepthL]; omega` (max facts); shape already used in `roundtrip_value` |
| A10 `canonical_unique` | (proved) | **HAVE** | closes `scanNumber_complete`'s value clause |

**Load-bearing observation (verified against `RoundTrip.lean:469–481`).** `roundtrip_value`'s
`motive_1` is *literally*
`∀ d rest, Canonical v → d + jdepth v ≤ nestingLimit → SafeTail rest → pv d (serialize v ++ rest) = some (v, rest)`
— **C4's exact shape**, with `serialize v` in place of an arbitrary grammatical `p`. It inducts on
`JSON.rec` (the value structure) and threads the depth bound in the `d + jdepth v ≤ nestingLimit`
form (which avoids Nat subtraction). **This design adopts that same `d + jdepth` bound**, and
recommends inducting on `SValue.rec` instead of `JSON.rec` (see §8) so that `p`'s byte layout comes
from the derivation directly rather than requiring a separate inversion of `SValue p v`. C4 is `roundtrip_value`
**generalised from the canonical rendering to an arbitrary grammatical `p`.** The structural
skeleton (arr/obj/elems/members assembly via `pv_arr_cons`, `pe_cons`, `pm_cons`, …) is therefore
**already built and proven**; the genuinely new work is the two leaf lemmas
`scanNumber_complete` and `parseStrBody_complete`, which replace `roundtrip_value`'s reliance on
`scanNumber_renderNum` (T1a) and `parseStrBody_renderStr` (T1b) — those handle only the canonical
spelling, whereas the grammar admits many (e.g. `01`, `1.0`, `\/`, `A`).

---

## 5. A10 sufficiency for value uniqueness

**Yes.** In `SValue.num`, `SNumTok (c::p) n` carries `JNum.Canonical n` and a `SameNum`
equivalence between the token's raw digits and `n`. `scanNumber` returns `normNum(...)`, which is
`JNum.Canonical` (`normNum_canonical`, v1.0.1) and `SameNum`-equivalent to the token
(`normNum_denote`, proved). Two canonical `JNum`s that are `SameNum`-equivalent are **equal** by
**A10 (`canonical_unique`)**. So the parser's number equals the grammar's `n`. A10 is *exactly*
what makes `scanNumber_complete`'s value clause go through; without it the theorem would be
ill-posed (multiple `JNum` for one value). Confidence: `01 → 1`, non-canonical spelling collapses
to the canonical node.

---

## 6. Completeness asymmetry — reverse-direction obligations NOT needed for soundness

Soundness followed an accepting execution and *read off* grammar evidence. Completeness must
*force* the parser. New obligations, by location:

| forced property | where it bites | new lemma |
|---|---|---|
| **branch selection** | the parser's first-byte `match` must pick the arm the `SValue` constructor dictates | **first-byte disjointness** (below) |
| **exact consumption** | sub-parsers must consume *exactly* the grammatical piece, not less/more | `scanNumber_complete`, `parseStrBody_complete`, `skipWs_consume` |
| **remainder preservation** | `= some (v, rest)` — the tail must survive untouched | baked into the `++` layout; needs `SafeTail` at number leaves |
| **value equality** | parser's returned value must equal the grammar's | A10 (numbers); IH (structure) |
| **depth admission** | every container node must pass `depth < 1000` | depth invariant `d + jdepth v ≤ nestingLimit` |

**First-byte disjointness** is the sharpest new need. Each `SValue` constructor fixes the first
byte: `null`→110, `true_`→116, `false_`→102, `str`→34, `num`→(45 or a digit 48–57), `arr*`→91,
`obj*`→123. These are pairwise distinct, so the parser's `match` on the head selects the arm
matching the derivation. In practice this is discharged *implicitly*: once the grammar constructor
fixes `p`'s head, `rw [parseValue]`/`split` reduces to the matching arm and the other arms are
`absurd`. It surfaces as a proof obligation only in the `num` catch-all (must show the head is not
110/116/102/34/91/123 — true since it is 45 or a digit). Soundness never needed this (the parser
had already chosen).

---

## 7. Candidate induction architectures

| # | architecture | verdict |
|---|---|---|
| **1** | **mutual structural induction on `SValue.rec` (3 motives), depth threaded as a hypothesis** | **RECOMMENDED.** The grammar derivation is well-founded by construction; every sub-motive application is on a strict sub-derivation. No same-length hazard (unlike soundness). Directly available (recursor checked). |
| 2 | strong induction on derivation *size* | Works but strictly more manual than #1 — reconstructs by hand what `SValue.rec` gives for free. Unnecessary. |
| 3 | grammar induction + depth invariant | This *is* #1 with the depth bound carried as a hypothesis. Adopted as part of #1. |
| 4 | staged mutual proof (à la structural soundness) | The staging in soundness existed *only* because the PARSER's `parseElems→parseValue` call was same-length. Completeness inducts on the GRAMMAR, which has no such call; staging is unnecessary. |
| 5 | lexicographic measure (derivation size, input length, depth) | Only needed if plain derivation induction cannot express the recursion. It can. Unnecessary. |

**Why #1 succeeds where soundness needed staging:** soundness' measure was the *parser input
length*, and `parseElems d s` recursively calls `parseValue d s` at the **same** length, breaking
a naive length induction. Completeness' measure is the *grammar derivation*, and `SElems.cons`
contains strictly smaller `SValue`/`SElems` sub-derivations. The direction of the arrow moves the
well-foundedness from the parser (awkward) to the grammar (clean).

---

## 8. Recommended architecture

**One mutual induction via `SValue.rec`** with three motives (depth `d` and `rest` universally
quantified inside each motive):

```lean
-- depth in the `d + jdepth ≤ nestingLimit` form (matches roundtrip_value; avoids Nat subtraction)
motive_V p v   _ := ∀ d rest, d + jdepth v   ≤ nestingLimit → SafeTail rest →
                      pv d (p ++ rest) = some (v, rest)
motive_E p xs  _ := ∀ d rest, d + jdepthL xs ≤ nestingLimit →
                      pe d (p ++ rest) = some (xs, rest)          -- no SafeTail: ']' terminates p
motive_M p kvs _ := ∀ d rest, d + jdepthKV kvs ≤ nestingLimit →
                      pm d (p ++ rest) = some (kvs, rest)          -- no SafeTail: '}' terminates p
```

Inducting on `SValue.rec` (not `JSON.rec`) means the three motives are indexed by the derivation,
so each constructor *hands us* `p`'s layout (`91 :: (w ++ p)`, `p ++ w1 ++ [44] ++ …`, …) with no
separate inversion step. `xs ≠ []`/`kvs ≠ []` (which `roundtrip_value` states explicitly) are here
*automatic* — `SElems`/`SMembers` have no empty constructor. Note `motive_E`/`motive_M` take `p`
already including the closing `]`/`}` (the grammar puts it there), whereas `roundtrip_value` writes
`serializeL xs ++ (93 :: rest)` with the bracket split out; the two are the same layout.

* `SafeTail` is a hypothesis of `motive_V` only. In `motive_E`/`motive_M` the closing `]`/`}` is a
  hard terminator, so no tail condition is needed; when they invoke `motive_V` on an interior
  value they DISCHARGE its `SafeTail` via `safeTail_ws_delim` (the value is always followed by
  `Ws ++ (,|]|})`).
* The number and string LEAVES are the two separately-proved lemmas `scanNumber_complete` /
  `parseStrBody_complete`, invoked in the `num` and `str`/member-key cases.
* C4 (root) := instantiate `motive_V` at `d = 0`; `DepthOk v` gives `jdepth v ≤ nestingLimit − 0`;
  extract `∃ h` from `pv`.

Phrase everything on the `pv`/`pe`/`pm` views (as structural soundness did) to avoid the
dependent-subtype elaborator pain. **No parser or grammar change; nothing carries a witness.**

---

## 9. `SafeTail` audit (done with care, as instructed)

* **What it excludes:** a `rest` whose first byte is a digit (`isDigitB`), `.` (46), `e` (101) or
  `E` (69). Empty `rest` and any other first byte are *permitted*.
* **Sufficient to stop over-consumption?** **Yes.** After a complete number token, the only bytes
  `scanNumber` could append are a digit, a first `.`, or a first `e`/`E` — all excluded. A
  mid-token `+`/`-` is consumed only right after `e`/`E`, which cannot be the situation at the
  token boundary. So `SafeTail rest` ⇒ the parser consumes exactly `p`. (For strings/arrays/
  objects/literals the terminator is structural — `"`, `]`, `}`, or a fixed-length literal — so
  `SafeTail` is *unused* there; it is a uniform but harmless hypothesis.)
* **Only lexical separation?** **Yes.** It is a predicate on the first byte of `rest` and the
  fixed byte-classes `isDigitB`/`46`/`101`/`69`. It mentions **no parser state, no `parseValue`,
  no maximal-munch quantifier.** Contrast C3, which explicitly quantifies "no longer grammatical
  prefix" — `SafeTail` does not.
* **Smuggles parser behaviour?** **No.** `SafeTail` is defined in terms of byte classes only. It
  does not reference the parser; it is the same predicate used by T1a's `scanNumber_renderNum`,
  and it is *implied by* (weaker than) "a delimiter follows", so it does not encode munch.
* **Independent of the parser?** **Yes** (byte-class predicate).
* **Still meaningful for trailing garbage?** **Yes, and this is the point.** `SafeTail` *permits*
  arbitrary trailing garbage as long as the first byte is not a number-continuation — e.g.
  `rest = "xyz…"`, `"]"`, `",…"`, `" …"` all satisfy it. So C4 is a genuine statement about the
  §S5.1 trailing-garbage regime, not a disguised "whole-string" theorem.

**Verdict: `SafeTail` is correctly calibrated — not too strong (it permits trailing garbage), not
too weak (it stops number extension), not circular (byte-class only). No issue to record; proceed.**

One honest limitation to carry into the ledger: `SafeTail` is *slightly* conservative — it
excludes a few tails the parser actually handles (e.g. `p="1.5", rest=".3"`). This makes C4 weaker
than the tightest possible completeness statement, but it is the same condition C2's partner needs
and matches T1a. Tightening it is a C3-flavoured question and is out of scope.

---

## 10. Independence analysis

The contract (Parser → Grammar → Theorem) is preserved by construction:

* **No new parser, no new grammar, no witness carried.** As in structural soundness, the proof is
  phrased on the released `pv`/`pe`/`pm` views; conclusions are the grammar relations `SValue`/
  `SElems`/`SMembers`, unchanged.
* **The implication is substantive, not `rfl`.** Completeness *forces* the parser from a grammar
  derivation: it must derive branch selection (first-byte disjointness), exact consumption
  (`scanNumber_complete`, `parseStrBody_complete`, `skipWs_consume`), and value equality (A10). A
  defective parser — e.g. one that accepted `[1 2]` (no comma) or rejected `01` — would FALSIFY
  the corresponding case. The theorem is false of any parser that does not implement the grammar.
* **Not manufactured from C2.** C4 is the *converse* of C2; C2 (`parseDoc_sound`) is not used.
* **The `num` value clause uses A10**, which is independent (a fact about canonical `JNum`s).
* **Risk to watch:** `scanNumber_complete`. The tempting shortcut is to prove it only for the
  canonical rendering (reusing T1a) and quietly restrict the grammar's number spellings to match —
  that would weaken independence (the grammar's `SNumTok` deliberately admits `01`, `1.0`, `1e0`,
  …). The plan proves `scanNumber_complete` for **arbitrary** `SNumTok`, preserving the grammar's
  byte-freedom. If this proves intractable it must be recorded in `INDEPENDENCE_RISK.md`, not
  worked around by narrowing `SNumTok`.

**No independence risk is incurred by the recommended architecture.** (Recorded prospectively; a
concrete `INDEPENDENCE_RISK.md` entry is only needed if the `scanNumber_complete` shortcut is ever
reached for.)

---

## 11. Expected proof size and major risks

| component | est. lines | risk |
|---|---|---|
| `scanNumber_complete` (+ scanner sub-lemmas) | 300–450 | **HIGH** — the crux; reverse scanners + A10 value clause |
| `parseStrBody_complete` (+ `hex4_complete`) | 200–300 | MEDIUM — structural induction on `SChars` |
| structural mutual induction (V/E/M) | 350–500 | MEDIUM — `++`-accounting, but the branch-assembly lemmas (`pv_arr_cons`, `pe_cons`, `pm_cons`, …) are **already proven in v1.0.1** |
| whitespace / SafeTail-discharge / jdepth helpers | 100–150 | LOW |
| C4 root + `∃h` extraction | ~30 | LOW |
| **total** | **~1000–1400** | comparable to structural soundness |

**Top risk:** `scanNumber_complete` must show the scanners consume *exactly* the grammatical
pieces of an arbitrary `SNumTok` (not just the canonical rendering T1a handled) and that the
result equals the grammar's canonical `n`. If the "exact consumption" step (each of
`scanSign`/`scanDigits`/`scanFrac`/`scanExp` consuming precisely `sgn`/`ip`/`dot++fp`/`ep`) proves
harder than expected, the fallback is *not* to narrow the grammar (independence) but to record a
`BLOCKER.md` entry and prove the structural mutual induction first (it does not depend on the
number leaf beyond the lemma's statement).

---

## Proposed thin vertical slice (first, before the full proof — NOT done this run)

Prove **`null`** completeness first (no dependencies): from `SValue.null` (so `p =
[110,117,108,108]`, `v = .null`), any `d`, `SafeTail rest`, show
`pv d ([110,117,108,108] ++ rest) = some (.null, rest)`. Validates: branch selection (head 110),
exact remainder (`rest` untouched), the `SafeTail`-is-unused-for-literals fact, and the `pv` phrasing.

Then **empty array** (`SValue.arr0`, `p = 91 :: (w ++ [93])`): validates the whitespace lemma
`skipWs_consume` (the `Ws w` block before `]`), the depth check (`d < 1000` from `d + jdepth (.arr []) = d + 1 ≤ nestingLimit`), and the `91 :: (w ++ [93]) ++ rest` accounting.

These two exercise every mechanism except the two hard leaves and the recursive assembly; they are
the right smoke test before committing to `scanNumber_complete`.
