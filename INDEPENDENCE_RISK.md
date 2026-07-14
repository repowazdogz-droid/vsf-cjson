# INDEPENDENCE_RISK.md

Raised per the independence contract on branch `gap2-adequacy-proof`. **No change was made.**
This records a proof step that was *considered and rejected*, and why.

---

## The contract

```
Parser  →  Grammar  →  Theorem          (what we have)
```

The grammar must be derivable from SPEC.md **without looking at the parser**, so that
"the parser implements the grammar" is a real claim. The failure mode the contract forbids:

```
Parser  →  Grammar rewritten around the parser  →  Trivial theorem
```

The research phase measured our position: the grammar agrees with the **third-party C oracle**
on 8,847/8,849 inputs, the only gap being the one intentional divergence (D-STR-1). That
measurement is the asset. Any change that entangles the grammar with the parser spends it.

---

## Risk 1 — REJECTED: define the grammar's number semantics as `normNum`

**Proposed change.** `SNumTok`'s value clause currently says: the token's raw triple
`± m·10^e` is `SameNum`-equivalent to the canonical `JNum` the parser returned. The shortcut
would be to say instead: `n = normNum neg (ids ++ fds) (e - |fds|)`.

**Why it reduces independence.** `normNum` *is* the parser's normaliser. The grammar would then
assert "the parser's number is the parser's number", and `scanNumber_sound` would be `rfl` in
its interesting component. The theorem would still typecheck and would still say something —
but not the thing a reviewer is buying.

**Status: REJECTED, and the honest route was taken.** `SameNum` was kept as an equivalence on
raw triples, and `Cjson/Spec/NumSound.lean` **proves** `normNum_denote`:

```lean
theorem normNum_denote (neg) (ds) (e) :
    SameNum neg (natOf ds) e
            (normNum neg ds e).neg (natOf (normNum neg ds e).digits) (normNum neg ds e).exp
```

i.e. the parser's normaliser *lands in the grammar's equivalence class*. That is a real
obligation (it needs `natOf`'s behaviour under leading- and trailing-zero stripping, and the
`10^k` factorisation) and it is discharged. **The independence argument survives intact.**

---

## Risk 2 — REJECTED: carry the `SChars`/`SValue` witness in the parser's return type

**Proposed change.** Extend the parser's result subtype (the device that gave fuel-free totality
in v1.0.0 and closed GAP-1 in v1.0.1):

```lean
Res α P s := Option { p : α × Bytes // p.2.length < s.length ∧ P p.1 }
--                            ⋯ extend P with:  ∃ pre, s = pre ++ r ∧ SValue pre v
```

This would collapse `parseStrBody.induct`'s **31 minor premises** (and `parseValue.induct`'s 26)
to ~13 and ~8 construction sites respectively, and would very likely finish C2. It is the single
most effective technique in this project's history — used twice, successfully.

**Why it reduces independence — and why that matters more here than it did before.**

It inverts the arrow. `Cjson.Parser` would `import Cjson.Spec.Grammar` and its *type* would
mention `SValue`. Then:

1. **The parser can no longer be read without the grammar.** The grammar stops being an
   independent description of the language and becomes part of the parser's specification —
   which is fine engineering, but it is exactly the entanglement the contract exists to prevent.
2. **The theorem becomes true by construction.** `C2` would be a projection, as
   `parseDoc_canonical` is in v1.0.1. That was *fine* for canonicity (an internal invariant we
   authored). It is **not** fine for soundness against an externally-anchored grammar: a hostile
   reviewer would say, correctly, that we made the parser carry the answer.
3. **It changes the public parser.** v1.0.1's `Res` would gain a `Prop` conjunct. The bytes
   would not change — but the released artifact's definition would, and the reason would be
   "to make our proof easy", which the proof discipline explicitly names as the thing not to do.

The asymmetry is the point: in v1.0.1, the invariant carried in the type (canonicity) was
**our own**, so carrying it proved something real about the parser's outputs. Here the invariant
would be **the specification we are supposed to be checking the parser against**. Making the
parser carry it is assuming the conclusion.

**Status: REJECTED. No change made to `Cjson/Parser.lean` on this branch.**

## Alternatives, in preference order

1. **Grind out the 31 cases** of `parseStrBody.induct` (and later the 26 of
   `parseValue.induct`) by hand. Purely mechanical, ~400–600 and ~800–1200 lines. Preserves
   independence completely. **This is the recommended route** and is what `BLOCKER.md` records.
2. **Refactor `parseStrBody` into smaller mutually-recursive functions** (a `parseEscape` helper)
   so the generated induction principle has fewer, cleaner cases. This changes the parser but
   **not its type**, and not for the purpose of assuming the conclusion — it would have to be
   logged as a semantic-preserving refactor and re-verified byte-for-byte against the oracle,
   exactly as the `renderNum` refactors were in v1.0.0.
3. **Prove soundness via a separate, non-exported "witness-carrying" copy of the parser**, plus
   a lemma that it agrees with the real one. Honest, but it doubles the parser and moves the
   burden into the agreement lemma; probably not worth it.

Option 3 is the only one that would recover the return-type technique without inverting the
arrow, and it is not obviously cheaper than option 1.


---

## Risk 3 — string-body soundness: **NO RISK TAKEN** (architecture 1, no new definitions)

`parseStrBody_sound` was proved on **2026-07-14** using allowed architecture 1: a specialised
induction on the **input length**, plus branch equations about the **existing, released** parser
(`psb_esc34 … psb_esc116`, all `rfl`; `psb_esc`; `psb_bad_esc`; and `parseStrBody_other`, which
already existed in v1.0.1). Architecture 2 (a proof-only execution relation) was **not needed**.

### Independence test, answered as required

> **Does this definition merely describe an execution that already occurred?**
> There is **no new definition**. Nothing was introduced except theorems *about* the released
> `parseStrBody`. Every `psb_*` lemma is an equation the parser already satisfies definitionally.

> **Is acceptance/value meaning still supplied by the independent grammar?**
> Yes. The conclusion is `SChars p v` — the `SChars` relation in `Cjson/Spec/Grammar.lean`,
> written from SPEC.md, unchanged, and never mentioning the parser. The escape table, the
> four-valid-hex-digit requirement (D-STR-1), the surrogate-pairing rule and the
> raw-byte/no-UTF-8-validation policy are all supplied by the grammar, not by the parser.

> **Could a defective parser satisfy the relation while violating the grammar?**
> No — that is precisely what the theorem forbids, and it is not vacuous: a parser that accepted
> `"\uZZZZ"` (as **cJSON does**) could not satisfy it, because `SChars.uni` demands
> `IsHex h₁ … IsHex h₄`. The proof genuinely uses `hex4_isHex` to discharge that. The theorem
> would be **false of the C oracle**, which is the sharpest available evidence that it has content.

> **Is the final implication still substantive rather than `rfl` or a projection?**
> Substantive. The proof is ~200 lines and must construct a grammar derivation for every
> accepting execution: it converts the parser's boolean `isLowSur`/`isHighSur` tests into the
> grammar's *numeric* surrogate ranges (`isHigh_range`, `isLow_range`, `not_surrogate`), converts
> `hex4`'s `Option` into the grammar's `IsHex` + `hex4v` (`hex4_isHex`), and identifies the
> parser's `utf8Enc` with the grammar's independently-defined `enc` (`enc_eq`). None of these is
> `rfl` at the level that matters, and none of them was placed in the parser.

**Verdict: the parser → grammar → theorem separation is intact. No parser definition was
changed; no grammar definition was changed.** `Risk 2` (carrying the witness in the parser's
return type) remains **rejected and unused** — and is now also **unnecessary for strings**.
