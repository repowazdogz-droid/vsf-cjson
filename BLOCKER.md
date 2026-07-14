# BLOCKER.md — string-body soundness

Branch: `gap2-adequacy-proof`. Raised per the failure policy. Not worked around.

## Exact goal

```lean
theorem parseStrBody_sound : ∀ {s : Bytes} {v r : Bytes},
    parseStrBody s = some (v, r) → ∃ p, s = p ++ (34 :: r) ∧ SChars p v
```

Everything it needs is already proved and compiles (`lean/Cjson/Spec/StrSound.lean`):

* `enc_eq : enc cp = utf8Enc cp` — the grammar's encoder and the parser's are the same function.
* `hex4_isHex : hex4 a b c d = some cp → IsHex a ∧ IsHex b ∧ IsHex c ∧ IsHex d ∧ cp = hex4v a b c d`
* `not_surrogate`, `isHigh_range`, `isLow_range` — connect the parser's `isLowSur`/`isHighSur`
  booleans to the grammar's numeric surrogate ranges.

So the *mathematical content* is discharged. What is left is case plumbing.

## The obstacle

`parseStrBody` is defined by 13 overlapping byte patterns (closing quote; seven single-character
escapes; `\uXXXX`; the surrogate-pair sub-case; two error patterns; the catch-all). Lean's
generated functional-induction principle therefore has **31 minor premises**:

```
Expected `case1`, `case2`, … , `case31`
```

Each carries the dependent hypotheses of its branch, and the `\u` cases nest a `match` on
`hex4` inside a `match` on the following six bytes. Discharging them means ~31 hand-written
blocks with the "motive is not type correct" plumbing already documented in `REPORT.md` §4.4.

This is **the same trap as `parseValue.induct` (26 premises)**, which defeated the first attempt
at GAP-1 and was abandoned. It is mechanical, not deep. It is also large.

## Approaches attempted, and why each failed

1. **`induction … using parseStrBody.induct` with a combinator sweep**
   (`all_goals first | (rename_i …; split at h; …) | skip`).
   Failed: the seven escape branches have *different* binder counts and orders, so a single
   `rename_i` pattern does not fit them all; and `tauto` (which would have discharged the
   eight-way escape disjunct in `SChars.esc`) is **Mathlib**, which the hard rules forbid.

2. **Explicit `case1 … case31` blocks.**
   Not attempted to completion: this is the honest fallback and it *will* work, but it is a
   large, purely mechanical grind, and stopping to report it is worth more than half-finishing
   it. Estimated 400–600 lines.

3. **Carrying the `SChars` witness in `parseStrBody`'s return type** — the device that solved
   fuel-free totality and closed GAP-1, and which would collapse 31 cases to ~13 construction
   sites.
   **REJECTED on independence grounds. See `INDEPENDENCE_RISK.md`.** It would make the *parser*
   depend on the *grammar*, inverting the arrow the whole GAP-2 argument rests on.

## Smallest remaining obstacle

An eight-way disjunction discharger for `SChars.esc`'s escape-character premise, plus 31
mechanical case blocks. No new mathematics. No new lemmas.

## Status

Not a defect in the theorem, the grammar, or the parser. A tooling/effort obstacle, recorded
rather than worked around. Number soundness (the piece the research phase identified as *the*
hard part) is **proved**; this one is *long*.
