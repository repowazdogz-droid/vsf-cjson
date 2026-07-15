# BLOCKER.md — string-body soundness

## STATUS: **RESOLVED 2026-07-14.** `parseStrBody_sound` is proved.

The blocker below is retained verbatim as the historical record, followed by how it was cleared.

---

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


---

# RESOLUTION (2026-07-14)

## What was proved

```lean
theorem parseStrBody_sound : ∀ (n : Nat) (s : Bytes) (v r : Bytes), s.length ≤ n →
    parseStrBody s = some (v, r) → ∃ p, s = p ++ (34 :: r) ∧ SChars p v

theorem parseStrBody_sound' {s : Bytes} {v r : Bytes} (h : parseStrBody s = some (v, r)) :
    ∃ p, s = p ++ (34 :: r) ∧ SChars p v
```

`#print axioms` → `[propext, Quot.sound]`. **Not even `Classical.choice`.** Zero `sorry`.

## Which architecture worked

**Architecture 1** — a specialised induction, *not* `parseStrBody.induct`.

The 31-case functional-induction principle was abandoned. Instead: **strong induction on the
input length**, with the byte-pattern analysis done by hand (`cases s`, then `by_cases c = 34`,
`c = 92`, then on the escape byte). This turns 31 generated premises into a handful of *chosen*
ones, and — crucially — lets the eight simple escapes be collapsed into a **single** lemma
(`psb_esc`) rather than repeated eight times.

Architecture 2 (a proof-only `StrBodyRun` execution relation) was **not needed** and was not built.

## Obstacles actually hit, and their nature

| obstacle | nature |
|---|---|
| `exacts` and `tauto` unavailable | **Lean elaboration / no-Mathlib** — replaced with bullets and explicit disjunct construction. |
| `cases h : e` silently *reverts and substitutes* hypotheses that depend on `e`, so a following `rw [h] at …` fails with a confusing "pattern not found" | **Lean elaboration.** Fixed by using `split at h` (which yields the branch equation directly) instead of `cases … with` + `rw`. |
| `simp_all` **destroyed** the equation-compiler's unreachability hypotheses in the catch-all arm, making an *unreachable* case look like an open goal | **Lean elaboration, and the sharpest trap here.** The hypothesis `∀ x xs, c = 92 → r = x :: xs → False` was being rewritten into uselessness. Fixed by discharging that case *before* `simp_all`, applying the hypothesis by hand (`psb_bad_esc`). |
| the `match` arms in `parseStrBody`'s recursive calls are `some`-then-`none`, not `none`-then-`some` | **Representational** — bullet order. |

**None of the obstacles was logical.** The theorem was true; the fight was entirely with Lean's
elaborator and with `simp_all`'s willingness to discard hypotheses it did not understand.

## Next independent route (now the live blocker)

Structural soundness for values, arrays and objects — see `ADEQUACY_REPORT.md` §4. The induction
*order* is the new design constraint and is recorded there: `parseValue` calls `parseElems` on a
**strictly shorter** input, but `parseElems` calls `parseValue` on an input of the **same**
length, so a plain length induction does not close. The step must prove `pv` at length `n+1`
first (using the IH's `pe` at `≤ n`), then `pe`/`pm` at `n+1` using the `pv` just established.


---

# RESOLUTION 2 — structural soundness (2026-07-15)

The "next independent route" recorded above (structural soundness) is now **PROVED**, and so is
**C2**. The design constraint anticipated in the previous run was correct and was handled exactly
as sketched:

* Confirmed against the real code: the only same-length recursive call is `parseElems → parseValue`;
  every other recursive call is on a strictly shorter input.
* A single `Nat.rec` on a length bound, with a **staged successor step**:
  `hV_step` (value soundness at `n+1`, from the IH's elem/member soundness at `≤ n`),
  then `hE_step` (element soundness at `n+1`, using `hV_step` for the same-length value call),
  then `hM_step` (member soundness at `n+1`, using only the IH).
* The strict-decrease measure that the `pv`/`pe`/`pm` views discard was **recovered from the
  grammar** via `SValue_ne_nil` (every grammatical value consumes ≥ 1 byte) — not by reaching into
  the parser's result subtype.

New required whitespace/BOM facts, all proved: `skipWs_split`, `skipBom_split`, `isWs_IsWs`.
No parser change, no grammar change, no witness carried. `#print axioms` → standard axioms only.

**The live blocker is now C4 (completeness)** — deferred to the next phase per instruction.
