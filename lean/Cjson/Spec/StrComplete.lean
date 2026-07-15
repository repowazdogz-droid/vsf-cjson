/-
  GAP-2, C4 leaf 2 — parseStrBody_complete: SChars body v → parseStrBody (body ++ 34 :: rest) = some (v, rest).

  Independence: the grammar SChars is NOT narrowed to canonical (serialize) spellings. Every
  grammatical spelling goes through — `\/` and unescaped `/`, arbitrary hex letter case in
  `\uXXXX`, valid surrogate pairs, raw bytes ≥ 0x80 (SPEC §S1.3, no UTF-8 validation) — and
  the parser is FORCED into the branch the grammar dictates, returning the grammar-decoded `v`.

  Direct induction on `SChars.rec` (proof-search order step 1). Reuses the released reverse
  branch equations (`psb_esc34…psb_esc116`, `parseStrBody_other`) and the StrSound bridges
  (`enc_eq`); adds the reverse hex/surrogate helpers below.

  Zero sorry, zero custom axioms.
-/
import Cjson.Spec.StrSound

namespace Cjson.Spec

open Cjson

/-! ## Reverse hex / surrogate helpers (converses of the StrSound bridges) -/

theorem hex4_complete {a b c d : UInt8} (ha : IsHex a) (hb : IsHex b) (hc : IsHex c) (hd : IsHex d) :
    hex4 a b c d = some (hex4v a b c d) := by
  unfold IsHex at ha hb hc hd
  obtain ⟨va, hva⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨vb, hvb⟩ := Option.isSome_iff_exists.mp hb
  obtain ⟨vc, hvc⟩ := Option.isSome_iff_exists.mp hc
  obtain ⟨vd, hvd⟩ := Option.isSome_iff_exists.mp hd
  unfold hex4 hex4v
  rw [hva, hvb, hvc, hvd]; simp only [bind, Option.bind, Option.getD_some]

theorem isHigh_true {cp : Nat} (h : 0xD800 ≤ cp ∧ cp ≤ 0xDBFF) : isHighSur cp = true := by
  unfold isHighSur; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
theorem isLow_true {cp : Nat} (h : 0xDC00 ≤ cp ∧ cp ≤ 0xDFFF) : isLowSur cp = true := by
  unfold isLowSur; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega
theorem isLow_false_of_high {cp : Nat} (h : 0xD800 ≤ cp ∧ cp ≤ 0xDBFF) : isLowSur cp = false := by
  unfold isLowSur; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]; omega
theorem isLow_false_of_not {cp : Nat} (h : ¬ (0xD800 ≤ cp ∧ cp ≤ 0xDFFF)) : isLowSur cp = false := by
  unfold isLowSur; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]; omega
theorem isHigh_false_of_not {cp : Nat} (h : ¬ (0xD800 ≤ cp ∧ cp ≤ 0xDFFF)) : isHighSur cp = false := by
  unfold isHighSur; simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le]; omega

/-! ## The string-body completeness theorem -/

/-- **parseStrBody_complete.** For every grammatical string body `body` decoding to `v` (an
    *arbitrary* `SChars` spelling — `\/`, unescaped `/`, mixed-case `\uXXXX`, surrogate pairs,
    raw bytes ≥ 0x80 — NOT restricted to the canonical rendering), the parser consumes exactly
    `body` up to the closing quote and returns `v`, leaving `rest`. -/
theorem parseStrBody_complete : ∀ {body v : Bytes}, SChars body v →
    ∀ {rest : Bytes}, parseStrBody (body ++ (34 :: rest)) = some (v, rest) := by
  intro body v h
  induction h with
  | nil => intro rest; rfl
  | plain hpb _ ih =>
    intro rest
    obtain ⟨h34, h92⟩ := hpb
    rw [List.cons_append, parseStrBody_other h34 h92, ih]
  | @esc c d p out _ hcd ih =>
    intro rest
    have ihr : parseStrBody (p ++ 34 :: rest) = some (out, rest) := ih
    -- select the escape branch by the concrete escape byte
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
               | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show parseStrBody (92 :: 34  :: (p ++ 34 :: rest)) = _; rw [psb_esc34,  ihr]
    · show parseStrBody (92 :: 92  :: (p ++ 34 :: rest)) = _; rw [psb_esc92,  ihr]
    · show parseStrBody (92 :: 47  :: (p ++ 34 :: rest)) = _; rw [psb_esc47,  ihr]
    · show parseStrBody (92 :: 98  :: (p ++ 34 :: rest)) = _; rw [psb_esc98,  ihr]
    · show parseStrBody (92 :: 102 :: (p ++ 34 :: rest)) = _; rw [psb_esc102, ihr]
    · show parseStrBody (92 :: 110 :: (p ++ 34 :: rest)) = _; rw [psb_esc110, ihr]
    · show parseStrBody (92 :: 114 :: (p ++ 34 :: rest)) = _; rw [psb_esc114, ihr]
    · show parseStrBody (92 :: 116 :: (p ++ 34 :: rest)) = _; rw [psb_esc116, ihr]
  | @uni h1 h2 h3 h4 p out a1 a2 a3 a4 hns _ ih =>
    intro rest
    have ihr : parseStrBody (p ++ 34 :: rest) = some (out, rest) := ih
    show parseStrBody (92 :: 117 :: h1 :: h2 :: h3 :: h4 :: (p ++ 34 :: rest)) = _
    rw [parseStrBody, hex4_complete a1 a2 a3 a4]
    simp only []
    rw [if_neg (by rw [isLow_false_of_not hns]; simp),
        if_neg (by rw [isHigh_false_of_not hns]; simp), ihr, enc_eq]
  | @pair h1 h2 h3 h4 g1 g2 g3 g4 p out a1 a2 a3 a4 b1 b2 b3 b4 hh hl _ ih =>
    intro rest
    have ihr : parseStrBody (p ++ 34 :: rest) = some (out, rest) := ih
    show parseStrBody (92 :: 117 :: h1 :: h2 :: h3 :: h4 ::
          92 :: 117 :: g1 :: g2 :: g3 :: g4 :: (p ++ 34 :: rest)) = _
    rw [parseStrBody, hex4_complete a1 a2 a3 a4]
    simp only []
    rw [if_neg (by rw [isLow_false_of_high hh]; simp), if_pos (isHigh_true hh),
        hex4_complete b1 b2 b3 b4]
    simp only []
    rw [if_pos (isLow_true hl), ihr, enc_eq]

end Cjson.Spec
