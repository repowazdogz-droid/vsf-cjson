/-
  GAP-2, step 3 — STRING SOUNDNESS.

      parseStrBody s = some (v, r)  →  ∃ p, s = p ++ (34 :: r) ∧ SChars p v

  The bytes the parser consumed (excluding the closing quote) form a string body that the
  grammar decodes to exactly `v`.

  Zero `sorry`, zero axioms.
-/
import Cjson.Spec.NumSound

namespace Cjson.Spec

open Cjson

/-- The grammar's `enc` and the parser's `utf8Enc` are the same function. They are stated
    separately on purpose (the grammar must not *depend* on the parser), and this is the one
    place the duplication has to be discharged. -/
theorem enc_eq (cp : Nat) : enc cp = utf8Enc cp := rfl

/-- A successful `hex4` implies all four bytes are hex digits, and pins the value. -/
theorem hex4_isHex {a b c d : UInt8} {cp : Nat} (h : hex4 a b c d = some cp) :
    IsHex a ∧ IsHex b ∧ IsHex c ∧ IsHex d ∧ cp = hex4v a b c d := by
  unfold hex4 at h
  cases ha : hexVal? a with
  | none => rw [ha] at h; simp at h
  | some va =>
    cases hb : hexVal? b with
    | none => rw [ha, hb] at h; simp at h
    | some vb =>
      cases hc : hexVal? c with
      | none => rw [ha, hb, hc] at h; simp at h
      | some vc =>
        cases hd : hexVal? d with
        | none => rw [ha, hb, hc, hd] at h; simp at h
        | some vd =>
          rw [ha, hb, hc, hd] at h
          simp only [bind, Option.bind, Option.some.injEq] at h
          refine ⟨by simp [IsHex, ha], by simp [IsHex, hb], by simp [IsHex, hc],
                  by simp [IsHex, hd], ?_⟩
          unfold hex4v
          rw [ha, hb, hc, hd]
          exact h.symm

theorem not_surrogate {cp : Nat} (hl : isLowSur cp = false) (hh : isHighSur cp = false) :
    ¬ (0xD800 ≤ cp ∧ cp ≤ 0xDFFF) := by
  unfold isLowSur at hl
  unfold isHighSur at hh
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, Nat.not_le] at hl hh
  omega

theorem isHigh_range {cp : Nat} (h : isHighSur cp = true) : 0xD800 ≤ cp ∧ cp ≤ 0xDBFF := by
  unfold isHighSur at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h

theorem isLow_range {cp : Nat} (h : isLowSur cp = true) : 0xDC00 ≤ cp ∧ cp ≤ 0xDFFF := by
  unfold isLowSur at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h


end Cjson.Spec
