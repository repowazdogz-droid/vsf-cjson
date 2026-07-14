/-
  Phase 4b, part 2: the string round-trip.

      parseStrBody (s.flatMap escapeByte ++ (34 :: rest)) = some (s, rest)

  Unlike numbers, strings need NO side condition on `rest`: the closing quote terminates
  the token unambiguously. That asymmetry is exactly why the number lemma needs
  `SafeTail` and this one does not.
-/
import Cjson.Proofs.Digits

namespace Cjson

/-! ## Hex digits -/

/-- Sixteen concrete cases. `decide` is fine here (it is kernel reduction, NOT
    `native_decide`, which is banned). -/
theorem hexVal?_hexDigitLower {d : Nat} (h : d < 16) : hexVal? (hexDigitLower d) = some d := by
  have : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9
       ∨ d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega
  rcases this with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- The `\u00xx` escape the printer emits for a control byte reads back as that byte. -/
theorem hex4_ctrl {n : Nat} (h : n < 32) :
    hex4 48 48 (hexDigitLower (n / 16)) (hexDigitLower (n % 16)) = some n := by
  have h0 : hexVal? (48 : UInt8) = some 0 := by decide
  have h1 : hexVal? (hexDigitLower (n / 16)) = some (n / 16) :=
    hexVal?_hexDigitLower (by omega)
  have h2 : hexVal? (hexDigitLower (n % 16)) = some (n % 16) :=
    hexVal?_hexDigitLower (by omega)
  unfold hex4
  simp only [h0, h1, h2, bind, Option.bind, Option.some.injEq]
  omega

/-! ## One byte at a time -/

theorem utf8Enc_lt128 {n : Nat} (h : n < 128) : utf8Enc n = [UInt8.ofNat n] := by
  unfold utf8Enc
  rw [if_pos (by omega)]

/-- The catch-all clause of `parseStrBody`: any byte that is neither the closing quote
    nor a backslash is copied through verbatim. -/
theorem parseStrBody_other {c : UInt8} {t : Bytes} (h34 : ¬ (c = 34)) (h92 : ¬ (c = 92)) :
    parseStrBody (c :: t)
      = match parseStrBody t with
        | some (v, r) => some (c :: v, r)
        | none => none := by
  rw [parseStrBody.eq_def]
  split <;> simp_all <;> rfl

/-- **Escape/unescape is the identity, one byte at a time.** -/
theorem parseStrBody_escapeByte (c : UInt8) (t : Bytes) :
    parseStrBody (escapeByte c ++ t)
      = match parseStrBody t with
        | some (v, r) => some (c :: v, r)
        | none => none := by
  unfold escapeByte
  by_cases h34 : (c == 34) = true
  · have hc : c = 34 := by simpa using h34
    subst hc; rw [if_pos h34]; rfl
  by_cases h92 : (c == 92) = true
  · have hc : c = 92 := by simpa using h92
    subst hc; rw [if_neg h34, if_pos h92]; rfl
  by_cases h8 : (c == 8) = true
  · have hc : c = 8 := by simpa using h8
    subst hc; rw [if_neg h34, if_neg h92, if_pos h8]; rfl
  by_cases h12 : (c == 12) = true
  · have hc : c = 12 := by simpa using h12
    subst hc; rw [if_neg h34, if_neg h92, if_neg h8, if_pos h12]; rfl
  by_cases h10 : (c == 10) = true
  · have hc : c = 10 := by simpa using h10
    subst hc; rw [if_neg h34, if_neg h92, if_neg h8, if_neg h12, if_pos h10]; rfl
  by_cases h13 : (c == 13) = true
  · have hc : c = 13 := by simpa using h13
    subst hc
    rw [if_neg h34, if_neg h92, if_neg h8, if_neg h12, if_neg h10, if_pos h13]; rfl
  by_cases h9 : (c == 9) = true
  · have hc : c = 9 := by simpa using h9
    subst hc
    rw [if_neg h34, if_neg h92, if_neg h8, if_neg h12, if_neg h10, if_neg h13, if_pos h9]; rfl
  rw [if_neg h34, if_neg h92, if_neg h8, if_neg h12, if_neg h10, if_neg h13, if_neg h9]
  have hc34 : ¬ (c = 34) := by simpa using h34
  have hc92 : ¬ (c = 92) := by simpa using h92
  by_cases hlt : c.toNat < 32
  · -- control byte: printed as \u00xx, read back through the surrogate-free path
    rw [if_pos hlt]
    have hhex : hex4 48 48 (hexDigitLower (c.toNat / 16)) (hexDigitLower (c.toNat % 16))
        = some c.toNat := hex4_ctrl hlt
    have hlow : isLowSur c.toNat = false := by unfold isLowSur; simp; omega
    have hhigh : isHighSur c.toNat = false := by unfold isHighSur; simp; omega
    show parseStrBody (92 :: 117 :: 48 :: 48 :: hexDigitLower (c.toNat / 16)
        :: hexDigitLower (c.toNat % 16) :: t) = _
    rw [parseStrBody]
    simp only [hhex, hlow, hhigh, Bool.false_eq_true, if_neg,
      utf8Enc_lt128 (by omega : c.toNat < 128), UInt8.ofNat_toNat, List.singleton_append]
    cases parseStrBody t with
    | none => rfl
    | some p => obtain ⟨v, r⟩ := p; rfl
  · -- ordinary byte (including every byte ≥ 0x80): copied verbatim, no UTF-8 validation
    rw [if_neg hlt]
    exact parseStrBody_other hc34 hc92

/-! ## The whole string -/

/-- **String round-trip.** No `SafeTail` hypothesis: the closing quote is a terminator. -/
-- @attested parseStrBody_renderStr
theorem parseStrBody_renderStr (s : Bytes) (rest : Bytes) :
    parseStrBody (s.flatMap escapeByte ++ (34 :: rest)) = some (s, rest) := by
  induction s with
  | nil => simp [parseStrBody]
  | cons c cs ih =>
    rw [List.flatMap_cons, List.append_assoc, parseStrBody_escapeByte c, ih]

end Cjson
