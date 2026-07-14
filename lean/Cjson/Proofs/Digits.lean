/-
  Nat-level lemmas underpinning the number round-trip.
-/
import Cjson.Basic
import Cjson.Parser
import Cjson.Printer

namespace Cjson

/-! ## Byte/digit inverses -/

theorem toNat_digitByte {d : Nat} (h : d < 10) : (digitByte d).toNat = d + 48 := by
  have h2 : d + 48 < 256 := by omega
  unfold digitByte
  simp [UInt8.ofNat, UInt8.toNat, Nat.mod_eq_of_lt h2]

theorem digitVal_digitByte {d : Nat} (h : d < 10) : digitVal (digitByte d) = d := by
  unfold digitVal
  rw [toNat_digitByte h]
  omega

theorem isDigitB_digitByte {d : Nat} (h : d < 10) : isDigitB (digitByte d) = true := by
  have h2 : d + 48 < 256 := by omega
  unfold isDigitB
  rw [toNat_digitByte h]
  simp only [decide_eq_true_eq, Bool.and_eq_true]
  omega

/-! ## scanDigits inverts digitBytes

`scanDigits` is greedy, so it only returns exactly `ds` when the following bytes cannot
continue the digit run. `NotDigitStart t` is that side condition; every call site below
discharges it with a structural byte (`.`, `e`, `,`, `]`, `}`) or with `[]`. -/

def NotDigitStart (t : Bytes) : Prop :=
  ∀ c t', t = c :: t' → isDigitB c = false

theorem scanDigits_digitBytes {ds : List Nat} {t : Bytes}
    (hd : ∀ d ∈ ds, d < 10) (ht : NotDigitStart t) :
    scanDigits (digitBytes ds ++ t) = (ds, t) := by
  induction ds with
  | nil =>
    cases t with
    | nil => simp [digitBytes, scanDigits]
    | cons c t' =>
      have := ht c t' rfl
      simp [digitBytes, scanDigits, this]
  | cons d ds ih =>
    have hd0 : d < 10 := hd d (by simp)
    have hds : ∀ x ∈ ds, x < 10 := fun x hx => hd x (by simp [hx])
    simp only [digitBytes, List.map_cons, List.cons_append, scanDigits,
      isDigitB_digitByte hd0, if_pos, digitVal_digitByte hd0]
    have := ih hds
    simp only [digitBytes] at this
    rw [this]

/-! ## natToDigits / ofDigits are inverse -/

theorem natToDigits_lt10 (n : Nat) : ∀ d ∈ natToDigits n, d < 10 := by
  induction n using natToDigits.induct with
  | case1 n h => intro d hd; simp [natToDigits, h] at hd; omega
  | case2 n h ih =>
    intro d hd
    rw [natToDigits, dif_neg h] at hd
    simp only [List.mem_append, List.mem_singleton] at hd
    rcases hd with hd | hd
    · exact ih d hd
    · omega

/-- Folding one more digit on the right multiplies by ten and adds. This is the only
    algebraic fact we need, and it avoids `10 ^ n` entirely — which matters because
    `ring` and `push_cast` are Mathlib tactics and this project is Mathlib-free. -/
theorem ofDigits_snoc (ds : List Nat) (x : Nat) :
    ofDigits (ds ++ [x]) = ofDigits ds * 10 + (x : Int) := by
  unfold ofDigits
  rw [List.foldl_append]
  simp

theorem ofDigits_natToDigits (n : Nat) : ofDigits (natToDigits n) = (n : Int) := by
  induction n using natToDigits.induct with
  | case1 n h => simp [natToDigits, h, ofDigits]
  | case2 n h ih =>
    rw [natToDigits, dif_neg h, ofDigits_snoc, ih]
    omega

end Cjson
