/-
  GAP-2, step 1 — **A10: canonical number uniqueness.**

  C2 says the parser returns *the* value the grammar assigns. That is only well-posed if the
  canonical `JNum` is a UNIQUE representative of each number. A10 establishes exactly that,
  and nothing more:

      Canonical n₁ → Canonical n₂ → SameNum (denote n₁) (denote n₂) → n₁ = n₂

  NOTE WHAT THIS IS NOT. It is *not* uniqueness of syntactic spelling: `100`, `1e2` and `1.0e2`
  are three different byte strings denoting the same number, and they must be. A10 says only
  that they all land on the same canonical AST node.

  Zero `sorry`, zero axioms.
-/
import Cjson.Spec.Grammar

namespace Cjson.Spec

open Cjson

/-! ## `natOf` on snoc — the only structural fact we need -/

/-- A snoc recursor, built from `List.reverse` (core Lean has no `reverseRecOn`). -/
theorem snocRec {α : Type} {motive : List α → Prop}
    (h0 : motive []) (hs : ∀ l a, motive l → motive (l ++ [a])) : ∀ l, motive l := by
  have key : ∀ r : List α, motive r.reverse := by
    intro r
    induction r with
    | nil => simpa using h0
    | cons a r ih => simpa [List.reverse_cons] using hs r.reverse a ih
  intro l
  simpa using key l.reverse

theorem natOf_snoc (l : List Nat) (d : Nat) : natOf (l ++ [d]) = natOf l * 10 + d := by
  induction l with
  | nil => simp [natOf]
  | cons a l ih =>
    have hp : a * 10 ^ (l.length + 1) = a * 10 ^ l.length * 10 := by
      rw [Nat.pow_succ, ← Nat.mul_assoc]
    simp only [List.cons_append, natOf, List.length_append, List.length_cons,
      List.length_nil, ih, hp]
    -- `a * 10 ^ n` is nonlinear for `omega`; abstract it.
    generalize a * 10 ^ l.length = X
    generalize natOf l = Y
    omega

/-- A digit list with a non-zero head denotes a non-zero number. -/
theorem natOf_pos {l : List Nat} (hne : l ≠ []) (hhd : l.head? ≠ some 0) : 0 < natOf l := by
  cases l with
  | nil => exact absurd rfl hne
  | cons d ds =>
    have hd : d ≠ 0 := by intro h; exact hhd (by simp [h])
    have : 0 < d * 10 ^ ds.length := by
      have h10 : 0 < 10 ^ ds.length := Nat.pos_of_neZero _
      exact Nat.mul_pos (by omega) h10
    simp only [natOf]
    omega

/-- The last digit is the value mod 10. This is what forces `k = 0` in `SameNum`. -/
theorem natOf_mod_ten {l : List Nat} {d : Nat} (hd : d < 10) :
    natOf (l ++ [d]) % 10 = d := by
  rw [natOf_snoc]
  omega

/-- Every non-empty list is a snoc. -/
theorem exists_snoc {α : Type} {l : List α} (h : l ≠ []) : ∃ ls d, l = ls ++ [d] := by
  induction l using snocRec with
  | h0 => exact absurd rfl h
  | hs ls d _ => exact ⟨ls, d, rfl⟩

/-! ## `natOf` is injective on well-formed digit lists

    "Well-formed" = no leading zero and every digit < 10. Both are needed: without
    `< 10`, `[12]` and `[1,2]` both denote 12; without the leading-zero condition,
    `[0,1]` and `[1]` both denote 1. -/

def NoLead (l : List Nat) : Prop := l.head? ≠ some 0
def Lt10 (l : List Nat) : Prop := ∀ d ∈ l, d < 10

theorem noLead_of_snoc {ls : List Nat} {d : Nat} (h : NoLead (ls ++ [d])) : NoLead ls := by
  cases ls with
  | nil => simp [NoLead]
  | cons a as => simpa [NoLead] using h

theorem lt10_of_snoc {ls : List Nat} {d : Nat} (h : Lt10 (ls ++ [d])) :
    Lt10 ls ∧ d < 10 := by
  constructor
  · intro x hx; exact h x (by simp [hx])
  · exact h d (by simp)

theorem natOf_inj : ∀ {l l' : List Nat}, NoLead l → NoLead l' → Lt10 l → Lt10 l' →
    natOf l = natOf l' → l = l' := by
  intro l
  induction l using snocRec with
  | h0 =>
    intro l' _ hn' _ _ heq
    cases hl' : l' with
    | nil => rfl
    | cons a as =>
      exfalso
      subst hl'
      have hp : 0 < natOf (a :: as) := natOf_pos (by simp) hn'
      rw [show natOf ([] : List Nat) = 0 from rfl] at heq
      omega
  | hs ls d ih =>
    intro l' hn hn' hlt hlt' heq
    obtain ⟨hlts, hd10⟩ := lt10_of_snoc hlt
    have hl'ne : l' ≠ [] := by
      intro h0
      rw [h0] at heq
      simp only [natOf] at heq
      rw [natOf_snoc] at heq
      -- ls ++ [d] denotes 0, so its head would have to be 0
      have hpos : 0 < natOf (ls ++ [d]) := natOf_pos (by simp) hn
      rw [natOf_snoc] at hpos
      omega
    obtain ⟨ls', d', rfl⟩ := exists_snoc hl'ne
    obtain ⟨hlts', hd10'⟩ := lt10_of_snoc hlt'
    rw [natOf_snoc, natOf_snoc] at heq
    have hdd : d = d' := by omega
    have hss : natOf ls = natOf ls' := by omega
    have := ih (noLead_of_snoc hn) (noLead_of_snoc hn') hlts hlts' hss
    rw [this, hdd]

/-! ## A10 -/

/-- The canonicity predicate, unpacked into the two facts the proof needs. -/
theorem canon_parts {n : JNum} (h : JNum.Canonical n) :
    (n.digits = [] ∧ n.neg = false ∧ n.exp = 0)
    ∨ (n.digits ≠ [] ∧ NoLead n.digits ∧ n.digits.getLast? ≠ some 0 ∧ Lt10 n.digits) := by
  rcases h with ⟨a, b, c⟩ | ⟨a, b, c, d⟩
  · exact Or.inl ⟨a, b, c⟩
  · exact Or.inr ⟨a, b, c, d⟩

/-- A canonical non-zero mantissa is not divisible by ten. -/
theorem canon_not_div_ten {l : List Nat} (hne : l ≠ []) (hlast : l.getLast? ≠ some 0)
    (hlt : Lt10 l) : natOf l % 10 ≠ 0 := by
  obtain ⟨ls, d, rfl⟩ := exists_snoc hne
  obtain ⟨-, hd10⟩ := lt10_of_snoc hlt
  have hd0 : d ≠ 0 := by
    intro h
    exact hlast (by rw [List.getLast?_concat]; rw [h])
  rw [natOf_mod_ten hd10]
  exact hd0

/-- **A10 — canonical number uniqueness.**

    Two canonical `JNum`s that denote the same exact decimal ARE the same `JNum`.
    Therefore "the value the grammar assigns" is well-defined, and C2 is well-posed. -/
theorem canonical_unique {n₁ n₂ : JNum}
    (h₁ : JNum.Canonical n₁) (h₂ : JNum.Canonical n₂)
    (hsame : SameNum n₁.neg (natOf n₁.digits) n₁.exp n₂.neg (natOf n₂.digits) n₂.exp) :
    n₁ = n₂ := by
  obtain ⟨neg₁, ds₁, e₁⟩ := n₁
  obtain ⟨neg₂, ds₂, e₂⟩ := n₂
  -- unfold `Canonical` and reduce the structure projections, so the fields are visible
  simp only [JNum.Canonical] at h₁ h₂
  dsimp only at hsame h₁ h₂ ⊢
  rcases hsame with ⟨hz₁, hz₂⟩ | ⟨hneg, hm₁, hm₂, k, hk⟩
  · -- both denote zero: canonicity forces the zero node on both sides
    have g₁ : ds₁ = [] ∧ neg₁ = false ∧ e₁ = 0 := by
      rcases h₁ with ⟨a, b, c⟩ | ⟨a, b, -, -⟩
      · exact ⟨a, b, c⟩
      · exact absurd (natOf_pos a b) (by omega)
    have g₂ : ds₂ = [] ∧ neg₂ = false ∧ e₂ = 0 := by
      rcases h₂ with ⟨a, b, c⟩ | ⟨a, b, -, -⟩
      · exact ⟨a, b, c⟩
      · exact absurd (natOf_pos a b) (by omega)
    simp [g₁.1, g₁.2.1, g₁.2.2, g₂.1, g₂.2.1, g₂.2.2]
  · -- both non-zero: `k = 0`, because a canonical mantissa is not divisible by ten
    have p₁ : ds₁ ≠ [] ∧ NoLead ds₁ ∧ ds₁.getLast? ≠ some 0 ∧ Lt10 ds₁ := by
      rcases h₁ with ⟨a, -, -⟩ | h
      · exact absurd (by rw [a]; rfl) hm₁
      · exact h
    have p₂ : ds₂ ≠ [] ∧ NoLead ds₂ ∧ ds₂.getLast? ≠ some 0 ∧ Lt10 ds₂ := by
      rcases h₂ with ⟨a, -, -⟩ | h
      · exact absurd (by rw [a]; rfl) hm₂
      · exact h
    have nd₁ : natOf ds₁ % 10 ≠ 0 := canon_not_div_ten p₁.1 p₁.2.2.1 p₁.2.2.2
    have nd₂ : natOf ds₂ % 10 ≠ 0 := canon_not_div_ten p₂.1 p₂.2.2.1 p₂.2.2.2
    have hk0 : k = 0 := by
      rcases Nat.eq_zero_or_pos k with h0 | hpos
      · exact h0
      · exfalso
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        rcases hk with ⟨hm, -⟩ | ⟨hm, -⟩
        · exact nd₁ (by rw [hm, Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ 10)
        · exact nd₂ (by rw [hm, Nat.pow_succ, ← Nat.mul_assoc]; exact Nat.mul_mod_left _ 10)
    subst hk0
    simp only [Nat.pow_zero, Nat.mul_one] at hk
    have hds : ds₁ = ds₂ ∧ e₁ = e₂ := by
      rcases hk with ⟨a, b⟩ | ⟨a, b⟩
      · exact ⟨natOf_inj p₁.2.1 p₂.2.1 p₁.2.2.2 p₂.2.2.2 a, by omega⟩
      · exact ⟨natOf_inj p₁.2.1 p₂.2.1 p₁.2.2.2 p₂.2.2.2 a.symm, by omega⟩
    simp [hneg, hds.1, hds.2]

end Cjson.Spec
