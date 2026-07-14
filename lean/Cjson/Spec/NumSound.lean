/-
  GAP-2, step 2 — NUMBER SOUNDNESS.

      scanNumber s = some (n, r)  →  ∃ p, s = p ++ r ∧ SNumTok p n

  i.e. whatever bytes the parser's number scanner consumed form a token that the SPEC grammar
  assigns exactly the value `n`.

  INDEPENDENCE CONTRACT (see INDEPENDENCE_RISK.md). The grammar's number semantics are the
  `SameNum` equivalence on raw triples `± m·10^e`. The parser's are `normNum`, a normaliser.
  The tempting shortcut is to redefine the grammar in terms of `normNum` — that would make the
  theorem trivial and destroy the independence argument. We do NOT do that. Instead
  `normNum_denote` below proves that `normNum` *lands in the same `SameNum` class*, which is a
  real obligation and the crux of this file.

  Zero `sorry`, zero axioms.
-/
import Cjson.Spec.Uniqueness

namespace Cjson.Spec

open Cjson

/-! ## `natOf` and zeros -/

theorem natOf_cons_zero (ds : List Nat) : natOf (0 :: ds) = natOf ds := by
  simp [natOf]

theorem natOf_dropWhile_zero (l : List Nat) :
    natOf (l.dropWhile (fun x => x == 0)) = natOf l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    by_cases h : (d == 0) = true
    · have hd : d = 0 := by simpa using h
      subst hd
      rw [List.dropWhile_cons_of_pos (by simpa using h), ih, natOf_cons_zero]
    · rw [List.dropWhile_cons_of_neg (by simpa using h)]

/-- Core Lean has no `mem_takeWhile_imp`; prove it. -/
theorem mem_takeWhile {p : Nat → Bool} {l : List Nat} {x : Nat}
    (h : x ∈ l.takeWhile p) : p x = true := by
  induction l with
  | nil => simp [List.takeWhile] at h
  | cons a as ih =>
    by_cases ha : p a = true
    · rw [List.takeWhile_cons_of_pos ha] at h
      rcases List.mem_cons.mp h with rfl | h'
      · exact ha
      · exact ih h'
    · rw [List.takeWhile_cons_of_neg (by simpa using ha)] at h
      simp at h

/-- Appending `k` zeros multiplies the denotation by `10^k`. -/
theorem natOf_append_zeros {A zs : List Nat} (hz : ∀ x ∈ zs, x = 0) :
    natOf (A ++ zs) = natOf A * 10 ^ zs.length := by
  induction zs using snocRec with
  | h0 => simp [Nat.pow_zero]
  | hs zs' z ih =>
    have hz' : ∀ x ∈ zs', x = 0 := fun x hx => hz x (by simp [hx])
    have hz0 : z = 0 := hz z (by simp)
    subst hz0
    have : A ++ (zs' ++ [0]) = (A ++ zs') ++ [0] := by simp
    rw [this, natOf_snoc, ih hz']
    have hl : (zs' ++ [0]).length = zs'.length + 1 := by simp
    rw [hl, Nat.pow_succ, ← Nat.mul_assoc]
    simp

/-- A list is its trailing-zero-stripped prefix followed by the stripped zeros. -/
theorem split_trailing (l : List Nat) :
    l = ((l.reverse.dropWhile (fun x => x == 0)).reverse)
        ++ ((l.reverse.takeWhile (fun x => x == 0)).reverse)
    ∧ (∀ x ∈ (l.reverse.takeWhile (fun x => x == 0)).reverse, x = 0) := by
  constructor
  · have h := List.takeWhile_append_dropWhile (p := fun x => x == 0) (l := l.reverse)
    calc l = l.reverse.reverse := (List.reverse_reverse l).symm
    _ = (List.takeWhile (fun x => x == 0) l.reverse
          ++ List.dropWhile (fun x => x == 0) l.reverse).reverse := by rw [h]
    _ = _ := by rw [List.reverse_append]
  · intro x hx
    rw [List.mem_reverse] at hx
    have := mem_takeWhile hx
    simpa using this

/-! ## `normNum` lands in the right `SameNum` class

    This is the crux. It is what lets the grammar keep its own (parser-independent) number
    semantics while still being provable about the parser. -/

theorem normNum_denote (neg : Bool) (ds : List Nat) (e : Int) :
    SameNum neg (natOf ds) e
            (normNum neg ds e).neg (natOf (normNum neg ds e).digits) (normNum neg ds e).exp := by
  -- abbreviations (core Lean has no `set` tactic)
  obtain ⟨ds1, h1⟩ : ∃ x, ds.dropWhile (fun x => x == 0) = x := ⟨_, rfl⟩
  obtain ⟨ds2, h2⟩ : ∃ x, (ds1.reverse.dropWhile (fun x => x == 0)).reverse = x := ⟨_, rfl⟩
  obtain ⟨zs, h3⟩ : ∃ x, (ds1.reverse.takeWhile (fun x => x == 0)).reverse = x := ⟨_, rfl⟩
  obtain ⟨hsp, hz0⟩ := split_trailing ds1
  rw [h2, h3] at hsp
  rw [h3] at hz0
  have hds : natOf ds = natOf ds1 := by rw [← h1]; exact (natOf_dropWhile_zero ds).symm
  have hval : natOf ds1 = natOf ds2 * 10 ^ zs.length := by
    rw [hsp]
    exact natOf_append_zeros hz0
  -- ds1 has no leading zero (it is a `dropWhile` of zeros)
  have hd1 : ds1.head? ≠ some 0 := by
    intro hc
    rw [← h1] at hc
    have := head?_dropWhile (p := fun x => x == 0) (l := ds) (x := 0) hc
    simp at this
  unfold normNum
  simp only []
  rw [h1, h2]
  split
  · -- ds2 empty ⇒ the number is zero
    next hzero =>
      have he : ds2 = [] := by simpa [List.isEmpty_iff] using hzero
      refine Or.inl ⟨?_, by simp [JNum.zero, natOf]⟩
      rw [hds, hval, he]
      simp [natOf]
  · -- ds2 non-empty
    next hzero =>
      have hne : ds2 ≠ [] := by simpa [List.isEmpty_iff] using hzero
      have hhd : ds2.head? ≠ some 0 := by
        cases hc : ds2 with
        | nil => exact absurd hc hne
        | cons a as =>
          have hh : ds1.head? = some a := by rw [hsp, hc]; rfl
          intro hcon
          simp only [List.head?_cons, Option.some.injEq] at hcon
          subst hcon
          exact hd1 hh
      have hm2 : natOf ds2 ≠ 0 := by
        have := natOf_pos hne hhd
        omega
      have hm1 : natOf ds ≠ 0 := by
        rw [hds, hval]
        have hp : 0 < 10 ^ zs.length := Nat.pos_of_neZero _
        have := Nat.mul_pos (Nat.pos_of_ne_zero hm2) hp
        omega
      have hlen : (ds1.length - ds2.length : Nat) = zs.length := by
        have := congrArg List.length hsp
        simp only [List.length_append] at this
        omega
      refine Or.inr ⟨rfl, hm1, by simpa using hm2, zs.length, Or.inl ⟨?_, ?_⟩⟩
      · dsimp only
        rw [hds, hval]
      · dsimp only
        rw [hlen]

/-! ## The scanners produce grammar derivations -/

theorem scanDigits_sound (s : Bytes) :
    ∃ p, s = p ++ (scanDigits s).2 ∧ Digits p (scanDigits s).1 := by
  induction s with
  | nil => exact ⟨[], by simp [scanDigits], by simp [scanDigits]; exact Digits.nil⟩
  | cons c cs ih =>
    by_cases h : isDigitB c = true
    · obtain ⟨p, hp, hd⟩ := ih
      refine ⟨c :: p, ?_, ?_⟩
      · simp only [scanDigits, if_pos h, List.cons_append]
        exact congrArg (c :: ·) hp
      · simp only [scanDigits, if_pos h]
        exact Digits.cons h rfl hd
    · exact ⟨[], by simp [scanDigits, h], by simp [scanDigits, h]; exact Digits.nil⟩

theorem scanDigits_lt10' (s : Bytes) : ∀ d ∈ (scanDigits s).1, d < 10 := scanDigits_lt10 s




/-- The parser's `ofDigits` (a Horner fold, `Int`) and the grammar's `natOf` (positional,
    `Nat`) denote the same number. -/
theorem ofDigits_natOf (ds : List Nat) : ofDigits ds = (natOf ds : Int) := by
  induction ds using snocRec with
  | h0 => simp [ofDigits, natOf]
  | hs l d ih =>
    have h1 : ofDigits (l ++ [d]) = ofDigits l * 10 + (d : Int) := by
      unfold ofDigits
      rw [List.foldl_append]
      simp
    rw [h1, ih, natOf_snoc]
    omega

/-- `scanFrac` either consumes nothing, or consumes `.` followed by (possibly zero) digits.
    The second case with zero digits is what makes `1.` a number (SPEC §S3.1, ambiguity A1). -/
theorem scanFrac_sound (s : Bytes) :
    ((scanFrac s).1 = [] ∧ (scanFrac s).2 = s)
    ∨ (∃ fp, s = 46 :: (fp ++ (scanFrac s).2) ∧ Digits fp (scanFrac s).1) := by
  cases s with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons c cs =>
    by_cases h : (c.toNat == 46) = true
    · right
      obtain ⟨fp, hfp, hd⟩ := scanDigits_sound cs
      have hc : c = 46 := by
        have : c.toNat = 46 := by simpa using h
        exact UInt8.toNat_inj.mp (by rw [this]; rfl)
      refine ⟨fp, ?_, ?_⟩
      · simp only [scanFrac, if_pos h, hc]
        exact congrArg (46 :: ·) hfp
      · simp only [scanFrac, if_pos h]
        exact hd
    · left
      exact ⟨by simp [scanFrac, h], by simp [scanFrac, h]⟩


/-- `scanExpDigits` soundness: it consumes an optional sign then a NON-EMPTY digit run. -/
theorem scanExpDigits_sound {cs : Bytes} {e : Int} {r : Bytes}
    (h : scanExpDigits cs = some (e, r)) :
    ∃ bs ds, Digits bs ds ∧ ds ≠ [] ∧
      ((cs = bs ++ r ∧ e = (natOf ds : Int))
       ∨ (cs = 43 :: (bs ++ r) ∧ e = (natOf ds : Int))
       ∨ (cs = 45 :: (bs ++ r) ∧ e = -(natOf ds : Int))) := by
  cases cs with
  | nil => simp [scanExpDigits] at h
  | cons sg cs' =>
    simp only [scanExpDigits] at h
    by_cases hp : (sg.toNat == 43) = true
    · rw [if_pos hp] at h
      by_cases hE : (scanDigits cs').1.isEmpty = true
      · rw [if_pos hE] at h; exact absurd h (by simp)
      · rw [if_neg hE] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨he, hr⟩ := h
        obtain ⟨bs, hbs, hd⟩ := scanDigits_sound cs'
        have hsg : sg = 43 := UInt8.toNat_inj.mp (by simpa using hp)
        refine ⟨bs, (scanDigits cs').1, hd, by simpa [List.isEmpty_iff] using hE, Or.inr (Or.inl ⟨?_, ?_⟩)⟩
        · rw [hsg, ← hr]; exact congrArg (43 :: ·) hbs
        · rw [← he]; exact ofDigits_natOf _
    · by_cases hm : (sg.toNat == 45) = true
      · rw [if_neg hp, if_pos hm] at h
        by_cases hE : (scanDigits cs').1.isEmpty = true
        · rw [if_pos hE] at h; exact absurd h (by simp)
        · rw [if_neg hE] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨he, hr⟩ := h
          obtain ⟨bs, hbs, hd⟩ := scanDigits_sound cs'
          have hsg : sg = 45 := UInt8.toNat_inj.mp (by simpa using hm)
          refine ⟨bs, (scanDigits cs').1, hd, by simpa [List.isEmpty_iff] using hE,
                  Or.inr (Or.inr ⟨?_, ?_⟩)⟩
          · rw [hsg, ← hr]; exact congrArg (45 :: ·) hbs
          · rw [← he, ofDigits_natOf]
      · rw [if_neg hp, if_neg hm] at h
        by_cases hE : (scanDigits (sg :: cs')).1.isEmpty = true
        · rw [if_pos hE] at h; exact absurd h (by simp)
        · rw [if_neg hE] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨he, hr⟩ := h
          obtain ⟨bs, hbs, hd⟩ := scanDigits_sound (sg :: cs')
          refine ⟨bs, (scanDigits (sg :: cs')).1, hd,
                  by simpa [List.isEmpty_iff] using hE, Or.inl ⟨?_, ?_⟩⟩
          · rw [← hr]; exact hbs
          · rw [← he]; exact ofDigits_natOf _

/-- `scanExp` consumes a grammatical exponent suffix (possibly the empty one). -/
theorem scanExp_sound (s : Bytes) :
    ∃ ep, s = ep ++ (scanExp s).2 ∧ ExpPart ep (scanExp s).1 := by
  cases s with
  | nil => exact ⟨[], rfl, ExpPart.none⟩
  | cons c cs =>
    by_cases he : (c.toNat == 101 || c.toNat == 69) = true
    · have hc : c = 101 ∨ c = 69 := by
        simp only [Bool.or_eq_true, beq_iff_eq] at he
        rcases he with h | h
        · exact Or.inl (UInt8.toNat_inj.mp (by rw [h]; rfl))
        · exact Or.inr (UInt8.toNat_inj.mp (by rw [h]; rfl))
      cases hx : scanExpDigits cs with
      | none =>
        refine ⟨[], ?_, ?_⟩
        · simp [scanExp, he, hx]
        · rw [show (scanExp (c :: cs)).1 = 0 by simp [scanExp, he, hx]]; exact ExpPart.none
      | some p =>
        obtain ⟨e, r⟩ := p
        obtain ⟨bs, ds, hd, hne, hcase⟩ := scanExpDigits_sound hx
        have hE1 : (scanExp (c :: cs)).1 = e := by simp [scanExp, he, hx]
        have hE2 : (scanExp (c :: cs)).2 = r := by simp [scanExp, he, hx]
        rw [hE1, hE2]
        rcases hcase with ⟨hcs, hev⟩ | ⟨hcs, hev⟩ | ⟨hcs, hev⟩
        · exact ⟨c :: bs, by simp [hcs], by rw [hev]; exact ExpPart.plain hc hd hne⟩
        · exact ⟨c :: 43 :: bs, by simp [hcs], by rw [hev]; exact ExpPart.pos hc hd hne⟩
        · exact ⟨c :: 45 :: bs, by simp [hcs], by rw [hev]; exact ExpPart.neg hc hd hne⟩
    · refine ⟨[], ?_, ?_⟩
      · simp [scanExp, he]
      · rw [show (scanExp (c :: cs)).1 = 0 by simp [scanExp, he]]; exact ExpPart.none


theorem scanFrac_lt10 (s : Bytes) : ∀ d ∈ (scanFrac s).1, d < 10 := by
  cases s with
  | nil => simp [scanFrac]
  | cons c cs =>
    by_cases h : (c.toNat == 46) = true
    · rw [scanFrac, if_pos h]; exact scanDigits_lt10 cs
    · rw [scanFrac, if_neg h]; simp

/-! ## THE number soundness theorem -/

theorem scanSign_sound (s : Bytes) :
    ((scanSign s).1 = false ∧ (scanSign s).2 = s)
    ∨ ((scanSign s).1 = true ∧ s = 45 :: (scanSign s).2) := by
  cases s with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons c cs =>
    by_cases h : (c.toNat == 45) = true
    · right
      have hc : c = 45 := UInt8.toNat_inj.mp (by simpa using h)
      exact ⟨by simp [scanSign, h], by simp [scanSign, h, hc]⟩
    · exact Or.inl ⟨by simp [scanSign, h], by simp [scanSign, h]⟩

/-- **NUMBER SOUNDNESS.** Whatever bytes `scanNumber` consumed form a token that the SPEC
    grammar assigns exactly the value the parser returned.

    This does NOT establish the §S2 dispatch gate (that `+1`/`.5` are rejected at value
    position): that gate lives in `parseValue`, not in `scanNumber`, and is discharged by the
    caller. It also does NOT establish maximal munch (C3, deferred). -/
theorem scanNumber_sound {s : Bytes} {n : JNum} {r : Bytes}
    (h : scanNumber s = some (n, r)) : ∃ p, s = p ++ r ∧ SNumTok p n := by
  simp only [scanNumber] at h
  split at h
  · exact absurd h (by simp)
  · next hne =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hn, hr⟩ := h
    -- names for the pieces
    obtain ⟨ip, hip, hdi⟩ := scanDigits_sound (scanSign s).2
    obtain ⟨ep, hep, hxp⟩ := scanExp_sound (scanFrac (scanDigits (scanSign s).2).2).2
    have hmant : (scanDigits (scanSign s).2).1 ++ (scanFrac (scanDigits (scanSign s).2).2).1 ≠ [] := by
      intro hc
      apply hne
      have h1 : (scanDigits (scanSign s).2).1 = [] := by
        cases hx : (scanDigits (scanSign s).2).1 with
        | nil => rfl
        | cons a as => rw [hx] at hc; simp at hc
      have h2 : (scanFrac (scanDigits (scanSign s).2).2).1 = [] := by
        rw [h1] at hc; simpa using hc
      simp [h1, h2]
    -- the fractional part
    rcases scanFrac_sound (scanDigits (scanSign s).2).2 with ⟨hf1, hf2⟩ | ⟨fp, hfp, hdf⟩
    · -- no dot
      rcases scanSign_sound s with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · refine ⟨ip ++ [] ++ [] ++ ep, ?_, ?_⟩
        · rw [← hr]
          calc s = (scanSign s).2 := hs2.symm
          _ = ip ++ (scanDigits (scanSign s).2).2 := hip
          _ = ip ++ ((scanFrac (scanDigits (scanSign s).2).2).2) := by rw [hf2]
          _ = ip ++ (ep ++ (scanExp (scanFrac (scanDigits (scanSign s).2).2).2).2) := by rw [← hep]
          _ = ip ++ [] ++ [] ++ ep ++ _ := by simp
        · rw [← hn]
          exact SNumTok.mk (Or.inl ⟨rfl, hs1⟩) hdi (Or.inl ⟨rfl, rfl, hf1⟩) hmant hxp
            (normNum_canonical _ _ _ (by
              intro d hd
              rcases List.mem_append.mp hd with hm | hm
              · exact scanDigits_lt10 _ d hm
              · exact scanFrac_lt10 _ d hm))
            (normNum_denote _ _ _)
      · exact ⟨[45] ++ ip ++ [] ++ [] ++ ep, by
          rw [← hr]
          calc s = 45 :: (scanSign s).2 := hs2
          _ = 45 :: (ip ++ (scanDigits (scanSign s).2).2) := by rw [← hip]
          _ = 45 :: (ip ++ ((scanFrac (scanDigits (scanSign s).2).2).2)) := by rw [hf2]
          _ = 45 :: (ip ++ (ep ++ (scanExp (scanFrac (scanDigits (scanSign s).2).2).2).2)) := by
                rw [← hep]
          _ = [45] ++ ip ++ [] ++ [] ++ ep ++ _ := by simp, by
          rw [← hn]
          exact SNumTok.mk (Or.inr ⟨rfl, hs1⟩) hdi (Or.inl ⟨rfl, rfl, hf1⟩) hmant hxp
            (normNum_canonical _ _ _ (by
              intro d hd
              rcases List.mem_append.mp hd with hm | hm
              · exact scanDigits_lt10 _ d hm
              · exact scanFrac_lt10 _ d hm))
            (normNum_denote _ _ _)⟩
    · -- there IS a dot
      rcases scanSign_sound s with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
      · refine ⟨ip ++ [46] ++ fp ++ ep, ?_, ?_⟩
        · rw [← hr]
          calc s = (scanSign s).2 := hs2.symm
          _ = ip ++ (scanDigits (scanSign s).2).2 := hip
          _ = ip ++ (46 :: (fp ++ (scanFrac (scanDigits (scanSign s).2).2).2)) := by rw [← hfp]
          _ = ip ++ (46 :: (fp ++ (ep ++ (scanExp (scanFrac (scanDigits (scanSign s).2).2).2).2)))
                := by rw [← hep]
          _ = ip ++ [46] ++ fp ++ ep ++ _ := by simp
        · rw [← hn]
          exact SNumTok.mk (Or.inl ⟨rfl, hs1⟩) hdi (Or.inr ⟨rfl, hdf⟩) hmant hxp
            (normNum_canonical _ _ _ (by
              intro d hd
              rcases List.mem_append.mp hd with hm | hm
              · exact scanDigits_lt10 _ d hm
              · exact scanFrac_lt10 _ d hm))
            (normNum_denote _ _ _)
      · refine ⟨[45] ++ ip ++ [46] ++ fp ++ ep, ?_, ?_⟩
        · rw [← hr]
          calc s = 45 :: (scanSign s).2 := hs2
          _ = 45 :: (ip ++ (scanDigits (scanSign s).2).2) := by rw [← hip]
          _ = 45 :: (ip ++ (46 :: (fp ++ (scanFrac (scanDigits (scanSign s).2).2).2))) := by rw [← hfp]
          _ = 45 :: (ip ++ (46 :: (fp ++ (ep ++ (scanExp (scanFrac (scanDigits (scanSign s).2).2).2).2))))
                := by rw [← hep]
          _ = [45] ++ ip ++ [46] ++ fp ++ ep ++ _ := by simp
        · rw [← hn]
          exact SNumTok.mk (Or.inr ⟨rfl, hs1⟩) hdi (Or.inr ⟨rfl, hdf⟩) hmant hxp
            (normNum_canonical _ _ _ (by
              intro d hd
              rcases List.mem_append.mp hd with hm | hm
              · exact scanDigits_lt10 _ d hm
              · exact scanFrac_lt10 _ d hm))
            (normNum_denote _ _ _)

end Cjson.Spec
