/-
  GAP-2, C4 leaf 1 — scanNumber_complete: SNumTok p n → SafeTail rest → scanNumber (p ++ rest) = some (n, rest).

  Independence: the grammar (SNumTok/SameNum) is NOT narrowed to canonical spellings. Arbitrary
  grammatical spellings (01, 1.0, 1e0, .5, arbitrary exponent/zero spellings) must go through,
  landing on the canonical `n` via normNum_denote + SameNum equivalence + A10 (canonical_unique).
  See INDEPENDENCE_RISK.md.

  Zero sorry, zero custom axioms.
-/
import Cjson.Spec.NumSound
import Cjson.Proofs.Digits    -- released: digitBytes, scanDigits_digitBytes
import Cjson.Proofs.Num       -- released: SafeTail (+ helpers), scanNumber_renderNum (unused)

namespace Cjson.Spec

open Cjson

/-! ## SameNum is an equivalence (needed to bridge normNum and n through the (M,E) class) -/

theorem SameNum_symm {ng₁ ng₂ : Bool} {m₁ e₁ m₂ e₂}
    (h : SameNum ng₁ m₁ e₁ ng₂ m₂ e₂) : SameNum ng₂ m₂ e₂ ng₁ m₁ e₁ := by
  unfold SameNum at *
  rcases h with ⟨a, b⟩ | ⟨hn, ha, hb, k, hk⟩
  · exact Or.inl ⟨b, a⟩
  · refine Or.inr ⟨hn.symm, hb, ha, k, ?_⟩
    rcases hk with h1 | h1
    · exact Or.inr h1
    · exact Or.inl h1

theorem pow_cancel {a b k1 k2 : Nat} (hle : k2 ≤ k1) (h : a * 10 ^ k1 = b * 10 ^ k2) :
    a * 10 ^ (k1 - k2) = b := by
  have hsplit : a * 10 ^ k1 = a * 10 ^ (k1 - k2) * 10 ^ k2 := by
    rw [Nat.mul_assoc, ← Nat.pow_add]; congr 2; omega
  rw [hsplit] at h
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_neZero _) h

theorem mul_pow_comm (a x y : Nat) : a * 10 ^ x * 10 ^ y = a * 10 ^ y * 10 ^ x := by
  rw [Nat.mul_assoc, Nat.mul_assoc, ← Nat.pow_add, ← Nat.pow_add, Nat.add_comm]

theorem SameNum_trans {ng₁ ng₂ ng₃ : Bool} {m₁ e₁ m₂ e₂ m₃ e₃}
    (h12 : SameNum ng₁ m₁ e₁ ng₂ m₂ e₂) (h23 : SameNum ng₂ m₂ e₂ ng₃ m₃ e₃) :
    SameNum ng₁ m₁ e₁ ng₃ m₃ e₃ := by
  unfold SameNum at *
  rcases h12 with ⟨z1, z2⟩ | ⟨hn12, ha1, ha2, k1, hk1⟩
  · rcases h23 with ⟨_, z3⟩ | ⟨_, hb2, _, _, _⟩
    · exact Or.inl ⟨z1, z3⟩
    · exact absurd z2 hb2
  · rcases h23 with ⟨z2', _⟩ | ⟨hn23, _, hb3, k2, hk2⟩
    · exact absurd z2' ha2
    · refine Or.inr ⟨hn12.trans hn23, ha1, hb3, ?_⟩
      rcases hk1 with ⟨e1, f1⟩ | ⟨e1, f1⟩ <;> rcases hk2 with ⟨e2, f2⟩ | ⟨e2, f2⟩
      · -- m₁=m₂·10^k1, m₂=m₃·10^k2
        exact ⟨k1 + k2, Or.inl ⟨by rw [e1, e2, Nat.mul_assoc, Nat.pow_add, Nat.mul_comm (10^k2)], by omega⟩⟩
      · -- m₁=m₂·10^k1, m₃=m₂·10^k2
        have key : m₃ * 10 ^ k1 = m₁ * 10 ^ k2 := by rw [e2, e1, mul_pow_comm]
        rcases Nat.le_total k2 k1 with hle | hle
        · exact ⟨k1 - k2, Or.inl ⟨(pow_cancel hle key).symm, by omega⟩⟩
        · exact ⟨k2 - k1, Or.inr ⟨(pow_cancel hle key.symm).symm, by omega⟩⟩
      · -- m₂=m₁·10^k1, m₂=m₃·10^k2
        have key : m₁ * 10 ^ k1 = m₃ * 10 ^ k2 := by rw [← e1, ← e2]
        rcases Nat.le_total k2 k1 with hle | hle
        · exact ⟨k1 - k2, Or.inr ⟨(pow_cancel hle key).symm, by omega⟩⟩
        · exact ⟨k2 - k1, Or.inl ⟨(pow_cancel hle key.symm).symm, by omega⟩⟩
      · -- m₂=m₁·10^k1, m₃=m₂·10^k2
        exact ⟨k1 + k2, Or.inr ⟨by rw [e2, e1, Nat.mul_assoc, Nat.pow_add, Nat.mul_comm (10^k1)], by omega⟩⟩


/-! ## Digit bridge: a `Digits` derivation is exactly `digitBytes` of its values -/

theorem digitByte_digitVal {c : UInt8} (h : isDigitB c = true) : digitByte (digitVal c) = c := by
  unfold isDigitB at h; unfold digitByte digitVal
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  have h1 : c.toNat - 48 + 48 = c.toNat := by omega
  rw [h1]; exact UInt8.ofNat_toNat

theorem Digits_eq_digitBytes {ip : Bytes} {ids : List Nat} (h : Digits ip ids) :
    ip = digitBytes ids := by
  induction h with
  | nil => rfl
  | cons hc hd _ ih =>
      subst hd
      show _ :: _ = digitByte (digitVal _) :: digitBytes _
      rw [digitByte_digitVal hc, ih]

theorem Digits_lt10 {ip : Bytes} {ids : List Nat} (h : Digits ip ids) : ∀ d ∈ ids, d < 10 := by
  induction h with
  | nil => simp
  | cons hc hd _ ih =>
    intro d hm
    rcases List.mem_cons.mp hm with rfl | hm2
    · unfold isDigitB at hc; simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [← hd]; unfold digitVal; omega
    · exact ih d hm2

/-- `scanDigits` completeness: it consumes exactly a `Digits`-block when the tail cannot
    continue a digit run. Reuses the released `scanDigits_digitBytes` via the bridge. -/
theorem scanDigits_complete {ip : Bytes} {ids : List Nat} {t : Bytes}
    (h : Digits ip ids) (ht : NotDigitStart t) : scanDigits (ip ++ t) = (ids, t) := by
  rw [Digits_eq_digitBytes h]
  exact scanDigits_digitBytes (Digits_lt10 h) ht


/-! ## Tail classification from the grammar structure -/

theorem head_notDigit_notDot {c : UInt8} (h : c = 101 ∨ c = 69) :
    isDigitB c = false ∧ c.toNat ≠ 46 := by
  rcases h with rfl | rfl <;> exact ⟨by decide, by decide⟩

/-- After the exponent part, `ep ++ rest` neither starts a digit run nor is `.`. -/
theorem expTail {ep : Bytes} {e : Int} {rest : Bytes} (hx : ExpPart ep e) (hs : SafeTail rest) :
    NotDigitStart (ep ++ rest) ∧ (∀ c t', ep ++ rest = c :: t' → c.toNat ≠ 46) := by
  cases hx with
  | none =>
    constructor
    · intro c t' he; simp only [List.nil_append] at he; exact (hs c t' he).1
    · intro c t' he; simp only [List.nil_append] at he; exact (hs c t' he).2.1
  | plain hc _ _ =>
    constructor
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).1
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).2
  | pos hc _ _ =>
    constructor
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).1
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).2
  | neg hc _ _ =>
    constructor
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).1
    · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
      obtain ⟨rfl, -⟩ := he; exact (head_notDigit_notDot hc).2

/-- The digit run of an exponent starts with a digit (so not `+`/`-`). -/
theorem Digits_head_digit {bs : Bytes} {ds : List Nat} (hd : Digits bs ds) (hne : ds ≠ []) :
    ∃ c bs', bs = c :: bs' ∧ isDigitB c = true := by
  cases hd with
  | nil => exact absurd rfl hne
  | cons hci _ _ => exact ⟨_, _, rfl, hci⟩

theorem scanExpDigits_complete {bs : Bytes} {ds : List Nat} {e : Int} {rest ep : Bytes}
    (hd : Digits bs ds) (hne : ds ≠ [])
    (hval : (ep = bs ∧ e = (natOf ds : Int)) ∨ (ep = 43 :: bs ∧ e = (natOf ds : Int))
            ∨ (ep = 45 :: bs ∧ e = -(natOf ds : Int)))
    (hnd : NotDigitStart rest) :
    scanExpDigits (ep ++ rest) = some (e, rest) := by
  have hbe : scanDigits (bs ++ rest) = (ds, rest) := scanDigits_complete hd hnd
  have hnemp : ¬ (scanDigits (bs ++ rest)).1.isEmpty = true := by rw [hbe]; simpa using hne
  have hof : ofDigits ds = (natOf ds : Int) := ofDigits_natOf ds
  rcases hval with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨c, bs', rfl, hcd⟩ := Digits_head_digit hd hne
    unfold isDigitB at hcd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hcd
    simp only [List.cons_append, scanExpDigits]
    rw [if_neg (by simp; omega), if_neg (by simp; omega)]
    rw [if_neg (by rw [← List.cons_append, hbe]; simpa using hne), ← List.cons_append, hbe, hof]
  · simp only [List.cons_append, scanExpDigits]
    rw [if_pos (by decide), if_neg hnemp, hbe, hof]
  · simp only [List.cons_append, scanExpDigits]
    rw [if_neg (by decide), if_pos (by decide), if_neg hnemp, hbe, hof]

theorem scanExp_complete {ep : Bytes} {e : Int} {rest : Bytes}
    (hx : ExpPart ep e) (hs : SafeTail rest) : scanExp (ep ++ rest) = (e, rest) := by
  cases hx with
  | none =>
    cases rest with
    | nil => rfl
    | cons c t =>
      obtain ⟨-, -, hce, hcE⟩ := hs c t rfl
      simp only [List.nil_append, scanExp]
      rw [if_neg (by simp only [Bool.or_eq_true, beq_iff_eq, not_or]; exact ⟨hce, hcE⟩)]
  | plain hc hd hne =>
    have hnd : NotDigitStart rest := fun c t' he => (hs c t' he).1
    simp only [List.cons_append, scanExp]
    rw [if_pos (by rcases hc with rfl | rfl <;> decide),
        scanExpDigits_complete hd hne (Or.inl ⟨rfl, rfl⟩) hnd]
  | pos hc hd hne =>
    have hnd : NotDigitStart rest := fun c t' he => (hs c t' he).1
    simp only [List.cons_append, scanExp]
    rw [if_pos (by rcases hc with rfl | rfl <;> decide)]
    have hcomp := scanExpDigits_complete hd hne (Or.inr (Or.inl ⟨rfl, rfl⟩)) hnd
    rw [List.cons_append] at hcomp; rw [hcomp]
  | neg hc hd hne =>
    have hnd : NotDigitStart rest := fun c t' he => (hs c t' he).1
    simp only [List.cons_append, scanExp]
    rw [if_pos (by rcases hc with rfl | rfl <;> decide)]
    have hcomp := scanExpDigits_complete hd hne (Or.inr (Or.inr ⟨rfl, rfl⟩)) hnd
    rw [List.cons_append] at hcomp; rw [hcomp]


/-! ## scanFrac / scanSign completeness -/

/-- `scanFrac` completeness. Two grammar shapes: no dot (`dot=fp=[]`, `fds=[]`), or `dot=[46]`
    with `Digits fp fds`. The tail after `fp` is the exponent-then-rest, classified by `expTail`. -/
theorem scanFrac_complete {dot fp ep : Bytes} {fds : List Nat} {e : Int} {rest : Bytes}
    (hdot : (dot = [] ∧ fp = [] ∧ fds = []) ∨ (dot = [46] ∧ Digits fp fds))
    (hx : ExpPart ep e) (hs : SafeTail rest) :
    scanFrac (dot ++ fp ++ ep ++ rest) = (fds, ep ++ rest) := by
  obtain ⟨hnd, hndot⟩ := expTail hx hs
  rcases hdot with ⟨rfl, rfl, rfl⟩ | ⟨rfl, hdf⟩
  · -- no fraction: scanFrac sees ep ++ rest, whose head is not '.'
    simp only [List.nil_append]
    cases hep : ep ++ rest with
    | nil => simp [scanFrac]
    | cons c t =>
      have := hndot c t hep
      simp only [scanFrac]
      rw [if_neg (by simp; omega)]
  · -- dot present: scanFrac (46 :: fp ++ ep ++ rest) = scanDigits (fp ++ ep ++ rest)
    have hfd : scanDigits (fp ++ (ep ++ rest)) = (fds, ep ++ rest) := scanDigits_complete hdf hnd
    simp only [List.cons_append, List.nil_append, scanFrac]
    rw [if_pos (by decide)]
    rw [← List.append_assoc] at hfd
    -- scanFrac (46 :: (fp ++ ep ++ rest)) = scanDigits (fp ++ ep ++ rest)
    show scanDigits (fp ++ ep ++ rest) = _
    exact hfd

/-- `scanSign` completeness. `sgn` is `[]` (neg=false, tail not starting with `-`) or `[45]`. -/
theorem scanSign_complete {sgn t : Bytes} {neg : Bool}
    (hsgn : (sgn = [] ∧ neg = false) ∨ (sgn = [45] ∧ neg = true))
    (htne : sgn = [] → ∀ c t', t = c :: t' → c.toNat ≠ 45) :
    scanSign (sgn ++ t) = (neg, t) := by
  rcases hsgn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases t with
    | nil => rfl
    | cons c t' =>
      have := htne rfl c t' rfl
      simp only [List.nil_append, scanSign]
      rw [if_neg (by simp; omega)]
  · simp only [List.cons_append, List.nil_append, scanSign]
    rw [if_pos (by decide)]



/-! ## First-byte facts to route scanNumber's internal decompositions -/

/-- `ip ++ dot ++ fp ++ ep ++ rest` cannot start a digit run *after* consuming `ip`:
    the byte after `ip` is `.`, or `e`/`E`, or a SafeTail `rest` byte. -/
theorem afterIntTail {dot fp ep : Bytes} {fds : List Nat} {e : Int} {rest : Bytes}
    (hdot : (dot = [] ∧ fp = [] ∧ fds = []) ∨ (dot = [46] ∧ Digits fp fds))
    (hx : ExpPart ep e) (hs : SafeTail rest) :
    NotDigitStart (dot ++ fp ++ ep ++ rest) := by
  rcases hdot with ⟨rfl, rfl, rfl⟩ | ⟨rfl, _⟩
  · simp only [List.nil_append]; exact (expTail hx hs).1
  · intro c t' he; simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he; decide

/-! ## THE completeness theorem for the number leaf -/

/-- **scanNumber_complete.** For every grammatical number token `p` (an *arbitrary* `SNumTok`
    spelling — `01`, `1.0`, `1e0`, `.5`, … — NOT restricted to the canonical rendering) and every
    `SafeTail rest`, the parser's `scanNumber` consumes exactly `p` and returns the grammar's
    canonical value `n`, leaving `rest`.

    The value clause routes through `normNum_denote` (parser normaliser ∈ the `SameNum` class of
    the token) and `canonical_unique` (**A10**): the parser's canonical output and the grammar's
    canonical `n` are `SameNum`-equivalent canonicals, hence equal. The grammar is NOT narrowed. -/
theorem scanNumber_complete {p : Bytes} {n : JNum} {rest : Bytes}
    (h : SNumTok p n) (hs : SafeTail rest) : scanNumber (p ++ rest) = some (n, rest) := by
  cases h with
  | @mk sgn neg ip fp ep ids fds e dot _n hsgn hip hdot hmant hx hcanon hsame =>
  -- 1. scanSign consumes sgn
  have hsign : scanSign ((sgn ++ ip ++ dot ++ fp ++ ep) ++ rest)
      = (neg, ip ++ dot ++ fp ++ ep ++ rest) := by
    rw [show (sgn ++ ip ++ dot ++ fp ++ ep) ++ rest
          = sgn ++ (ip ++ dot ++ fp ++ ep ++ rest) by simp [List.append_assoc]]
    refine scanSign_complete hsgn ?_
    -- if sgn = [], the head of ip ++ … is a digit or '.', never '-'
    intro hsgn0 c t' he
    rcases hdot with ⟨rfl, rfl, hfds0⟩ | ⟨rfl, hdf⟩
    · -- no dot: ip must be non-empty (else mantissa empty, contradicting hmant)
      cases hip with
      | nil =>
        simp only [List.nil_append] at hmant; exact absurd hfds0 hmant
      | cons hci _ _ =>
        simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        unfold isDigitB at hci; simp only [Bool.and_eq_true, decide_eq_true_eq] at hci; omega
    · cases hip with
      | nil => simp only [List.nil_append, List.cons_append, List.cons.injEq] at he
               obtain ⟨rfl, -⟩ := he; decide
      | cons hci _ _ =>
        simp only [List.cons_append, List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        unfold isDigitB at hci; simp only [Bool.and_eq_true, decide_eq_true_eq] at hci; omega
  -- 2. scanDigits consumes ip
  have hdig : scanDigits (ip ++ dot ++ fp ++ ep ++ rest) = (ids, dot ++ fp ++ ep ++ rest) := by
    rw [show ip ++ dot ++ fp ++ ep ++ rest = ip ++ (dot ++ fp ++ ep ++ rest) by
          simp [List.append_assoc]]
    exact scanDigits_complete hip (afterIntTail hdot hx hs)
  -- 3. scanFrac consumes dot ++ fp
  have hfrac : scanFrac (dot ++ fp ++ ep ++ rest) = (fds, ep ++ rest) := scanFrac_complete hdot hx hs
  -- 4. scanExp consumes ep
  have hexp : scanExp (ep ++ rest) = (e, rest) := scanExp_complete hx hs
  -- assemble scanNumber
  simp only [scanNumber]
  rw [hsign]
  simp only [hdig, hfrac, hexp]
  -- the `if ... isEmpty` guard is false because the mantissa ids ++ fds ≠ []
  have hguard : ¬ (ids.isEmpty && fds.isEmpty) = true := by
    simp only [Bool.and_eq_true, List.isEmpty_iff]
    rintro ⟨h1, h2⟩; exact hmant (by rw [h1, h2]; rfl)
  rw [if_neg hguard]
  -- value: normNum neg (ids ++ fds) (e - |fds|) = n
  suffices hval : normNum neg (ids ++ fds) (e - (fds.length : Int)) = n by rw [hval]
  -- both canonical, both SameNum to (neg, natOf(ids++fds), e - |fds|)
  have hden := normNum_denote neg (ids ++ fds) (e - (fds.length : Int))
  have hfds10 : ∀ d ∈ fds, d < 10 := by
    rcases hdot with ⟨_, _, rfl⟩ | ⟨_, hdf⟩
    · intro d hd; simp at hd
    · exact Digits_lt10 hdf
  have hids_fds10 : ∀ d ∈ ids ++ fds, d < 10 := by
    intro d hd
    rcases List.mem_append.mp hd with hm | hm
    · exact Digits_lt10 hip d hm
    · exact hfds10 d hm
  have hcanon' := normNum_canonical neg (ids ++ fds) (e - (fds.length : Int)) hids_fds10
  -- SameNum (normNum) n  via  symm(hden) ∘ hsame
  exact canonical_unique hcanon' hcanon (SameNum_trans (SameNum_symm hden) hsame)

end Cjson.Spec
