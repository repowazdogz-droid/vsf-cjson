/-
  Phase 4b, part 1: the number round-trip.

      scanNumber (renderNum n ++ rest) = some (n, rest)

  for every CANONICAL n and every SAFE rest.

  "Safe" is load-bearing and is not a technicality. The theorem is FALSE for arbitrary
  `rest`: `renderNum 1 = "1"`, and `scanNumber ("1" ++ "2")` is `12`, not `1`. A JSON
  number has no terminator, so it can only be recovered when the following bytes cannot
  continue the token. At every site where the serializer actually emits a number, the
  next byte is `,`, `]`, `}` or end-of-input — which is exactly `SafeTail`.
-/
import Cjson.Proofs.Digits

namespace Cjson

/-! ## Canonical digit strings -/

structure CanonDigits (ds : List Nat) : Prop where
  ne : ds ≠ []
  hd : ds.head? ≠ some 0
  tl : ds.getLast? ≠ some 0
  lt : ∀ d ∈ ds, d < 10

theorem canon_of_JNum {n : JNum} (h : JNum.Canonical n) (hne : n.digits ≠ []) :
    CanonDigits n.digits := by
  rcases h with ⟨h0, -, -⟩ | ⟨h1, h2, h3, h4⟩
  · exact absurd h0 hne
  · exact ⟨h1, h2, h3, h4⟩

/-! ## dropWhile over zero-runs

One lemma serves both directions: stripping leading zeros, and (applied to the reversed
list) stripping trailing zeros. -/

theorem dropWhile_zeros (zs ds : List Nat)
    (hz : ∀ x ∈ zs, x = 0) (hd : ds.head? ≠ some 0) :
    (zs ++ ds).dropWhile (fun x => x == 0) = ds := by
  induction zs with
  | nil =>
    cases ds with
    | nil => simp
    | cons d ds' =>
      have : d ≠ 0 := by
        intro h; exact hd (by simp [h])
      simp [List.dropWhile, this]
  | cons z zs ih =>
    have hz0 : z = 0 := hz z (by simp)
    have hzs : ∀ x ∈ zs, x = 0 := fun x hx => hz x (by simp [hx])
    simp [List.dropWhile, hz0, ih hzs]

theorem head?_append_ne {ds t : List Nat} (hne : ds ≠ []) (hd : ds.head? ≠ some 0) :
    (ds ++ t).head? ≠ some 0 := by
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds' => simpa using (by simpa using hd)

/-- No trailing zero means the reversed list has no LEADING zero. -/
theorem head?_reverse_ne {ds : List Nat} (hc : CanonDigits ds) :
    ds.reverse.head? ≠ some 0 := by
  cases hrev : ds.reverse with
  | nil => simp
  | cons a as =>
    have hlast : ds.getLast? = some a := by
      rw [List.getLast?_eq_head?_reverse, hrev]; rfl
    intro hcon
    simp only [List.head?_cons, Option.some.injEq] at hcon
    exact hc.tl (by rw [hlast, hcon])

/-- A canonical digit list has no trailing zero, so `dropWhile (== 0)` on its reverse
    strips nothing. Shared by the trailing- and leading-zero shapes below. -/
theorem dropWhile_reverse_canon {ds : List Nat} (hc : CanonDigits ds) :
    ds.reverse.dropWhile (fun x => x == 0) = ds.reverse := by
  have := dropWhile_zeros [] ds.reverse (by simp) (head?_reverse_ne hc)
  simpa using this

/-! ## normNum on the shapes the printer actually produces -/

/-- Trailing-zero shape (printer branch 1: `ds` followed by `m` zeros). -/
theorem normNum_trailing (neg : Bool) (ds : List Nat) (m : Nat) (e : Int)
    (hc : CanonDigits ds) :
    normNum neg (ds ++ List.replicate m 0) e = ⟨neg, ds, e + (m : Int)⟩ := by
  have hz : ∀ x ∈ List.replicate m 0, x = 0 := fun x hx => List.eq_of_mem_replicate hx
  have h1 : (ds ++ List.replicate m 0).dropWhile (fun x => x == 0)
      = ds ++ List.replicate m 0 := by
    have := dropWhile_zeros [] (ds ++ List.replicate m 0) (by simp)
      (head?_append_ne hc.ne hc.hd)
    simpa using this
  have h2 : (((ds ++ List.replicate m 0).reverse).dropWhile (fun x => x == 0)).reverse = ds := by
    rw [List.reverse_append, List.reverse_replicate,
        dropWhile_zeros (List.replicate m 0) ds.reverse hz (head?_reverse_ne hc)]
    exact List.reverse_reverse ds
  unfold normNum
  simp only [h1, h2]
  have hne : ¬ (ds.isEmpty = true) := by simp [List.isEmpty_iff, hc.ne]
  simp only [hne, if_false, List.length_append, List.length_replicate]
  simp

/-- Leading-zero shape (printer branch 3: `0`, then `z` zeros, then `ds`). -/
theorem normNum_leading (neg : Bool) (ds : List Nat) (z : Nat) (e : Int)
    (hc : CanonDigits ds) :
    normNum neg (0 :: (List.replicate z 0 ++ ds)) e = ⟨neg, ds, e⟩ := by
  have hz : ∀ x ∈ (0 :: List.replicate z 0), x = 0 := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h
    · exact List.eq_of_mem_replicate h
  have h1 : (0 :: (List.replicate z 0 ++ ds)).dropWhile (fun x => x == 0) = ds := by
    have := dropWhile_zeros (0 :: List.replicate z 0) ds hz hc.hd
    simpa using this
  unfold normNum
  simp only [h1, dropWhile_reverse_canon hc, List.reverse_reverse]
  have hne : ¬ (ds.isEmpty = true) := by simp [List.isEmpty_iff, hc.ne]
  simp only [hne, if_false]
  simp

/-- No-zeros shape (printer branches 2 and 4: the digits verbatim). -/
theorem normNum_exact (neg : Bool) (ds : List Nat) (e : Int) (hc : CanonDigits ds) :
    normNum neg ds e = ⟨neg, ds, e⟩ := by
  have := normNum_trailing neg ds 0 e hc
  simpa using this


/-! ## SafeTail — the precondition that makes the number round-trip TRUE

A JSON number has no terminator, so `scanNumber (renderNum n ++ rest) = some (n, rest)`
is FALSE for arbitrary `rest` (render `1`, append `2`, read back `12`). The exact
condition needed is that the first byte of `rest` cannot continue a number token: it is
not a digit, not `.`, not `e`/`E`. Every site where the serializer emits a number is
followed by `,`, `]`, `}` or end-of-input, all of which satisfy this. -/

def SafeTail (t : Bytes) : Prop :=
  ∀ c t', t = c :: t' →
    isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69

theorem safeTail_nil : SafeTail [] := by intro c t' h; exact absurd h (by simp)

theorem safeTail_struct {c : UInt8} {t : Bytes}
    (h : c.toNat = 44 ∨ c.toNat = 93 ∨ c.toNat = 125) : SafeTail (c :: t) := by
  intro c' t' he
  simp only [List.cons.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  unfold isDigitB
  rcases h with h | h | h <;> simp [h]

theorem safeTail_notDigit {t : Bytes} (h : SafeTail t) : NotDigitStart t := by
  intro c t' he; exact (h c t' he).1

/-! ## Scanning the pieces the printer emits -/

theorem natToDigits_ne_nil (n : Nat) : natToDigits n ≠ [] := by
  induction n using natToDigits.induct with
  | case1 n h => simp [natToDigits, h]
  | case2 n h _ => rw [natToDigits, dif_neg h]; simp

/-- Digit bytes never look like a sign. -/
theorem digitBytes_head_notSign {ds : List Nat} (hne : ds ≠ [])
    (hlt : ∀ d ∈ ds, d < 10) :
    ∀ c t, digitBytes ds = c :: t → c.toNat ≠ 43 ∧ c.toNat ≠ 45 := by
  intro c t he
  cases ds with
  | nil => exact absurd rfl hne
  | cons d ds' =>
    simp only [digitBytes, List.map_cons, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := toNat_digitByte (hlt d (by simp))
    omega

/-- `scanExpDigits` reads back exactly what `renderInt` wrote. -/
theorem scanExpDigits_renderInt (E : Int) {rest : Bytes} (hr : NotDigitStart rest) :
    scanExpDigits (renderInt E ++ rest) = some (E, rest) := by
  have hlt := natToDigits_lt10 E.natAbs
  have hne := natToDigits_ne_nil E.natAbs
  have hscan : scanDigits (digitBytes (natToDigits E.natAbs) ++ rest)
      = (natToDigits E.natAbs, rest) := scanDigits_digitBytes hlt hr
  have hof : ofDigits (natToDigits E.natAbs) = (E.natAbs : Int) := ofDigits_natToDigits _
  unfold renderInt
  by_cases hE : E < 0
  · rw [if_pos hE]
    simp only [List.cons_append, scanExpDigits]
    rw [if_neg (by decide), if_pos (by decide)]
    rw [hscan]
    simp only [List.isEmpty_iff, hne, if_neg, hof]
    have : -(E.natAbs : Int) = E := by omega
    simp [this]
  · rw [if_neg hE]
    cases hd : digitBytes (natToDigits E.natAbs) with
    | nil => exact absurd (by simpa [digitBytes] using hd) hne
    | cons c cs =>
      obtain ⟨h43, h45⟩ := digitBytes_head_notSign hne hlt c cs hd
      simp only [List.cons_append, scanExpDigits]
      rw [if_neg (by simp; omega), if_neg (by simp; omega)]
      rw [← List.cons_append, ← hd, hscan]
      simp only [List.isEmpty_iff, hne, if_neg, hof]
      have : (E.natAbs : Int) = E := by omega
      simp [this]

/-- `scanExp` reads back the `e`-part. -/
theorem scanExp_renderExp (E : Int) {rest : Bytes} (hr : NotDigitStart rest) :
    scanExp (101 :: (renderInt E ++ rest)) = (E, rest) := by
  simp only [scanExp]
  rw [if_pos (by decide), scanExpDigits_renderInt E hr]

/-- `scanFrac` on a tail that is not a `.`. -/
theorem scanFrac_notDot {t : Bytes} (h : SafeTail t) : scanFrac t = ([], t) := by
  cases t with
  | nil => simp [scanFrac]
  | cons c t' =>
    have := (h c t' rfl).2.1
    simp only [scanFrac]
    rw [if_neg (by simp; omega)]

/-- `scanExp` on a tail that is not an `e`/`E`. -/
theorem scanExp_notE {t : Bytes} (h : SafeTail t) : scanExp t = (0, t) := by
  cases t with
  | nil => simp [scanExp]
  | cons c t' =>
    obtain ⟨-, -, he, hE⟩ := h c t' rfl
    simp only [scanExp]
    rw [if_neg (by simp; omega)]


/-! ## scanNumber inverts renderNum -/

theorem digitBytes_append (a b : List Nat) :
    digitBytes (a ++ b) = digitBytes a ++ digitBytes b := by
  simp [digitBytes]

/-- "The next byte is not a `.`" — needed alongside `NotDigitStart` so that an EMPTY
    fractional part is read back as empty. `SafeTail` implies it; so does a leading `e`. -/
def NotDotStart (t : Bytes) : Prop := ∀ c t', t = c :: t' → c.toNat ≠ 46

theorem safeTail_notDot {t : Bytes} (h : SafeTail t) : NotDotStart t := by
  intro c t' he; exact (h c t' he).2.1

theorem notDigit_dotPart {F : List Nat} {t : Bytes} (ht : NotDigitStart t) :
    NotDigitStart (dotPart F ++ t) := by
  cases F with
  | nil => simpa [dotPart] using ht
  | cons f fs =>
    intro c t' he
    simp only [dotPart, List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    decide

theorem scanFrac_dotPart {F : List Nat} {t : Bytes}
    (hF : ∀ d ∈ F, d < 10) (hnd : NotDigitStart t) (hdot : NotDotStart t) :
    scanFrac (dotPart F ++ t) = (F, t) := by
  cases F with
  | nil =>
    cases t with
    | nil => simp [dotPart, scanFrac]
    | cons c t' =>
      have h46 := hdot c t' rfl
      simp only [dotPart, List.nil_append, scanFrac]
      rw [if_neg (by simp; omega)]
  | cons f fs =>
    simp only [dotPart, List.cons_append, scanFrac]
    rw [if_pos (by decide)]
    exact scanDigits_digitBytes hF hnd

theorem scanSign_render (neg : Bool) {I : List Nat} {t : Bytes}
    (hIne : I ≠ []) (hI : ∀ d ∈ I, d < 10) :
    scanSign (signBytes neg ++ digitBytes I ++ t) = (neg, digitBytes I ++ t) := by
  cases neg with
  | true =>
    have hsb : signBytes true = [45] := rfl
    rw [hsb]
    simp [scanSign]
  | false =>
    cases hd : digitBytes I with
    | nil => exact absurd (by simpa [digitBytes] using hd) hIne
    | cons c cs =>
      obtain ⟨-, h45⟩ := digitBytes_head_notSign hIne hI c cs hd
      have hne45 : ¬ ((c.toNat == 45) = true) := by simp; omega
      have hsb : signBytes false = [] := rfl
      rw [hsb, List.nil_append]
      simp only [List.cons_append, scanSign]
      rw [if_neg hne45]

/-- THE scanning lemma. One statement covers all four printer branches: the exponent
    branch instantiates `tl` with `'e' :: renderInt E ++ rest`, the other three with
    `rest` itself and `E = 0`. -/
theorem scanNumber_shape (neg : Bool) (I F : List Nat) (tl rest : Bytes) (E : Int)
    (hI : ∀ d ∈ I, d < 10) (hF : ∀ d ∈ F, d < 10) (hIne : I ≠ [])
    (hnd : NotDigitStart tl) (hdot : NotDotStart tl)
    (hexp : scanExp tl = (E, rest)) :
    scanNumber (signBytes neg ++ digitBytes I ++ dotPart F ++ tl)
      = some (normNum neg (I ++ F) (E - (F.length : Int)), rest) := by
  have hdp : NotDigitStart (dotPart F ++ tl) := notDigit_dotPart hnd
  have hsg := scanSign_render neg (I := I) (t := dotPart F ++ tl) hIne hI
  rw [List.append_assoc] at hsg
  have hsd : scanDigits (digitBytes I ++ (dotPart F ++ tl)) = (I, dotPart F ++ tl) :=
    scanDigits_digitBytes hI hdp
  have hsf : scanFrac (dotPart F ++ tl) = (F, tl) := scanFrac_dotPart hF hnd hdot
  have hIe : I.isEmpty = false := by simp [List.isEmpty_iff, hIne]
  simp only [scanNumber, List.append_assoc, hsg, hsd, hsf, hexp, hIe,
    Bool.false_and, Bool.false_eq_true, if_false]


/-! ## THE number round-trip -/

theorem normNum_zero (neg : Bool) : normNum neg [0] 0 = JNum.zero := by
  simp [normNum]

/-- The ARITHMETIC half: whichever branch `numParts` picks, the pieces it hands back
    re-normalise to exactly the number we started from, and satisfy the side conditions
    the scanning lemma needs. All four branches, no bytes in sight. -/
theorem numParts_spec (neg : Bool) (ds : List Nat) (exp : Int) (hcd : CanonDigits ds) :
    let p := numParts ds exp
    (p.1 ≠ [])
    ∧ (∀ x ∈ p.1, x < 10)
    ∧ (∀ x ∈ p.2.1, x < 10)
    ∧ normNum neg (p.1 ++ p.2.1) ((p.2.2.getD 0) - (p.2.1.length : Int))
        = ⟨neg, ds, exp⟩ := by
  have hne := hcd.ne
  have hlen : 0 < ds.length := List.length_pos_iff.mpr hne
  simp only [numParts]
  split
  · -- BRANCH 1: plain integer
    next hc1 =>
      obtain ⟨he0, -⟩ := hc1
      have hm : ((exp.toNat : Nat) : Int) = exp := Int.toNat_of_nonneg he0
      refine ⟨by simp [hne], ?_, by simp, ?_⟩
      · intro x hx
        rcases List.mem_append.mp hx with h | h
        · exact hcd.lt x h
        · rw [List.eq_of_mem_replicate h]; omega
      · dsimp only
        rw [List.append_nil, normNum_trailing neg ds exp.toNat _ hcd]
        simp only [JNum.mk.injEq, true_and, Option.getD_none, List.length_nil]
        omega
  · split
    · -- BRANCH 2: fixed point
      next hc2 =>
        obtain ⟨hlt0, hpos, -⟩ := hc2
        have hp : (((ds.length : Int) + exp).toNat : Int) = (ds.length : Int) + exp :=
          Int.toNat_of_nonneg (by omega)
        have hplt : ((ds.length : Int) + exp).toNat < ds.length := by omega
        have hpgt : 0 < ((ds.length : Int) + exp).toNat := by omega
        refine ⟨?_, fun x hx => hcd.lt x (List.mem_of_mem_take hx),
                   fun x hx => hcd.lt x (List.mem_of_mem_drop hx), ?_⟩
        · intro hcon
          have hl := congrArg List.length hcon
          simp only [List.length_take, List.length_nil] at hl
          omega
        · dsimp only
          rw [List.take_append_drop, normNum_exact neg ds _ hcd]
          simp only [JNum.mk.injEq, true_and, Option.getD_none, List.length_drop]
          omega
    · split
      · -- BRANCH 3: 0.000ddd
        next hc3 =>
          obtain ⟨hlt0, -, hle0⟩ := hc3
          have hz : ((-((ds.length : Int) + exp)).toNat : Int) = -((ds.length : Int) + exp) :=
            Int.toNat_of_nonneg (by omega)
          refine ⟨by simp, by intro x hx; simp at hx; omega, ?_, ?_⟩
          · intro x hx
            rcases List.mem_append.mp hx with h | h
            · rw [List.eq_of_mem_replicate h]; omega
            · exact hcd.lt x h
          · dsimp only
            rw [List.singleton_append,
                normNum_leading neg ds (-((ds.length : Int) + exp)).toNat _ hcd]
            simp only [JNum.mk.injEq, true_and, Option.getD_none, List.length_append,
              List.length_replicate]
            omega
      · -- BRANCH 4: scientific
        have hd1 : ds.take 1 ++ ds.drop 1 = ds := List.take_append_drop 1 ds
        refine ⟨?_, fun x hx => hcd.lt x (List.mem_of_mem_take hx),
                   fun x hx => hcd.lt x (List.mem_of_mem_drop hx), ?_⟩
        · intro hcon
          have hl := congrArg List.length hcon
          simp only [List.length_take, List.length_nil] at hl
          omega
        · dsimp only
          rw [hd1, normNum_exact neg ds _ hcd]
          simp only [JNum.mk.injEq, true_and, Option.getD_some, List.length_drop]
          omega

/-- **Number round-trip.** For every canonical `n` and every tail that cannot continue a
    number token, the scanner recovers `n` exactly and stops exactly where the printer
    stopped. A genuine normalisation statement, not a tautology: `100`, `1e2` and `1.0e2`
    all parse to the SAME node, which must print back to one canonical spelling. -/
-- @attested scanNumber_renderNum
theorem scanNumber_renderNum (n : JNum) (hc : JNum.Canonical n) (rest : Bytes)
    (hs : SafeTail rest) :
    scanNumber (renderNum n ++ rest) = some (n, rest) := by
  have hnd : NotDigitStart rest := safeTail_notDigit hs
  have hdot : NotDotStart rest := safeTail_notDot hs
  have hexp0 : scanExp rest = (0, rest) := scanExp_notE hs
  obtain ⟨neg, digits, exp⟩ := n
  cases hds : digits with
  | nil =>
    obtain ⟨-, hneg, hexp⟩ | ⟨hne, -, -, -⟩ := hc
    · simp only at hneg hexp
      subst hneg; subst hexp
      show scanNumber (renderNum ⟨false, [], 0⟩ ++ rest) = _
      have h48 : renderNum ⟨false, [], 0⟩
          = signBytes false ++ digitBytes [0] ++ dotPart [] := by decide
      rw [h48, scanNumber_shape false [0] [] rest rest 0
            (by intro x hx; simp at hx; omega) (by simp) (by simp) hnd hdot hexp0]
      simp [normNum_zero, JNum.zero]
    · exact absurd hds hne
  | cons d rds =>
    have hcd : CanonDigits (d :: rds) := by
      have := canon_of_JNum hc (by simp [hds])
      simpa [hds] using this
    obtain ⟨hIne, hI, hF, hnorm⟩ := numParts_spec neg (d :: rds) exp hcd
    show scanNumber (renderNum ⟨neg, d :: rds, exp⟩ ++ rest)
        = some (⟨neg, d :: rds, exp⟩, rest)
    simp only [renderNum]
    -- the exponent part: either absent, or 'e' followed by the rendered exponent
    cases hE : (numParts (d :: rds) exp).2.2 with
    | none =>
      simp only [expPart, List.append_nil]
      rw [scanNumber_shape neg _ _ rest rest 0 hI hF hIne hnd hdot hexp0]
      rw [show ((0 : Int) - ((numParts (d :: rds) exp).2.1.length : Int))
            = ((numParts (d :: rds) exp).2.2.getD 0)
              - ((numParts (d :: rds) exp).2.1.length : Int) by rw [hE]; simp]
      rw [hnorm]
    | some E =>
      have htl_nd : NotDigitStart (101 :: (renderInt E ++ rest)) := by
        intro c t' he
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        decide
      have htl_dot : NotDotStart (101 :: (renderInt E ++ rest)) := by
        intro c t' he
        simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he
        decide
      simp only [expPart, hE]
      rw [List.append_assoc (signBytes neg ++ digitBytes _ ++ dotPart _),
          List.cons_append,
          scanNumber_shape neg _ _ _ rest E hI hF hIne htl_nd htl_dot
            (scanExp_renderExp E hnd)]
      rw [show (E - ((numParts (d :: rds) exp).2.1.length : Int))
            = ((numParts (d :: rds) exp).2.2.getD 0)
              - ((numParts (d :: rds) exp).2.1.length : Int) by rw [hE]; simp]
      rw [hnorm]


end Cjson
