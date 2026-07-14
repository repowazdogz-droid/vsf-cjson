/-
  Phase 4b, part 3: the round-trip theorem for the whole AST.

      parseDoc (serialize v) = some v      for canonical v within the depth limit

  Note the two hypotheses. Both are real, and both are in the ledger:
    * `Canonical v` — the parser only ever BUILDS canonical numbers (T2), so this is not
      a restriction on parsing, only on which ASTs you may hand to `serialize` directly.
    * `d + jdepth v ≤ nestingLimit` — a value nested deeper than 1000 serializes fine but
      will NOT re-parse, because the parser enforces cJSON's depth limit. The round-trip
      genuinely fails past that depth, and the theorem says so rather than hiding it.
-/
import Cjson.Proofs.Num
import Cjson.Proofs.Str

namespace Cjson

/-! ## Plain-Option views of the parsers (the subtype is a nuisance in equations) -/

def pv (d : Nat) (s : Bytes) : Option (JSON × Bytes) := (parseValue d s).map Subtype.val
def pe (d : Nat) (s : Bytes) : Option (List JSON × Bytes) := (parseElems d s).map Subtype.val
def pm (d : Nat) (s : Bytes) : Option (List (Bytes × JSON) × Bytes) :=
  (parseMembers d s).map Subtype.val

/-! ## Serialized output never starts with whitespace -/

def NoLeadWs (s : Bytes) : Prop := ∀ c t, s = c :: t → isWs c = false

theorem skipWs_id {s : Bytes} (h : NoLeadWs s) : skipWs s = s := by
  cases s with
  | nil => rfl
  | cons c t =>
    have := h c t rfl
    simp only [skipWs]
    rw [if_neg (by simp [this])]

/-- The first byte of a rendered number is `-` or a digit. That is what gets it past the
    SPEC S2 dispatch gate — and it is also why it is never whitespace. -/
theorem renderNum_head (n : JNum) (hc : JNum.Canonical n) :
    ∀ c t, renderNum n = c :: t → (c.toNat = 45 ∨ isDigitB c = true) := by
  obtain ⟨neg, digits, exp⟩ := n
  cases hds : digits with
  | nil =>
    intro c t hct
    have : renderNum ⟨neg, [], exp⟩ = [48] := by simp [renderNum]
    rw [this] at hct
    simp only [List.cons.injEq] at hct
    obtain ⟨rfl, -⟩ := hct
    exact Or.inr (by decide)
  | cons d rds =>
    have hcd : CanonDigits (d :: rds) := by
      have := canon_of_JNum hc (by simp [hds])
      simpa [hds] using this
    obtain ⟨hIne, hI, -, -⟩ := numParts_spec neg (d :: rds) exp hcd
    intro c t hct
    show c.toNat = 45 ∨ isDigitB c = true
    rw [show renderNum ⟨neg, d :: rds, exp⟩
          = signBytes neg ++ digitBytes (numParts (d :: rds) exp).1
            ++ dotPart (numParts (d :: rds) exp).2.1
            ++ expPart (numParts (d :: rds) exp).2.2 from rfl] at hct
    cases hneg : neg with
    | true =>
      rw [hneg, show signBytes true = [45] from rfl] at hct
      simp only [List.cons_append, List.nil_append, List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      exact Or.inl (by decide)
    | false =>
      rw [hneg, show signBytes false = [] from rfl, List.nil_append] at hct
      cases hp : (numParts (d :: rds) exp).1 with
      | nil => exact absurd hp hIne
      | cons i is =>
        rw [hp] at hct
        simp only [digitBytes, List.map_cons, List.cons_append, List.cons.injEq] at hct
        obtain ⟨rfl, -⟩ := hct
        exact Or.inr (isDigitB_digitByte (hI i (by rw [hp]; simp)))

theorem renderNum_ne_nil (n : JNum) (hc : JNum.Canonical n) : renderNum n ≠ [] := by
  obtain ⟨neg, digits, exp⟩ := n
  cases hds : digits with
  | nil => simp [renderNum]
  | cons d rds =>
    have hcd : CanonDigits (d :: rds) := by
      have := canon_of_JNum hc (by simp [hds])
      simpa [hds] using this
    obtain ⟨hIne, -, -, -⟩ := numParts_spec neg (d :: rds) exp hcd
    show renderNum ⟨neg, d :: rds, exp⟩ ≠ []
    rw [show renderNum ⟨neg, d :: rds, exp⟩
          = signBytes neg ++ digitBytes (numParts (d :: rds) exp).1
            ++ dotPart (numParts (d :: rds) exp).2.1
            ++ expPart (numParts (d :: rds) exp).2.2 from rfl]
    cases hp : (numParts (d :: rds) exp).1 with
    | nil => exact absurd hp hIne
    | cons i is => simp [digitBytes, signBytes]


/-! ## The head byte of any serialized value -/

/-- The first byte of a serialized value is never whitespace, never `]` and never `}`.
    That is what lets `skipWs` be the identity on serializer output, and what stops an
    array's first element from being mistaken for the closing bracket. -/
def HeadOk (c : UInt8) : Prop := isWs c = false ∧ c ≠ 93 ∧ c ≠ 125 ∧ c ≠ 239

theorem serialize_head {v : JSON} (hc : JSON.Canonical v) :
    ∀ c t, serialize v = c :: t → HeadOk c := by
  intro c t hct
  cases v with
  | null => simp only [serialize, List.cons.injEq] at hct
            obtain ⟨rfl, -⟩ := hct; exact ⟨by decide, by decide, by decide, by decide⟩
  | bool b => cases b <;>
      (simp only [serialize, List.cons.injEq] at hct
       obtain ⟨rfl, -⟩ := hct; exact ⟨by decide, by decide, by decide, by decide⟩)
  | num n =>
    have hcn : JNum.Canonical n := by cases hc with | num _ h => exact h
    have := renderNum_head n hcn c t (by simpa [serialize] using hct)
    rcases this with h | h
    · exact ⟨by unfold isWs; simp; omega,
             by intro hcon; rw [hcon] at h; simp at h,
             by intro hcon; rw [hcon] at h; simp at h,
             by intro hcon; rw [hcon] at h; simp at h⟩
    · unfold isDigitB at h; simp at h
      exact ⟨by unfold isWs; simp; omega,
             by intro hcon; rw [hcon] at h; simp at h,
             by intro hcon; rw [hcon] at h; simp at h,
             by intro hcon; rw [hcon] at h; simp at h⟩
  | str s =>
    simp only [serialize, renderStr, List.cons.injEq] at hct
    obtain ⟨rfl, -⟩ := hct; exact ⟨by decide, by decide, by decide, by decide⟩
  | arr xs =>
    simp only [serialize, List.cons.injEq] at hct
    obtain ⟨rfl, -⟩ := hct; exact ⟨by decide, by decide, by decide, by decide⟩
  | obj kvs =>
    simp only [serialize, List.cons.injEq] at hct
    obtain ⟨rfl, -⟩ := hct; exact ⟨by decide, by decide, by decide, by decide⟩

theorem serialize_ne_nil {v : JSON} (hc : JSON.Canonical v) : serialize v ≠ [] := by
  cases v with
  | null => simp [serialize]
  | bool b => cases b <;> simp [serialize]
  | num n =>
    have hcn : JNum.Canonical n := by cases hc with | num _ h => exact h
    simpa [serialize] using renderNum_ne_nil n hcn
  | str s => simp [serialize, renderStr]
  | arr xs => simp [serialize]
  | obj kvs => simp [serialize]

/-- Serializer output followed by anything still has no leading whitespace. -/
theorem noLeadWs_serialize {v : JSON} (hc : JSON.Canonical v) (t : Bytes) :
    NoLeadWs (serialize v ++ t) := by
  intro c t' he
  cases hs : serialize v with
  | nil => exact absurd hs (serialize_ne_nil hc)
  | cons a as =>
    rw [hs, List.cons_append, List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact (serialize_head hc a as hs).1


/-! ## Equation lemmas for the plain-Option views

The parsers return a SUBTYPE carrying the consumed-a-byte proof, so a plain `cases` on
the scrutinee trips over the dependent motive. Instead each lemma `split`s the dependent
match and discharges the impossible branch using the ALREADY-KNOWN value of the scrutinee.
Subtype equality is proof-irrelevant, so the proof components never have to match. -/

theorem pv_str_known {d : Nat} {s rest X : Bytes} (h : parseStrBody X = some (s, rest)) :
    pv d (34 :: X) = some (JSON.str s, rest) := by
  unfold pv
  rw [parseValue]
  split
  · next hs => rw [h] at hs; exact absurd hs (by simp)
  · next v r' hs =>
      rw [h] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      rfl

theorem pv_num_known {d : Nat} {c : UInt8} {cs : Bytes} {n : JNum} {r : Bytes}
    (hg : c.toNat = 45 ∨ isDigitB c = true) (h : scanNumber (c :: cs) = some (n, r)) :
    pv d (c :: cs) = some (JSON.num n, r) := by
  -- The head byte is `-` or a digit: ELEVEN concrete literals. Making them literal is what
  -- lets `parseValue`'s match reduce definitionally, instead of fighting `split` over a
  -- variable head against eight literal patterns.
  have hn : c.toNat = 45 ∨ c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨ c.toNat = 51
          ∨ c.toNat = 52 ∨ c.toNat = 53 ∨ c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56
          ∨ c.toNat = 57 := by
    rcases hg with hx | hx
    · exact Or.inl hx
    · unfold isDigitB at hx
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hx
      omega
  have key : ∀ (k : UInt8), c.toNat = k.toNat → c = k := fun k hk => UInt8.toNat_inj.mp hk
  have hcases : c = 45 ∨ c = 48 ∨ c = 49 ∨ c = 50 ∨ c = 51 ∨ c = 52
              ∨ c = 53 ∨ c = 54 ∨ c = 55 ∨ c = 56 ∨ c = 57 := by
    rcases hn with h|h|h|h|h|h|h|h|h|h|h
    · exact Or.inl (key 45 (by rw [h]; rfl))
    · exact Or.inr (Or.inl (key 48 (by rw [h]; rfl)))
    · exact Or.inr (Or.inr (Or.inl (key 49 (by rw [h]; rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (key 50 (by rw [h]; rfl)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 51 (by rw [h]; rfl))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 52 (by rw [h]; rfl)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 53 (by rw [h]; rfl))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 54 (by rw [h]; rfl)))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 55 (by rw [h]; rfl))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (key 56 (by rw [h]; rfl)))))))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (key 57 (by rw [h]; rfl)))))))))))
  unfold pv
  rcases hcases with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (rw [parseValue]
     rw [if_pos (by decide)]
     split
     · next hn => rw [h] at hn; exact absurd hn (by simp)
     · next n' r' hn =>
         rw [h] at hn
         simp only [Option.some.injEq, Prod.mk.injEq] at hn
         obtain ⟨rfl, rfl⟩ := hn
         rfl
     all_goals (intros; simp_all))


theorem pv_arr_empty {d : Nat} {rest : Bytes} (hd : d < nestingLimit) :
    pv d (91 :: 93 :: rest) = some (JSON.arr [], rest) := by
  unfold pv
  rw [parseValue, dif_neg (by omega)]
  simp [skipWs, isWs]

theorem pv_obj_empty {d : Nat} {rest : Bytes} (hd : d < nestingLimit) :
    pv d (123 :: 125 :: rest) = some (JSON.obj [], rest) := by
  unfold pv
  rw [parseValue, dif_neg (by omega)]
  simp [skipWs, isWs]

/-- Note `skipWs` is kept in the STATEMENT rather than rewritten away inside the proof:
    the parser's match is dependent (the subtype carries a proof mentioning the scrutinee),
    so rewriting under it fails with "motive is not type correct". Pushing the rewrite out
    to the caller, where it is an ordinary hypothesis rewrite, sidesteps that entirely. -/
theorem pv_arr_cons {d : Nat} {c : UInt8} {t : Bytes} {xs : List JSON} {rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs (c :: t) = c :: t) (hc : c ≠ 93)
    (hpe : pe (d + 1) (skipWs (c :: t)) = some (xs, rest)) :
    pv d (91 :: (c :: t)) = some (JSON.arr xs, rest) := by
  unfold pv
  unfold pe at hpe
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw =>
      rw [hws] at hw
      simp only [List.cons.injEq] at hw
      exact absurd hw.1 hc
  · next hw =>
      split
      · next hn => rw [hn] at hpe; exact absurd hpe (by simp)
      · next p hn =>
          rw [hn] at hpe
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpe
          obtain ⟨rfl, rfl⟩ := hpe
          rfl

theorem pv_obj_cons {d : Nat} {c : UInt8} {t : Bytes} {kvs : List (Bytes × JSON)} {rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs (c :: t) = c :: t) (hc : c ≠ 125)
    (hpm : pm (d + 1) (skipWs (c :: t)) = some (kvs, rest)) :
    pv d (123 :: (c :: t)) = some (JSON.obj kvs, rest) := by
  unfold pv
  unfold pm at hpm
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw =>
      rw [hws] at hw
      simp only [List.cons.injEq] at hw
      exact absurd hw.1 hc
  · next hw =>
      split
      · next hn => rw [hn] at hpm; exact absurd hpm (by simp)
      · next p hn =>
          rw [hn] at hpm
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
          obtain ⟨rfl, rfl⟩ := hpm
          rfl


/-! ## Loop equations -/

theorem skipWs_struct {c : UInt8} {t : Bytes} (h : 32 < c.toNat) : skipWs (c :: t) = c :: t := by
  simp only [skipWs]
  rw [if_neg (by unfold isWs; simp; omega)]

@[simp] theorem skipWs_44 (t : Bytes) : skipWs (44 :: t) = 44 :: t := skipWs_struct (by decide)
@[simp] theorem skipWs_58 (t : Bytes) : skipWs (58 :: t) = 58 :: t := skipWs_struct (by decide)
@[simp] theorem skipWs_93 (t : Bytes) : skipWs (93 :: t) = 93 :: t := skipWs_struct (by decide)
@[simp] theorem skipWs_125 (t : Bytes) : skipWs (125 :: t) = 125 :: t := skipWs_struct (by decide)

theorem pe_last {d : Nat} {s : Bytes} {x : JSON} {rest : Bytes}
    (h : pv d s = some (x, 93 :: rest)) : pe d s = some ([x], rest) := by
  unfold pe; unfold pv at h
  rw [parseElems]
  split
  · next hn => rw [hn] at h; exact absurd h (by simp)
  · next v r hr hn =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split
      · next r2 hw => simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
                      simp only [List.cons.injEq] at hw
                      exact absurd hw.1 (by decide)
      · next r2 hw => simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
                      simp only [List.cons.injEq] at hw
                      obtain ⟨-, rfl⟩ := hw
                      rfl
      · next hw1 hw2 => exact (hw2 rest (skipWs_93 rest)).elim

theorem pe_cons {d : Nat} {s : Bytes} {x : JSON} {r2 : Bytes} {xs : List JSON} {rest : Bytes}
    (h : pv d s = some (x, 44 :: r2))
    (hrec : pe d (skipWs r2) = some (xs, rest)) : pe d s = some (x :: xs, rest) := by
  unfold pe at *; unfold pv at h
  rw [parseElems]
  split
  · next hn => rw [hn] at h; exact absurd h (by simp)
  · next v r hr hn =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split
      · next r3 hw =>
          simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
          simp only [List.cons.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          split
          · next hn2 => rw [hn2] at hrec; exact absurd hrec (by simp)
          · next p hn2 =>
              rw [hn2] at hrec
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
              obtain ⟨rfl, rfl⟩ := hrec
              rfl
      · next r3 hw =>
          simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
          simp only [List.cons.injEq] at hw
          exact absurd hw.1 (by decide)
      · next hw1 hw2 => exact (hw1 r2 (skipWs_44 r2)).elim

theorem pm_last {d : Nat} {rk k sv : Bytes} {v : JSON} {rest : Bytes}
    (hk : parseStrBody rk = some (k, 58 :: sv))
    (hv : pv d (skipWs sv) = some (v, 125 :: rest)) :
    pm d (34 :: rk) = some ([(k, v)], rest) := by
  unfold pm; unfold pv at hv
  rw [parseMembers]
  split
  · next hn => rw [hk] at hn; exact absurd hn (by simp)
  · next k' r1 hn =>
      rw [hk] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      split
      · next r2 hw =>
          simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
          simp only [List.cons.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          split
          · next hn2 => rw [hn2] at hv; exact absurd hv (by simp)
          · next v' r3 hr3 hn2 =>
              rw [hn2] at hv
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, rfl⟩ := hv
              split
              · next r4 hw2 =>
                  simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw2
                  simp only [List.cons.injEq] at hw2
                  exact absurd hw2.1 (by decide)
              · next r4 hw2 =>
                  simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw2
                  simp only [List.cons.injEq] at hw2
                  obtain ⟨-, rfl⟩ := hw2
                  rfl
              · next hx hw2 => exact (hw2 rest (skipWs_125 rest)).elim
      · next hw => exact (hw sv (skipWs_58 sv)).elim

theorem pm_cons {d : Nat} {rk k sv sr : Bytes} {v : JSON}
    {kvs : List (Bytes × JSON)} {rest : Bytes}
    (hk : parseStrBody rk = some (k, 58 :: sv))
    (hv : pv d (skipWs sv) = some (v, 44 :: sr))
    (hrec : pm d (skipWs sr) = some (kvs, rest)) :
    pm d (34 :: rk) = some ((k, v) :: kvs, rest) := by
  unfold pm at *; unfold pv at hv
  rw [parseMembers]
  split
  · next hn => rw [hk] at hn; exact absurd hn (by simp)
  · next k' r1 hn =>
      rw [hk] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      split
      · next r2 hw =>
          simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw
          simp only [List.cons.injEq] at hw
          obtain ⟨-, rfl⟩ := hw
          split
          · next hn2 => rw [hn2] at hv; exact absurd hv (by simp)
          · next v' r3 hr3 hn2 =>
              rw [hn2] at hv
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, rfl⟩ := hv
              split
              · next r4 hw2 =>
                  simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw2
                  simp only [List.cons.injEq] at hw2
                  obtain ⟨-, rfl⟩ := hw2
                  split
                  · next hn3 => rw [hn3] at hrec; exact absurd hrec (by simp)
                  · next p hn3 =>
                      rw [hn3] at hrec
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨rfl, rfl⟩ := hrec
                      rfl
              · next r4 hw2 =>
                  simp only [skipWs_44, skipWs_58, skipWs_93, skipWs_125] at hw2
                  simp only [List.cons.injEq] at hw2
                  exact absurd hw2.1 (by decide)
              · next hx hw2 => exact (hx sr (skipWs_44 sr)).elim
      · next hw => exact (hw sv (skipWs_58 sv)).elim


/-! ## Literal equations -/

theorem pv_null {d : Nat} {r : Bytes} : pv d (110 :: 117 :: 108 :: 108 :: r) = some (JSON.null, r) := by
  unfold pv; rw [parseValue]; rfl

theorem pv_true {d : Nat} {r : Bytes} : pv d (116 :: 114 :: 117 :: 101 :: r) = some (JSON.bool true, r) := by
  unfold pv; rw [parseValue]; rfl

theorem pv_false {d : Nat} {r : Bytes} :
    pv d (102 :: 97 :: 108 :: 115 :: 101 :: r) = some (JSON.bool false, r) := by
  unfold pv; rw [parseValue]; rfl

/-! ## Heads of serialized sequences -/

theorem serializeL_head {x : JSON} {xs : List JSON} (hc : JSON.Canonical x) :
    ∃ c t, serializeL (x :: xs) = c :: t ∧ HeadOk c := by
  cases hs : serialize x with
  | nil => exact absurd hs (serialize_ne_nil hc)
  | cons a as =>
    have hok := serialize_head hc a as hs
    cases xs with
    | nil => exact ⟨a, as, by show serialize x = a :: as; exact hs, hok⟩
    | cons y ys =>
      refine ⟨a, as ++ (44 :: serializeL (y :: ys)), ?_, hok⟩
      show serialize x ++ (44 :: serializeL (y :: ys)) = a :: (as ++ (44 :: serializeL (y :: ys)))
      rw [hs, List.cons_append]

theorem serializeKV_head {k : Bytes} {v : JSON} {kvs : List (Bytes × JSON)} :
    ∃ t, serializeKV ((k, v) :: kvs) = 34 :: t := by
  cases kvs with
  | nil => exact ⟨(k.flatMap escapeByte ++ [34]) ++ (58 :: serialize v), by
      show renderStr k ++ (58 :: serialize v) = _
      rw [renderStr, List.cons_append]⟩
  | cons kv kvs' =>
    obtain ⟨k', v'⟩ := kv
    exact ⟨(k.flatMap escapeByte ++ [34])
           ++ (58 :: (serialize v ++ (44 :: serializeKV ((k', v') :: kvs')))), by
      show renderStr k ++ (58 :: (serialize v ++ (44 :: serializeKV ((k', v') :: kvs')))) = _
      rw [renderStr, List.cons_append]⟩

/-! ## THE ROUND-TRIP THEOREM -/

-- @attested roundtrip_value
theorem roundtrip_value (v : JSON) :
    ∀ (d : Nat) (rest : Bytes), JSON.Canonical v → d + jdepth v ≤ nestingLimit →
      SafeTail rest → pv d (serialize v ++ rest) = some (v, rest) := by
  -- `induction ... with` cannot be used: the recursor's alternatives for `List JSON` and
  -- for `List (Bytes × JSON)` are BOTH named `nil`/`cons`, so named alternatives are
  -- ambiguous. Positional `refine` with ordered bullets is the way through.
  refine JSON.rec
    (motive_1 := fun v => ∀ (d : Nat) (rest : Bytes), JSON.Canonical v →
        d + jdepth v ≤ nestingLimit → SafeTail rest →
        pv d (serialize v ++ rest) = some (v, rest))
    (motive_2 := fun xs => ∀ (d : Nat) (rest : Bytes), xs ≠ [] → JSON.CanonicalL xs →
        d + jdepthL xs ≤ nestingLimit → SafeTail rest →
        pe d (serializeL xs ++ (93 :: rest)) = some (xs, rest))
    (motive_3 := fun kvs => ∀ (d : Nat) (rest : Bytes), kvs ≠ [] → JSON.CanonicalKV kvs →
        d + jdepthKV kvs ≤ nestingLimit → SafeTail rest →
        pm d (serializeKV kvs ++ (125 :: rest)) = some (kvs, rest))
    (motive_4 := fun kv => ∀ (d : Nat) (rest : Bytes), JSON.Canonical kv.2 →
        d + jdepth kv.2 ≤ nestingLimit → SafeTail rest →
        pv d (serialize kv.2 ++ rest) = some (kv.2, rest))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ v
  -- 1. null
  · intro d rest _ _ _; exact pv_null
  -- 2. bool
  · intro b; cases b <;> (intro d rest _ _ _; first | exact pv_true | exact pv_false)
  -- 3. num
  · intro n d rest hc _ hs
    have hcn : JNum.Canonical n := by cases hc with | num _ h => exact h
    have hsn : scanNumber (renderNum n ++ rest) = some (n, rest) :=
      scanNumber_renderNum n hcn rest hs
    cases hr : renderNum n with
    | nil => exact absurd hr (renderNum_ne_nil n hcn)
    | cons c t =>
      have hgate := renderNum_head n hcn c t hr
      rw [hr] at hsn
      show pv d (renderNum n ++ rest) = _
      rw [hr, List.cons_append]
      exact pv_num_known hgate hsn
  -- 4. str
  · intro s d rest _ _ _
    show pv d ((34 :: (s.flatMap escapeByte ++ [34])) ++ rest) = _
    rw [List.cons_append, List.append_assoc, List.singleton_append]
    exact pv_str_known (parseStrBody_renderStr s rest)
  -- 5. arr
  · intro xs ih d rest hc hd hs
    have hcl : JSON.CanonicalL xs := by cases hc with | arr _ h => exact h
    have hdd : d < nestingLimit := by simp only [jdepth] at hd; omega
    have hdl : (d + 1) + jdepthL xs ≤ nestingLimit := by simp only [jdepth] at hd; omega
    show pv d ((91 :: (serializeL xs ++ [93])) ++ rest) = _
    rw [List.cons_append, List.append_assoc, List.singleton_append]
    cases hxs : xs with
    | nil => exact pv_arr_empty hdd
    | cons x xs' =>
      have hcx : JSON.Canonical x := by
        rw [hxs] at hcl; cases hcl with | cons _ _ h _ => exact h
      obtain ⟨c, t, hct, hok⟩ := serializeL_head (x := x) (xs := xs') hcx
      have hpe : pe (d + 1) (serializeL (x :: xs') ++ (93 :: rest)) = some (x :: xs', rest) := by
        subst hxs; exact ih (d + 1) rest (by simp) hcl hdl hs
      have hws : skipWs (c :: (t ++ (93 :: rest))) = c :: (t ++ (93 :: rest)) := by
        apply skipWs_id
        intro c' t' he; simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he; exact hok.1
      rw [hct, List.cons_append] at hpe
      rw [hct, List.cons_append]
      exact pv_arr_cons hdd hws hok.2.1 (by rw [hws]; exact hpe)
  -- 6. obj
  · intro kvs ih d rest hc hd hs
    have hck : JSON.CanonicalKV kvs := by cases hc with | obj _ h => exact h
    have hdd : d < nestingLimit := by simp only [jdepth] at hd; omega
    have hdl : (d + 1) + jdepthKV kvs ≤ nestingLimit := by simp only [jdepth] at hd; omega
    show pv d ((123 :: (serializeKV kvs ++ [125])) ++ rest) = _
    rw [List.cons_append, List.append_assoc, List.singleton_append]
    cases hkvs : kvs with
    | nil => exact pv_obj_empty hdd
    | cons kv kvs' =>
      obtain ⟨k, v⟩ := kv
      obtain ⟨t, hct⟩ := serializeKV_head (k := k) (v := v) (kvs := kvs')
      have hpm : pm (d + 1) (serializeKV ((k, v) :: kvs') ++ (125 :: rest))
          = some ((k, v) :: kvs', rest) := by
        subst hkvs; exact ih (d + 1) rest (by simp) hck hdl hs
      rw [hct, List.cons_append] at hpm
      rw [hct, List.cons_append]
      exact pv_obj_cons hdd (skipWs_struct (by decide)) (by decide)
        (by rw [skipWs_struct (by decide)]; exact hpm)
  -- 7. motive_2 nil (vacuous: the empty element list is never serialized on its own)
  · intro d rest hne _ _ _; exact absurd rfl hne
  -- 8. motive_2 cons
  · intro x xs ihx ihxs d rest _ hcl hdl hs
    have hcx : JSON.Canonical x := by cases hcl with | cons _ _ h _ => exact h
    have hcxs : JSON.CanonicalL xs := by cases hcl with | cons _ _ _ h => exact h
    have hdx : d + jdepth x ≤ nestingLimit := by simp only [jdepthL] at hdl; omega
    have hdxs : d + jdepthL xs ≤ nestingLimit := by simp only [jdepthL] at hdl; omega
    cases hxs : xs with
    | nil =>
      have hv := ihx d (93 :: rest) hcx hdx (safeTail_struct (by decide))
      show pe d (serialize x ++ (93 :: rest)) = _
      exact pe_last hv
    | cons y ys =>
      have hcy : JSON.Canonical y := by
        rw [hxs] at hcxs; cases hcxs with | cons _ _ h _ => exact h
      have hv := ihx d (44 :: (serializeL (y :: ys) ++ (93 :: rest))) hcx hdx
        (safeTail_struct (by decide))
      have hrec : pe d (serializeL (y :: ys) ++ (93 :: rest)) = some (y :: ys, rest) := by
        subst hxs; exact ihxs d rest (by simp) hcxs hdxs hs
      obtain ⟨c, t, hct, hok⟩ := serializeL_head (x := y) (xs := ys) hcy
      have hws : skipWs (serializeL (y :: ys) ++ (93 :: rest))
          = serializeL (y :: ys) ++ (93 :: rest) := by
        apply skipWs_id
        rw [hct, List.cons_append]
        intro c' t' he; simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he; exact hok.1
      show pe d ((serialize x ++ (44 :: serializeL (y :: ys))) ++ (93 :: rest)) = _
      rw [List.append_assoc, List.cons_append]
      exact pe_cons hv (by rw [hws]; exact hrec)
  -- 9. motive_3 nil (vacuous)
  · intro d rest hne _ _ _; exact absurd rfl hne
  -- 10. motive_3 cons
  · intro kv kvs ihkv ihkvs d rest _ hck hdl hs
    obtain ⟨k, v⟩ := kv
    have hcv : JSON.Canonical v := by cases hck with | cons _ _ _ h _ => exact h
    have hckvs : JSON.CanonicalKV kvs := by cases hck with | cons _ _ _ _ h => exact h
    have hdv : d + jdepth v ≤ nestingLimit := by simp only [jdepthKV] at hdl; omega
    have hdkvs : d + jdepthKV kvs ≤ nestingLimit := by simp only [jdepthKV] at hdl; omega
    cases hkvs : kvs with
    | nil =>
      have hv := ihkv d (125 :: rest) hcv hdv (safeTail_struct (by decide))
      show pm d ((renderStr k ++ (58 :: serialize v)) ++ (125 :: rest)) = _
      simp only [renderStr, List.cons_append, List.append_assoc, List.singleton_append]
      exact pm_last (parseStrBody_renderStr k _)
        (by rw [skipWs_id (noLeadWs_serialize hcv _)]; exact hv)
    | cons kv2 kvs2 =>
      obtain ⟨k2, v2⟩ := kv2
      have hv := ihkv d (44 :: (serializeKV ((k2, v2) :: kvs2) ++ (125 :: rest))) hcv hdv
        (safeTail_struct (by decide))
      have hrec : pm d (serializeKV ((k2, v2) :: kvs2) ++ (125 :: rest))
          = some ((k2, v2) :: kvs2, rest) := by
        subst hkvs; exact ihkvs d rest (by simp) hckvs hdkvs hs
      obtain ⟨t, hct⟩ := serializeKV_head (k := k2) (v := v2) (kvs := kvs2)
      have hws : skipWs (serializeKV ((k2, v2) :: kvs2) ++ (125 :: rest))
          = serializeKV ((k2, v2) :: kvs2) ++ (125 :: rest) := by
        apply skipWs_id
        rw [hct, List.cons_append]
        intro c' t' he; simp only [List.cons.injEq] at he
        obtain ⟨rfl, -⟩ := he; decide
      show pm d ((renderStr k
            ++ (58 :: (serialize v ++ (44 :: serializeKV ((k2, v2) :: kvs2)))))
            ++ (125 :: rest)) = _
      simp only [renderStr, List.cons_append, List.append_assoc, List.singleton_append]
      refine pm_cons (parseStrBody_renderStr k _) ?_ (by rw [hws]; exact hrec)
      rw [skipWs_id (noLeadWs_serialize hcv _)]
      exact hv
  -- 11. motive_4 mk
  · intro k v ih d rest hc hd hs; exact ih d rest hc hd hs


/-! ## Document level -/

theorem skipBom_serialize {v : JSON} (hc : JSON.Canonical v) :
    skipBom (serialize v) = serialize v := by
  unfold skipBom
  split
  · next r he =>
      cases hs : serialize v with
      | nil => exact absurd hs (serialize_ne_nil hc)
      | cons a as =>
        rw [hs] at he
        simp only [List.cons.injEq] at he
        exact absurd he.1 (serialize_head hc a as hs).2.2.2
  · rfl

theorem noLeadWs_serialize' {v : JSON} (hc : JSON.Canonical v) : NoLeadWs (serialize v) := by
  intro c t he
  cases hs : serialize v with
  | nil => exact absurd hs (serialize_ne_nil hc)
  | cons a as =>
    rw [hs] at he
    simp only [List.cons.injEq] at he
    obtain ⟨rfl, -⟩ := he
    exact (serialize_head hc a as hs).1

theorem pv_congr {d : Nat} {s t : Bytes} (h : s = t) : pv d s = pv d t := by
  subst h; rfl

/-- `parseDoc` in terms of `pv`. Stated separately because `parseValue`'s RETURN TYPE
    depends on its argument (`Res JSON s`), so rewriting the argument inside `parseDoc`
    fails with "motive is not type correct". Going through this equation and `pv_congr`
    keeps every rewrite at the non-dependent `Option (JSON × Bytes)` level. -/
theorem parseDoc_eq (s : Bytes) :
    parseDoc s = (pv 0 (skipWs (skipBom s))).map Prod.fst := by
  unfold parseDoc pv
  split
  · next hn => rw [hn]; rfl
  · next p hn => rw [hn]; rfl

/-- **T1 — ROUND-TRIP.** `parse (serialize v) = v` for every canonical value within the
    depth limit. Both hypotheses are real and both are in the LEDGER:
      * `Canonical v` is discharged for anything the parser produced (T2);
      * the depth bound is NOT removable — a value nested deeper than 1000 serializes
        fine but does not re-parse, because the parser enforces cJSON's limit. -/
-- @attested parseDoc_serialize
theorem parseDoc_serialize (v : JSON) (hc : JSON.Canonical v)
    (hd : jdepth v ≤ nestingLimit) : parseDoc (serialize v) = some v := by
  have h := roundtrip_value v 0 [] hc (by omega) safeTail_nil
  rw [List.append_nil] at h
  have hbom : skipWs (skipBom (serialize v)) = serialize v := by
    rw [skipBom_serialize hc]
    exact skipWs_id (noLeadWs_serialize' hc)
  rw [parseDoc_eq, pv_congr hbom, h]
  rfl


/-! ## T3 — the headline theorem (GAP-1 CLOSED)

`parseDoc s = some v → parseDoc (serialize v) = some v`

Both hypotheses of T1 are now DISCHARGED, not assumed:
  * `Canonical v`            from `parseDoc_canonical` (the parser's return type carries it);
  * `jdepth v ≤ nestingLimit` from `parseDoc_depth`    (likewise).

So T3 is unconditional: anything this parser produces re-parses to itself. -/

-- @attested parseDoc_depth
theorem parseDoc_depth {s : Bytes} {v : JSON} (h : parseDoc s = some v) :
    jdepth v ≤ nestingLimit := by
  unfold parseDoc at h
  split at h
  · exact absurd h (by simp)
  · next v' r' hp hn =>
      simp only [Option.some.injEq] at h
      subst h
      have := hp.2.2
      omega

/-- **T3.** Anything the parser produces re-parses to itself. Unconditional. -/
-- @attested parseDoc_idempotent
theorem parseDoc_idempotent {s : Bytes} {v : JSON} (h : parseDoc s = some v) :
    parseDoc (serialize v) = some v :=
  parseDoc_serialize v (parseDoc_canonical h) (parseDoc_depth h)

end Cjson
