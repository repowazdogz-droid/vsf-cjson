/-
  GAP-2, step 3 — STRING SOUNDNESS.

      parseStrBody s = some (v, r)  →  ∃ p, s = p ++ (34 :: r) ∧ SChars p v

  The bytes the parser consumed (excluding the closing quote) form a string body that the
  grammar decodes to exactly `v`.

  Zero `sorry`, zero axioms.
-/
import Cjson.Spec.NumSound
-- for `parseStrBody_other`, an existing equation lemma about the RELEASED parser (v1.0.1)
import Cjson.Proofs.Str

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



/-! ## String-body soundness

    ARCHITECTURE 1 (allowed list): a specialised induction on the INPUT LENGTH, plus the
    branch equations that already exist for the released parser. We do NOT use
    `parseStrBody.induct` (31 minor premises), we do NOT change `parseStrBody`, and we
    introduce NO new definition — so the parser/specification boundary is untouched by
    construction. See INDEPENDENCE_RISK.md §Risk 3. -/

/-- The escape branches, as equations on the EXISTING parser. Each is definitional. -/
theorem psb_esc34 (r : Bytes) : parseStrBody (92 :: 34 :: r)
    = match parseStrBody r with | some (v, r') => some (34 :: v, r') | none => none := rfl
theorem psb_esc92 (r : Bytes) : parseStrBody (92 :: 92 :: r)
    = match parseStrBody r with | some (v, r') => some (92 :: v, r') | none => none := rfl
theorem psb_esc47 (r : Bytes) : parseStrBody (92 :: 47 :: r)
    = match parseStrBody r with | some (v, r') => some (47 :: v, r') | none => none := rfl
theorem psb_esc98 (r : Bytes) : parseStrBody (92 :: 98 :: r)
    = match parseStrBody r with | some (v, r') => some (8 :: v, r') | none => none := rfl
theorem psb_esc102 (r : Bytes) : parseStrBody (92 :: 102 :: r)
    = match parseStrBody r with | some (v, r') => some (12 :: v, r') | none => none := rfl
theorem psb_esc110 (r : Bytes) : parseStrBody (92 :: 110 :: r)
    = match parseStrBody r with | some (v, r') => some (10 :: v, r') | none => none := rfl
theorem psb_esc114 (r : Bytes) : parseStrBody (92 :: 114 :: r)
    = match parseStrBody r with | some (v, r') => some (13 :: v, r') | none => none := rfl
theorem psb_esc116 (r : Bytes) : parseStrBody (92 :: 116 :: r)
    = match parseStrBody r with | some (v, r') => some (9 :: v, r') | none => none := rfl

/-- Generic escape lemma: collapses the seven-plus-one repeated cases into one. -/
theorem psb_esc {c d : UInt8} {t : Bytes} {v r : Bytes}
    (hcd : (c = 34 ∧ d = 34) ∨ (c = 92 ∧ d = 92) ∨ (c = 47 ∧ d = 47) ∨
           (c = 98 ∧ d = 8) ∨ (c = 102 ∧ d = 12) ∨ (c = 110 ∧ d = 10) ∨
           (c = 114 ∧ d = 13) ∨ (c = 116 ∧ d = 9))
    (h : parseStrBody (92 :: c :: t) = some (v, r)) :
    ∃ v', parseStrBody t = some (v', r) ∧ v = d :: v' := by
  have key : parseStrBody (92 :: c :: t)
      = match parseStrBody t with | some (w, r') => some (d :: w, r') | none => none := by
    rcases hcd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
             | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact psb_esc34 t
    · exact psb_esc92 t
    · exact psb_esc47 t
    · exact psb_esc98 t
    · exact psb_esc102 t
    · exact psb_esc110 t
    · exact psb_esc114 t
    · exact psb_esc116 t
  rw [key] at h
  cases hp : parseStrBody t with
  | none => rw [hp] at h; simp at h
  | some p =>
    obtain ⟨w, r'⟩ := p
    rw [hp] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨hv, hr⟩ := h
    subst hr
    exact ⟨w, rfl, hv.symm⟩

/-- A backslash followed by a byte that is neither a simple escape nor `u` is rejected. -/
theorem psb_bad_esc {d : UInt8} {t : Bytes}
    (hs : ¬ (d = 34 ∨ d = 92 ∨ d = 47 ∨ d = 98 ∨ d = 102 ∨ d = 110 ∨ d = 114 ∨ d = 116))
    (hu : d ≠ 117) : parseStrBody (92 :: d :: t) = none := by
  have h1 : d ≠ 34 := fun hc => hs (by simp [hc])
  have h2 : d ≠ 92 := fun hc => hs (by simp [hc])
  have h3 : d ≠ 47 := fun hc => hs (by simp [hc])
  have h4 : d ≠ 98 := fun hc => hs (by simp [hc])
  have h5 : d ≠ 102 := fun hc => hs (by simp [hc])
  have h6 : d ≠ 110 := fun hc => hs (by simp [hc])
  have h7 : d ≠ 114 := fun hc => hs (by simp [hc])
  have h8 : d ≠ 116 := fun hc => hs (by simp [hc])
  clear hs
  rw [parseStrBody.eq_def]
  split
  case h_14 =>
    -- the catch-all is UNREACHABLE for a `92`-headed input: `92 :: _ :: _` precedes it
    exfalso
    rename_i hbad hnil heq
    simp only [List.cons.injEq] at heq
    obtain ⟨h92, hr⟩ := heq
    exact hbad d t h92.symm hr.symm
  all_goals simp_all

/-- **STRING-BODY SOUNDNESS.**

    Does NOT establish: completeness (that every grammatical body is accepted — C4); maximal
    munch (C3); anything about UTF-8 validity (the grammar, like the parser, passes bytes
    ≥ 0x80 through unexamined, SPEC §S1.3); and nothing about the surrounding quotes, which
    `parseValue` handles. -/
theorem parseStrBody_sound : ∀ (n : Nat) (s : Bytes) (v r : Bytes), s.length ≤ n →
    parseStrBody s = some (v, r) → ∃ p, s = p ++ (34 :: r) ∧ SChars p v := by
  intro n
  induction n with
  | zero =>
    intro s v r hlen h
    have : s = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this
    simp [parseStrBody] at h
  | succ n ih =>
    intro s v r hlen h
    cases s with
    | nil => simp [parseStrBody] at h
    | cons c t =>
      by_cases h34 : c = 34
      · -- closing quote
        subst h34
        rw [show parseStrBody (34 :: t) = some ([], t) from rfl] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨[], rfl, SChars.nil⟩
      by_cases h92 : c = 92
      · -- an escape
        subst h92
        cases t with
        | nil => rw [show parseStrBody [92] = none from rfl] at h; simp at h
        | cons d t' =>
          -- is it one of the eight simple escapes?
          by_cases hsimp : (d = 34 ∨ d = 92 ∨ d = 47 ∨ d = 98 ∨ d = 102 ∨ d = 110
                            ∨ d = 114 ∨ d = 116)
          · have hcd : (d = 34 ∧ (34:UInt8) = 34) ∨ (d = 92 ∧ (92:UInt8) = 92)
                     ∨ (d = 47 ∧ (47:UInt8) = 47) ∨ (d = 98 ∧ (8:UInt8) = 8)
                     ∨ (d = 102 ∧ (12:UInt8) = 12) ∨ (d = 110 ∧ (10:UInt8) = 10)
                     ∨ (d = 114 ∧ (13:UInt8) = 13) ∨ (d = 116 ∧ (9:UInt8) = 9) := by
              rcases hsimp with h|h|h|h|h|h|h|h <;> simp [h]
            -- pick the decoded byte
            obtain ⟨dd, hdd⟩ : ∃ dd : UInt8,
                ((d = 34 ∧ dd = 34) ∨ (d = 92 ∧ dd = 92) ∨ (d = 47 ∧ dd = 47) ∨
                 (d = 98 ∧ dd = 8) ∨ (d = 102 ∧ dd = 12) ∨ (d = 110 ∧ dd = 10) ∨
                 (d = 114 ∧ dd = 13) ∨ (d = 116 ∧ dd = 9)) := by
              rcases hsimp with h|h|h|h|h|h|h|h
              · exact ⟨34, by simp [h]⟩
              · exact ⟨92, by simp [h]⟩
              · exact ⟨47, by simp [h]⟩
              · exact ⟨8, by simp [h]⟩
              · exact ⟨12, by simp [h]⟩
              · exact ⟨10, by simp [h]⟩
              · exact ⟨13, by simp [h]⟩
              · exact ⟨9, by simp [h]⟩
            obtain ⟨v', hv', rfl⟩ := psb_esc hdd h
            have hlen' : t'.length ≤ n := by simp at hlen; omega
            obtain ⟨p, hp, hc⟩ := ih t' v' r hlen' hv'
            exact ⟨92 :: d :: p, by simp [hp], SChars.esc hc hdd⟩
          · -- must be \u, otherwise the parser rejects
            by_cases hu : d = 117
            · subst hu
              -- need four more bytes
              cases t' with
              | nil => rw [show parseStrBody [92, 117] = none from rfl] at h; simp at h
              | cons a t1 =>
              cases t1 with
              | nil => rw [show parseStrBody [92, 117, a] = none from rfl] at h; simp at h
              | cons b t2 =>
              cases t2 with
              | nil => rw [show parseStrBody [92, 117, a, b] = none from rfl] at h; simp at h
              | cons cc t3 =>
              cases t3 with
              | nil => rw [show parseStrBody [92, 117, a, b, cc] = none from rfl] at h
                       simp at h
              | cons dd t4 =>
                -- the \uXXXX arm
                rw [parseStrBody] at h
                split at h
                · simp at h                                   -- hex4 failed: parser rejects
                · next cp hx =>
                  obtain ⟨ia, ib, ic, id, hcp⟩ := hex4_isHex hx
                  split at h
                  · simp at h                                 -- lone low surrogate: rejects
                  · next hlo =>
                    split at h
                    · next hhi =>
                      -- HIGH surrogate: the parser demands a well-formed low half
                      split at h
                      · next g1 g2 g3 g4 r2 =>
                        split at h
                        · simp at h                           -- second hex4 failed
                        · next cp2 hy =>
                          obtain ⟨ja, jb, jc, jd, hcp2⟩ := hex4_isHex hy
                          split at h
                          · next hlo2 =>
                            split at h
                            · next w r' hrec =>
                              simp only [Option.some.injEq, Prod.mk.injEq] at h
                              obtain ⟨hv, hr⟩ := h
                              subst hr
                              have hlen' : r2.length ≤ n := by
                                simp only [List.length_cons] at hlen
                                omega
                              obtain ⟨p, hp, hc⟩ := ih r2 w r' hlen' hrec
                              refine ⟨92 :: 117 :: a :: b :: cc :: dd ::
                                      92 :: 117 :: g1 :: g2 :: g3 :: g4 :: p, by simp [hp], ?_⟩
                              have hpair := SChars.pair (p := p) (out := w)
                                        ia ib ic id ja jb jc jd
                                        (by rw [← hcp]; exact isHigh_range hhi)
                                        (by rw [← hcp2]; exact isLow_range hlo2) hc
                              rw [← hv, hcp, hcp2, ← enc_eq]
                              exact hpair
                            · simp at h                       -- recursive parse failed
                          · simp at h                         -- not a low surrogate: rejects
                      · simp at h                             -- no `\uXXXX` after the high half
                    · next hhi =>
                      -- plain \uXXXX (not a surrogate half)
                      split at h
                      · next w r' hrec =>
                        simp only [Option.some.injEq, Prod.mk.injEq] at h
                        obtain ⟨hv, hr⟩ := h
                        subst hr
                        have hlen' : t4.length ≤ n := by
                          simp only [List.length_cons] at hlen; omega
                        obtain ⟨p, hp, hc⟩ := ih t4 w r' hlen' hrec
                        refine ⟨92 :: 117 :: a :: b :: cc :: dd :: p, by simp [hp], ?_⟩
                        have huni := SChars.uni (p := p) (out := w) ia ib ic id
                                  (by rw [← hcp]
                                      exact not_surrogate (by simpa using hlo) (by simpa using hhi))
                                  hc
                        rw [← hv, hcp, ← enc_eq]
                        exact huni
                      · simp at h                             -- recursive parse failed
            · -- backslash followed by something else: the parser rejects
              exfalso
              rw [psb_bad_esc hsimp hu] at h
              simp at h
      · -- an ordinary byte
        rw [parseStrBody_other h34 h92] at h
        cases hrec : parseStrBody t with
        | none => rw [hrec] at h; simp at h
        | some q =>
          obtain ⟨w, r'⟩ := q
          rw [hrec] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hv, hr⟩ := h
          subst hr
          have hlen' : t.length ≤ n := by simp at hlen; omega
          obtain ⟨p, hp, hc⟩ := ih t w r' hlen' hrec
          exact ⟨c :: p, by simp [hp], by rw [← hv]; exact SChars.plain ⟨h34, h92⟩ hc⟩

/-- The form actually needed downstream. -/
theorem parseStrBody_sound' {s : Bytes} {v r : Bytes} (h : parseStrBody s = some (v, r)) :
    ∃ p, s = p ++ (34 :: r) ∧ SChars p v :=
  parseStrBody_sound s.length s v r (Nat.le_refl _) h

end Cjson.Spec
