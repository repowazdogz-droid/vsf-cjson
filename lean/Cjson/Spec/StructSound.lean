/-
  GAP-2, step 4 — STRUCTURAL SOUNDNESS for values, arrays and objects, then C2.

  Statements are phrased on the plain-Option views `pv`/`pe`/`pm` (from the released
  `Cjson.Proofs.RoundTrip`), which strip the parser's result subtype. No new definition of a
  parser or a grammar is introduced; nothing carries a grammar witness. See
  INDEPENDENCE_RISK.md §Risk 3/4.

  Induction architecture (confirmed against the real code, ADEQUACY_REPORT §"proof shape"):
  the ONLY same-length recursive call is `parseElems → parseValue`; every other call is on a
  strictly shorter input. So a single `Nat.rec` on a length bound, with STAGING inside the
  successor step:
      1. establish value soundness at n+1              (uses IH's elem/member soundness at ≤ n)
      2. establish element soundness at n+1            (uses (1), plus IH's elem soundness at ≤ n)
      3. establish member soundness at n+1             (uses IH's value/member soundness at ≤ n)
  The strict decrease at a value is recovered from the grammar itself (`SValue_ne_nil`), not
  from the parser's stripped subtype.

  Zero `sorry`, zero custom axioms.
-/
import Cjson.Proofs.RoundTrip
import Cjson.Spec.StrSound

namespace Cjson.Spec

open Cjson

/-! ## Whitespace bridge -/

/-- The parser's boolean `isWs` implies the grammar's `IsWs`. -/
theorem isWs_IsWs {c : UInt8} (h : isWs c = true) : IsWs c := by
  unfold isWs at h; unfold IsWs; simpa using h

/-- `skipWs` drops a whitespace prefix. The load-bearing whitespace fact the grammar needs:
    the bytes `skipWs` removed form a `Ws` block. -/
theorem skipWs_split (s : Bytes) : ∃ w, s = w ++ skipWs s ∧ Ws w := by
  induction s with
  | nil => exact ⟨[], rfl, by intro c hc; simp at hc⟩
  | cons c cs ih =>
    by_cases h : isWs c
    · obtain ⟨w, hw, hws⟩ := ih
      refine ⟨c :: w, ?_, ?_⟩
      · show c :: cs = (c :: w) ++ skipWs (c :: cs)
        rw [skipWs, if_pos h, List.cons_append, ← hw]
      · intro x hx; rcases List.mem_cons.mp hx with rfl | hm
        · exact isWs_IsWs h
        · exact hws x hm
    · exact ⟨[], by simp only [skipWs, if_neg h]; rfl, by intro c hc; simp at hc⟩

/-! ## Every value consumes at least one byte

    This is how the strict decrease is recovered from the grammar rather than from the parser's
    (stripped) subtype proof. -/

theorem SStr_ne_nil {p out : Bytes} (h : SStr p out) : p ≠ [] := by
  obtain ⟨body, hp, _⟩ := h; rw [hp]; simp

theorem SValue_ne_nil {p : Bytes} {v : JSON} (h : SValue p v) : p ≠ [] := by
  cases h with
  | str hs => exact SStr_ne_nil hs
  | _ => simp

/-! ## Dispatch-gate bridge -/

theorem gate_of {c : UInt8} (h : (c.toNat == 45 || isDigitB c) = true) :
    c = 45 ∨ isDigitB c = true := by
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with h | h
  · exact Or.inl (UInt8.toNat_inj.mp (by rw [h]; rfl))
  · exact Or.inr h

/-! ## Value soundness (the `hV` stage), parameterised by the IH's elem/member soundness -/

/-- The soundness predicates, over a length bound. -/
def PVsound (n : Nat) : Prop := ∀ (d : Nat) (s : Bytes) (v : JSON) (r : Bytes),
  s.length ≤ n → pv d s = some (v, r) → ∃ p, s = p ++ r ∧ SValue p v
def PEsound (n : Nat) : Prop := ∀ (d : Nat) (s : Bytes) (xs : List JSON) (r : Bytes),
  s.length ≤ n → pe d s = some (xs, r) → ∃ p, s = p ++ r ∧ SElems p xs
def PMsound (n : Nat) : Prop := ∀ (d : Nat) (s : Bytes) (kvs : List (Bytes × JSON)) (r : Bytes),
  s.length ≤ n → pm d s = some (kvs, r) → ∃ p, s = p ++ r ∧ SMembers p kvs


/-! ## Stage 1 — value soundness at `n+1` from elem/member soundness at `≤ n` -/

theorem hV_step (n : Nat) (ihE : PEsound n) (ihM : PMsound n) : PVsound (n+1) := by
  intro d s v r hlen h
  unfold pv at h
  rw [parseValue.eq_def] at h
  split at h
  case h_1 => exact absurd h (by simp)                          -- []
  case h_2 r0 =>                                                 -- null
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[110,117,108,108], rfl, SValue.null⟩
  case h_3 r0 =>                                                 -- true
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[116,114,117,101], rfl, SValue.true_⟩
  case h_4 r0 =>                                                 -- false
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[102,97,108,115,101], rfl, SValue.false_⟩
  case h_5 r0 =>                                                 -- string
    split at h
    · exact absurd h (by simp)
    · next w r' hs =>
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨p, hp, hchars⟩ := parseStrBody_sound' hs
        exact ⟨34 :: (p ++ [34]), by rw [hp]; simp, SValue.str ⟨p, rfl, hchars⟩⟩
  case h_6 r0 =>                                                 -- array
    split at h
    · exact absurd h (by simp)                                  -- depth limit
    · next hdlt =>
      split at h
      · next r' hw =>                                           -- empty array
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨w, hwq, hws⟩ := skipWs_split r0
          rw [hw] at hwq
          exact ⟨91 :: (w ++ [93]), by rw [hwq]; simp, SValue.arr0 hws⟩
      · next hne =>                                             -- non-empty array
          split at h
          · exact absurd h (by simp)
          · next xs r' hr hpe =>
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hle : (skipWs r0).length ≤ n := by
                have := skipWs_le r0; simp only [List.length_cons] at hlen; omega
              have hpe' : pe (d+1) (skipWs r0) = some (xs, r') := by unfold pe; rw [hpe]; rfl
              obtain ⟨pp, hpp, hsel⟩ := ihE (d+1) (skipWs r0) xs r' hle hpe'
              obtain ⟨w, hwq, hws⟩ := skipWs_split r0
              exact ⟨91 :: (w ++ pp), by rw [hwq, hpp]; simp, SValue.arr hws hsel⟩
  case h_7 r0 =>                                                 -- object
    split at h
    · exact absurd h (by simp)                                  -- depth limit
    · next hdlt =>
      split at h
      · next r' hw =>                                           -- empty object
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          obtain ⟨w, hwq, hws⟩ := skipWs_split r0
          rw [hw] at hwq
          exact ⟨123 :: (w ++ [125]), by rw [hwq]; simp, SValue.obj0 hws⟩
      · next hne =>                                             -- non-empty object
          split at h
          · exact absurd h (by simp)
          · next kvs r' hr hpm =>
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hle : (skipWs r0).length ≤ n := by
                have := skipWs_le r0; simp only [List.length_cons] at hlen; omega
              have hpm' : pm (d+1) (skipWs r0) = some (kvs, r') := by unfold pm; rw [hpm]; rfl
              obtain ⟨pp, hpp, hsm⟩ := ihM (d+1) (skipWs r0) kvs r' hle hpm'
              obtain ⟨w, hwq, hws⟩ := skipWs_split r0
              exact ⟨123 :: (w ++ pp), by rw [hwq, hpp]; simp, SValue.obj hws hsm⟩
  case h_8 c cs hlit1 hlit2 hlit3 hq hbr hbc =>                  -- number (catch-all)
    split at h
    · next hgate =>
        split at h
        · exact absurd h (by simp)                              -- scanNumber none
        · next nn rr hn =>
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨p, hp, htok⟩ := scanNumber_sound hn
            have hlt := scanNumber_lt hn
            have hpne : p ≠ [] := by
              intro h0; rw [h0, List.nil_append] at hp; rw [← hp] at hlt; omega
            obtain ⟨c', p', rfl⟩ : ∃ c' p', p = c' :: p' := by
              cases p with | nil => exact absurd rfl hpne | cons a as => exact ⟨a, as, rfl⟩
            rw [List.cons_append] at hp
            simp only [List.cons.injEq] at hp
            obtain ⟨rfl, hcs⟩ := hp
            exact ⟨c :: p', by rw [List.cons_append, hcs], SValue.num (gate_of hgate) htok⟩
    · exact absurd h (by simp)                                  -- gate false


/-! ## Stage 2 — element soundness at `n+1` from value soundness at `n+1` + elem soundness at `≤ n` -/

theorem hE_step (n : Nat) (hV : PVsound (n+1)) (ihE : PEsound n) : PEsound (n+1) := by
  intro d s xs r hlen h
  unfold pe at h
  rw [parseElems.eq_def] at h
  split at h                                        -- match parseValue depth s
  · exact absurd h (by simp)                        -- parseValue none
  · next v r' hr hpv =>                             -- some ⟨(v, r'), hr⟩
    -- value soundness at the SAME length (≤ n+1) via hV
    have hpv' : pv d s = some (v, r') := by unfold pv; rw [hpv]; rfl
    obtain ⟨p1, hp1, hsv⟩ := hV d s v r' hlen hpv'
    -- strict decrease from the grammar: p1 ≠ [] ⇒ |r'| < |s|
    have hdec : r'.length < s.length := by
      have := SValue_ne_nil hsv
      rw [hp1]; simp only [List.length_append]
      cases p1 with | nil => exact absurd rfl this | cons a as => simp
    split at h                                       -- match skipWs r'
    · next r2 hw =>                                  -- 44 :: r2 (comma, recurse)
        split at h
        · exact absurd h (by simp)                   -- recursive parseElems none
        · next vs r3 hr3 hpe =>
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hle : (skipWs r2).length ≤ n := by
              have a1 := skipWs_le r'; have a2 := skipWs_le r2
              rw [hw] at a1; simp only [List.length_cons] at a1; omega
            have hpe' : pe d (skipWs r2) = some (vs, r3) := by unfold pe; rw [hpe]; rfl
            obtain ⟨pp, hpp, hsel⟩ := ihE d (skipWs r2) vs r3 hle hpe'
            obtain ⟨w2, hw2q, hws2⟩ := skipWs_split r2
            obtain ⟨w1, hw1q, hws1⟩ := skipWs_split r'
            rw [hw] at hw1q
            refine ⟨p1 ++ w1 ++ [44] ++ w2 ++ pp, ?_, SElems.cons hsv hws1 hws2 hsel⟩
            rw [hp1, hw1q, hw2q, hpp]; simp
    · next r2 hw =>                                  -- 93 :: r2 (close, last element)
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨w1, hw1q, hws1⟩ := skipWs_split r'
        rw [hw] at hw1q
        refine ⟨p1 ++ w1 ++ [93], ?_, SElems.last hsv hws1⟩
        rw [hp1, hw1q]; simp
    · next hne => exact absurd h (by simp)           -- skipWs r' is neither , nor ]

/-! ## Stage 3 — member soundness at `n+1` from value/member soundness at `≤ n` -/

theorem hM_step (n : Nat) (ihV : PVsound n) (ihM : PMsound n) : PMsound (n+1) := by
  intro d s kvs r hlen h
  unfold pm at h
  rw [parseMembers.eq_def] at h
  split at h
  · next rk =>                                       -- s = 34 :: rk
    split at h
    · exact absurd h (by simp)                       -- parseStrBody none
    · next k r1 hk =>                                -- some (k, r1)
      split at h
      · next r2 hw1 =>                                -- skipWs r1 = 58 :: r2 (colon)
        split at h
        · exact absurd h (by simp)                    -- parseValue none
        · next v r3 hr3 hpv =>
          -- sub-value on strictly shorter input: use ihV
          have hlensub : (skipWs r2).length ≤ n := by
            have hb := parseStrBody_le hk
            have a1 := skipWs_le r1; have a2 := skipWs_le r2
            rw [hw1] at a1
            simp only [List.length_cons] at hlen a1; omega
          have hpv' : pv d (skipWs r2) = some (v, r3) := by unfold pv; rw [hpv]; rfl
          obtain ⟨pv1, hpvq, hsv⟩ := ihV d (skipWs r2) v r3 hlensub hpv'
          have hr3dec : r3.length < (skipWs r2).length := by
            have hne := SValue_ne_nil hsv
            rw [hpvq]; simp only [List.length_append]
            cases pv1 with | nil => exact absurd rfl hne | cons a as => simp
          obtain ⟨pk, hpk, hchars⟩ := parseStrBody_sound' hk
          obtain ⟨w1, hw1q, hws1⟩ := skipWs_split r1
          rw [hw1] at hw1q
          obtain ⟨w2, hw2q, hws2⟩ := skipWs_split r2
          split at h
          · next r4 hw2 =>                             -- skipWs r3 = 44 :: r4 (comma, recurse)
            split at h
            · exact absurd h (by simp)                 -- recursive parseMembers none
            · next kvs2 r5 hr5 hpm =>
                simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hlem : (skipWs r4).length ≤ n := by
                  have hb := parseStrBody_le hk
                  have a1 := skipWs_le r1; have a2 := skipWs_le r2
                  have a3 := skipWs_le r3; have a4 := skipWs_le r4
                  rw [hw1] at a1; rw [hw2] at a3
                  simp only [List.length_cons] at hlen a1 a3; omega
                have hpm' : pm d (skipWs r4) = some (kvs2, r5) := by unfold pm; rw [hpm]; rfl
                obtain ⟨pm1, hpmq, hsm⟩ := ihM d (skipWs r4) kvs2 r5 hlem hpm'
                obtain ⟨w3, hw3q, hws3⟩ := skipWs_split r3
                rw [hw2] at hw3q
                obtain ⟨w4, hw4q, hws4⟩ := skipWs_split r4
                refine ⟨34 :: (pk ++ [34]) ++ w1 ++ [58] ++ w2 ++ pv1 ++ w3 ++ [44] ++ w4 ++ pm1,
                        ?_, ?_⟩
                · show (34 :: rk) = _
                  have hrk : rk = pk ++ (34 :: r1) := hpk
                  rw [hrk, hw1q, hw2q, hpvq, hw3q, hw4q, hpmq]; simp
                · exact SMembers.cons ⟨pk, rfl, hchars⟩ hws1 hws2 hsv hws3 hws4 hsm
          · next r4 hw2 =>                             -- skipWs r3 = 125 :: r4 (close, last)
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨w3, hw3q, hws3⟩ := skipWs_split r3
              rw [hw2] at hw3q
              refine ⟨34 :: (pk ++ [34]) ++ w1 ++ [58] ++ w2 ++ pv1 ++ w3 ++ [125], ?_, ?_⟩
              · show (34 :: rk) = _
                have hrk : rk = pk ++ (34 :: r1) := hpk
                rw [hrk, hw1q, hw2q, hpvq, hw3q]; simp
              · exact SMembers.last ⟨pk, rfl, hchars⟩ hws1 hws2 hsv hws3
          · next hne => exact absurd h (by simp)       -- skipWs r3 neither , nor }
      · next hne => exact absurd h (by simp)           -- skipWs r1 not a colon
  · next hne => exact absurd h (by simp)               -- s not starting with a quote


/-! ## The staged induction and the final soundness theorems -/

theorem struct_sound : ∀ n, PVsound n ∧ PEsound n ∧ PMsound n := by
  intro n
  induction n with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro d s _ r hlen h
      have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega); subst hs
      rw [pv, show parseValue d ([]:Bytes) = none by simp only [parseValue]] at h; simp at h
    · intro d s _ r hlen h
      have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega); subst hs
      have hpv : parseValue d ([]:Bytes) = none := by simp only [parseValue]
      rw [pe, show parseElems d ([]:Bytes) = none by rw [parseElems.eq_def, hpv]] at h; simp at h
    · intro d s _ r hlen h
      have hs : s = [] := List.eq_nil_of_length_eq_zero (by omega); subst hs
      rw [pm, show parseMembers d ([]:Bytes) = none by simp only [parseMembers]] at h; simp at h
  | succ n ih =>
    obtain ⟨ihV, ihE, ihM⟩ := ih
    have hV : PVsound (n+1) := hV_step n ihE ihM
    have hE : PEsound (n+1) := hE_step n hV ihE
    have hM : PMsound (n+1) := hM_step n ihV ihM
    exact ⟨hV, hE, hM⟩

/-- **VALUE SOUNDNESS.** Every input `parseValue` accepts, the bytes it consumed form a value
    that the independent grammar assigns exactly the returned value. -/
theorem pv_sound {d : Nat} {s : Bytes} {v : JSON} {r : Bytes} (h : pv d s = some (v, r)) :
    ∃ p, s = p ++ r ∧ SValue p v :=
  (struct_sound s.length).1 d s v r (Nat.le_refl _) h

/-- **ELEMENT SOUNDNESS.** -/
theorem pe_sound {d : Nat} {s : Bytes} {xs : List JSON} {r : Bytes} (h : pe d s = some (xs, r)) :
    ∃ p, s = p ++ r ∧ SElems p xs :=
  (struct_sound s.length).2.1 d s xs r (Nat.le_refl _) h

/-- **MEMBER SOUNDNESS.** -/
theorem pm_sound {d : Nat} {s : Bytes} {kvs : List (Bytes × JSON)} {r : Bytes}
    (h : pm d s = some (kvs, r)) : ∃ p, s = p ++ r ∧ SMembers p kvs :=
  (struct_sound s.length).2.2 d s kvs r (Nat.le_refl _) h


/-! ## Document level and C2 -/

/-- `skipBom` drops an optional BOM. -/
theorem skipBom_split (s : Bytes) : ∃ bom, s = bom ++ skipBom s ∧ Bom bom := by
  by_cases hb : ∃ r, s = 0xEF :: 0xBB :: 0xBF :: r
  · obtain ⟨r, rfl⟩ := hb
    exact ⟨[0xEF, 0xBB, 0xBF], rfl, Or.inr rfl⟩
  · refine ⟨[], ?_, Or.inl rfl⟩
    have hs : skipBom s = s := by
      unfold skipBom; split
      · next r => exact absurd ⟨r, rfl⟩ hb
      · rfl
    rw [hs]; simp

/-- **C2 — VALUE SOUNDNESS at the document level.**

    `parseDoc s = some v` implies the SPEC grammar accepts `s` as denoting exactly `v`:
    there is a BOM, a whitespace block, a grammatical value prefix denoting `v`, and a
    (discarded) trailing remainder, in that order. The depth bound is supplied by the
    released `parseDoc_depth` (v1.0.1). -/
theorem parseDoc_sound {s : Bytes} {v : JSON} (h : parseDoc s = some v) : SDoc s v := by
  -- extract the underlying parseValue success (mirrors parseDoc_canonical)
  unfold parseDoc at h
  split at h
  · exact absurd h (by simp)
  · next v' r' hp hn =>
      simp only [Option.some.injEq] at h
      subst h
      have hpvq : pv 0 (skipWs (skipBom s)) = some (v', r') := by unfold pv; rw [hn]; rfl
      obtain ⟨p, hp2, hsv⟩ := pv_sound hpvq
      obtain ⟨bom, hbom, hBom⟩ := skipBom_split s
      obtain ⟨w, hw, hWs⟩ := skipWs_split (skipBom s)
      refine ⟨bom, w, p, r', hBom, hWs, hsv, ?_, ?_⟩
      · exact parseDoc_depth (by unfold parseDoc; rw [hn])
      · rw [hbom, hw, hp2]; simp

end Cjson.Spec
