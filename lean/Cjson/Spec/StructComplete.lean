/-
  GAP-2, C4 — structural completeness and the C4 theorem.

  Mutual structural induction on the independent grammar derivations (SValue/SElems/SMembers,
  via SValue.rec), threading the depth bound `d + jdepth v ≤ nestingLimit` and using SafeTail on
  the value motive. The number and string LEAVES are the already-proved `scanNumber_complete`
  and `parseStrBody_complete`; the recursive structure is assembled by GENERALISED assembly
  lemmas proved here (the released `pv_arr_cons`/`pe_cons`/… assume `skipWs (c::t) = c::t`, i.e.
  NO interior whitespace, because `serialize` emits none — see the reuse note in
  ADEQUACY_REPORT; they are canonical-specific, so we generalise).

  Independence: no parser/grammar change; the grammar admits arbitrary spellings (interior
  whitespace, non-canonical numbers/strings) and the proof forces the parser through them.

  Zero sorry, zero custom axioms.
-/
import Cjson.Spec.StructSound
import Cjson.Spec.NumComplete
import Cjson.Spec.StrComplete

namespace Cjson.Spec

open Cjson

/-! ## Whitespace / head helpers -/

theorem skipWs_append_Ws {w t : Bytes} (hw : Ws w) : skipWs (w ++ t) = skipWs t := by
  induction w with
  | nil => rfl
  | cons c w' ih =>
    have hc : isWs c = true := by
      have := hw c (by simp); unfold IsWs at this; unfold isWs; simpa using this
    have hws : ∀ x ∈ w', IsWs x := fun x hx => hw x (by simp [hx])
    simp only [List.cons_append, skipWs, if_pos hc]; exact ih hws

theorem SValue_head {p : Bytes} {v : JSON} (h : SValue p v) :
    ∃ c t, p = c :: t ∧ (c = 110 ∨ c = 116 ∨ c = 102 ∨ c = 34 ∨ c = 91 ∨ c = 123
                          ∨ c = 45 ∨ isDigitB c = true) := by
  cases h with
  | null => exact ⟨_, _, rfl, Or.inl rfl⟩
  | true_ => exact ⟨_, _, rfl, Or.inr (Or.inl rfl)⟩
  | false_ => exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
  | str hs => obtain ⟨body, hp, _⟩ := hs
              exact ⟨34, body ++ [34], hp, Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩
  | num hg _ => rcases hg with rfl | hd
                · exact ⟨45, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))⟩
                · exact ⟨_, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd))))))⟩
  | arr0 _ => exact ⟨91, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | arr _ _ => exact ⟨91, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))⟩
  | obj0 _ => exact ⟨123, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩
  | obj _ _ => exact ⟨123, _, rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))⟩

theorem head_props {c : UInt8}
    (h : c = 110 ∨ c = 116 ∨ c = 102 ∨ c = 34 ∨ c = 91 ∨ c = 123 ∨ c = 45 ∨ isDigitB c = true) :
    isWs c = false ∧ c ≠ 93 ∧ c ≠ 125 ∧ c ≠ 44 := by
  unfold isWs
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|hd
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · unfold isDigitB at hd; simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
    refine ⟨by simp; omega, ?_, ?_, ?_⟩ <;>
      (intro hcon; subst hcon; exact absurd hd (by decide))

/-- The bytes of an `SValue` never begin with whitespace, so `skipWs` fixes `p ++ anything`. -/
theorem SValue_skipWs {p : Bytes} {v : JSON} (h : SValue p v) (rest : Bytes) :
    skipWs (p ++ rest) = p ++ rest := by
  obtain ⟨c, t, rfl, hc⟩ := SValue_head h
  have := (head_props hc).1
  rw [List.cons_append, skipWs, if_neg (by rw [this]; simp)]

-- Generalized array-empty: pre is arbitrary, skipWs pre lands on the closer.
theorem pv_arr_empty_gen {d : Nat} {pre rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs pre = 93 :: rest) :
    pv d (91 :: pre) = some (JSON.arr [], rest) := by
  unfold pv
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw => rw [hws] at hw; simp only [List.cons.injEq] at hw
                  obtain ⟨-, rfl⟩ := hw; rfl
  · next hw => exact absurd hws (hw rest)

-- Generalized array-cons: identical proof to released pv_arr_cons, head abstracted to pre.
theorem pv_arr_cons_gen {d : Nat} {pre : Bytes} {c : UInt8} {t : Bytes}
    {xs : List JSON} {rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs pre = c :: t) (hc : c ≠ 93)
    (hpe : pe (d + 1) (skipWs pre) = some (xs, rest)) :
    pv d (91 :: pre) = some (JSON.arr xs, rest) := by
  unfold pv; unfold pe at hpe
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw => rw [hws] at hw; simp only [List.cons.injEq] at hw; exact absurd hw.1 hc
  · next hw =>
      split
      · next hn => rw [hn] at hpe; exact absurd hpe (by simp)
      · next p hn =>
          rw [hn] at hpe
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpe
          obtain ⟨rfl, rfl⟩ := hpe
          rfl

theorem pv_obj_empty_gen {d : Nat} {pre rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs pre = 125 :: rest) :
    pv d (123 :: pre) = some (JSON.obj [], rest) := by
  unfold pv
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw => rw [hws] at hw; simp only [List.cons.injEq] at hw
                  obtain ⟨-, rfl⟩ := hw; rfl
  · next hw => exact absurd hws (hw rest)

theorem pv_obj_cons_gen {d : Nat} {pre : Bytes} {c : UInt8} {t : Bytes}
    {kvs : List (Bytes × JSON)} {rest : Bytes}
    (hd : d < nestingLimit) (hws : skipWs pre = c :: t) (hc : c ≠ 125)
    (hpm : pm (d + 1) (skipWs pre) = some (kvs, rest)) :
    pv d (123 :: pre) = some (JSON.obj kvs, rest) := by
  unfold pv; unfold pm at hpm
  rw [parseValue, dif_neg (by omega)]
  split
  · next r' hw => rw [hws] at hw; simp only [List.cons.injEq] at hw; exact absurd hw.1 hc
  · next hw =>
      split
      · next hn => rw [hn] at hpm; exact absurd hpm (by simp)
      · next p hn =>
          rw [hn] at hpm
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hpm
          obtain ⟨rfl, rfl⟩ := hpm
          rfl

/-! ## Generalized loop equations (whitespace-tolerant) -/

theorem pe_last_gen {d : Nat} {s : Bytes} {x : JSON} {r rest : Bytes}
    (h : pv d s = some (x, r)) (hw : skipWs r = 93 :: rest) :
    pe d s = some ([x], rest) := by
  unfold pe; unfold pv at h
  rw [parseElems]
  split
  · next hn => rw [hn] at h; exact absurd h (by simp)
  · next v r' hr' hn =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split
      · next r2 hbr => rw [hw] at hbr; simp only [List.cons.injEq] at hbr
                       exact absurd hbr.1 (by decide)
      · next r2 hbr => rw [hw] at hbr; simp only [List.cons.injEq] at hbr
                       obtain ⟨-, rfl⟩ := hbr; rfl
      · next h44 h93 => exact (h93 rest hw).elim

theorem pe_cons_gen {d : Nat} {s : Bytes} {x : JSON} {r r2 : Bytes}
    {xs : List JSON} {rest : Bytes}
    (h : pv d s = some (x, r)) (hw : skipWs r = 44 :: r2)
    (hrec : pe d (skipWs r2) = some (xs, rest)) : pe d s = some (x :: xs, rest) := by
  unfold pe at *; unfold pv at h
  rw [parseElems]
  split
  · next hn => rw [hn] at h; exact absurd h (by simp)
  · next v r' hr' hn =>
      rw [hn] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      split
      · next r3 hbr =>
          rw [hw] at hbr; simp only [List.cons.injEq] at hbr
          obtain ⟨-, rfl⟩ := hbr
          split
          · next hn2 => rw [hn2] at hrec; exact absurd hrec (by simp)
          · next p hn2 =>
              rw [hn2] at hrec
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
              obtain ⟨rfl, rfl⟩ := hrec; rfl
      · next r3 hbr => rw [hw] at hbr; simp only [List.cons.injEq] at hbr
                       exact absurd hbr.1 (by decide)
      · next h44 h93 => exact (h44 r2 hw).elim

theorem pm_last_gen {d : Nat} {rk k r1 sv : Bytes} {v : JSON} {r rest : Bytes}
    (hk : parseStrBody rk = some (k, r1)) (hw1 : skipWs r1 = 58 :: sv)
    (hv : pv d (skipWs sv) = some (v, r)) (hw : skipWs r = 125 :: rest) :
    pm d (34 :: rk) = some ([(k, v)], rest) := by
  unfold pm; unfold pv at hv
  rw [parseMembers]
  split
  · next hn => rw [hk] at hn; exact absurd hn (by simp)
  · next k' r1' hn =>
      rw [hk] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      split
      · next r2 hbr =>
          rw [hw1] at hbr; simp only [List.cons.injEq] at hbr
          obtain ⟨-, rfl⟩ := hbr
          split
          · next hn2 => rw [hn2] at hv; exact absurd hv (by simp)
          · next v' r3 hr3 hn2 =>
              rw [hn2] at hv
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, rfl⟩ := hv
              split
              · next r4 hw2 => rw [hw] at hw2; simp only [List.cons.injEq] at hw2
                               exact absurd hw2.1 (by decide)
              · next r4 hw2 => rw [hw] at hw2; simp only [List.cons.injEq] at hw2
                               obtain ⟨-, rfl⟩ := hw2; rfl
              · next h44 h125 => exact (h125 rest hw).elim
      · next hx2 => exact (hx2 sv hw1).elim

theorem pm_cons_gen {d : Nat} {rk k r1 sv : Bytes} {v : JSON} {r sr : Bytes}
    {kvs : List (Bytes × JSON)} {rest : Bytes}
    (hk : parseStrBody rk = some (k, r1)) (hw1 : skipWs r1 = 58 :: sv)
    (hv : pv d (skipWs sv) = some (v, r)) (hw : skipWs r = 44 :: sr)
    (hrec : pm d (skipWs sr) = some (kvs, rest)) :
    pm d (34 :: rk) = some ((k, v) :: kvs, rest) := by
  unfold pm at *; unfold pv at hv
  rw [parseMembers]
  split
  · next hn => rw [hk] at hn; exact absurd hn (by simp)
  · next k' r1' hn =>
      rw [hk] at hn
      simp only [Option.some.injEq, Prod.mk.injEq] at hn
      obtain ⟨rfl, rfl⟩ := hn
      split
      · next r2 hbr =>
          rw [hw1] at hbr; simp only [List.cons.injEq] at hbr
          obtain ⟨-, rfl⟩ := hbr
          split
          · next hn2 => rw [hn2] at hv; exact absurd hv (by simp)
          · next v' r3 hr3 hn2 =>
              rw [hn2] at hv
              simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hv
              obtain ⟨rfl, rfl⟩ := hv
              split
              · next r4 hw2 =>
                  rw [hw] at hw2; simp only [List.cons.injEq] at hw2
                  obtain ⟨-, rfl⟩ := hw2
                  split
                  · next hn3 => rw [hn3] at hrec; exact absurd hrec (by simp)
                  · next p hn3 =>
                      rw [hn3] at hrec
                      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨rfl, rfl⟩ := hrec; rfl
              · next r4 hw2 => rw [hw] at hw2; simp only [List.cons.injEq] at hw2
                               exact absurd hw2.1 (by decide)
              · next h44 h125 => exact (h44 sr hw).elim
      · next hx2 => exact (hx2 sv hw1).elim

/-! ## Head / skipWs for element and member lists -/

theorem SElems_head {p : Bytes} {xs : List JSON} (h : SElems p xs) :
    ∃ c t, p = c :: t ∧ (c = 110 ∨ c = 116 ∨ c = 102 ∨ c = 34 ∨ c = 91 ∨ c = 123
                          ∨ c = 45 ∨ isDigitB c = true) := by
  cases h with
  | @last p' v' w' hv hw =>
      obtain ⟨c, t, rfl, hh⟩ := SValue_head hv
      exact ⟨c, t ++ w' ++ [93], by simp only [List.cons_append], hh⟩
  | @cons p' v' w1 w2 q vs hv _ _ _ =>
      obtain ⟨c, t, rfl, hh⟩ := SValue_head hv
      exact ⟨c, t ++ w1 ++ [44] ++ w2 ++ q, by simp only [List.cons_append], hh⟩

theorem SElems_skipWs {p : Bytes} {xs : List JSON} (h : SElems p xs) (rest : Bytes) :
    skipWs (p ++ rest) = p ++ rest := by
  obtain ⟨c, t, rfl, hh⟩ := SElems_head h
  rw [List.cons_append, skipWs, if_neg (by have := (head_props hh).1; rw [this]; simp)]

theorem SMembers_head {p : Bytes} {kvs : List (Bytes × JSON)} (h : SMembers p kvs) :
    ∃ t, p = 34 :: t := by
  cases h with
  | @last k out w1 w2 pv v w3 hk _ _ _ _ =>
      obtain ⟨body, rfl, _⟩ := hk
      exact ⟨(body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pv ++ w3 ++ [125], by simp only [List.cons_append]⟩
  | @cons k out w1 w2 pv v w3 w4 q kvs' hk _ _ _ _ _ _ =>
      obtain ⟨body, rfl, _⟩ := hk
      exact ⟨(body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pv ++ w3 ++ [44] ++ w4 ++ q,
             by simp only [List.cons_append]⟩

theorem SMembers_skipWs {p : Bytes} {kvs : List (Bytes × JSON)} (h : SMembers p kvs)
    (rest : Bytes) : skipWs (p ++ rest) = p ++ rest := by
  obtain ⟨t, rfl⟩ := SMembers_head h
  rw [List.cons_append, skipWs, if_neg (by decide)]

/-! ## SafeTail for whitespace-then-delimiter tails -/

theorem safeTail_ws {w rest : Bytes} {b : UInt8} (hw : Ws w)
    (hb : b.toNat = 44 ∨ b.toNat = 93 ∨ b.toNat = 125) : SafeTail (w ++ b :: rest) := by
  cases w with
  | nil => exact safeTail_struct hb
  | cons a w' =>
      intro c t hct
      rw [List.cons_append] at hct
      simp only [List.cons.injEq] at hct
      obtain ⟨rfl, -⟩ := hct
      have ha : a.toNat ≤ 32 := hw a (by simp)
      refine ⟨?_, by omega, by omega, by omega⟩
      unfold isDigitB
      have hnd : ¬ (48 ≤ a.toNat) := by omega
      simp [hnd]

/-! ## Structural completeness (mutual induction on the grammar derivation) -/

-- @attested-gap2 Cjson.Spec.struct_complete
theorem struct_complete {p0 : Bytes} {v0 : JSON} (h0 : SValue p0 v0) :
    ∀ d rest, d + jdepth v0 ≤ nestingLimit → SafeTail rest →
      pv d (p0 ++ rest) = some (v0, rest) := by
  refine SValue.rec
    (motive_1 := fun p v _ => ∀ d rest, d + jdepth v ≤ nestingLimit → SafeTail rest →
        pv d (p ++ rest) = some (v, rest))
    (motive_2 := fun p xs _ => ∀ d rest, d + jdepthL xs ≤ nestingLimit →
        pe d (p ++ rest) = some (xs, rest))
    (motive_3 := fun p kvs _ => ∀ d rest, d + jdepthKV kvs ≤ nestingLimit →
        pm d (p ++ rest) = some (kvs, rest))
    ?null ?true ?false ?str ?num ?arr0 ?arr ?obj0 ?obj ?elast ?econs ?mlast ?mcons h0
  case null => intro d rest _ _; exact pv_null
  case true => intro d rest _ _; exact pv_true
  case false => intro d rest _ _; exact pv_false
  case str =>
    intro pp out hstr d rest _ _
    obtain ⟨body, rfl, hchars⟩ := hstr
    show pv d ((34 :: (body ++ [34])) ++ rest) = some (JSON.str out, rest)
    rw [List.cons_append, List.append_assoc]
    exact pv_str_known (parseStrBody_complete hchars)
  case num =>
    intro c pp n hg hnum d rest _ hst
    show pv d ((c :: pp) ++ rest) = some (JSON.num n, rest)
    rw [List.cons_append]
    have hg' : c.toNat = 45 ∨ isDigitB c = true := by
      rcases hg with rfl | hd
      · exact Or.inl (by decide)
      · exact Or.inr hd
    have hsc := scanNumber_complete hnum hst
    rw [List.cons_append] at hsc
    exact pv_num_known hg' hsc
  case arr0 =>
    intro w hw d rest hdep _
    have hdd : d < nestingLimit := by simp only [jdepth, jdepthL] at hdep; omega
    show pv d ((91 :: (w ++ [93])) ++ rest) = some (JSON.arr [], rest)
    rw [List.cons_append]
    refine pv_arr_empty_gen hdd ?_
    rw [List.append_assoc, skipWs_append_Ws hw]
    show skipWs (93 :: rest) = 93 :: rest
    rw [skipWs, if_neg (by decide)]
  case arr =>
    intro w pp xs hw hSE ih2 d rest hdep _
    have hdep' : (d + 1) + jdepthL xs ≤ nestingLimit := by simp only [jdepth] at hdep; omega
    have hdd : d < nestingLimit := by omega
    obtain ⟨c, t, hpeq, hh⟩ := SElems_head hSE
    have hc93 : c ≠ 93 := (head_props hh).2.1
    have hsp : skipWs ((w ++ pp) ++ rest) = pp ++ rest := by
      rw [List.append_assoc, skipWs_append_Ws hw, SElems_skipWs hSE]
    show pv d ((91 :: (w ++ pp)) ++ rest) = some (JSON.arr xs, rest)
    rw [List.cons_append]
    have hws : skipWs ((w ++ pp) ++ rest) = c :: (t ++ rest) := by
      rw [hsp, hpeq, List.cons_append]
    refine pv_arr_cons_gen hdd hws hc93 ?_
    rw [hsp]; exact ih2 (d + 1) rest hdep'
  case obj0 =>
    intro w hw d rest hdep _
    have hdd : d < nestingLimit := by simp only [jdepth, jdepthKV] at hdep; omega
    show pv d ((123 :: (w ++ [125])) ++ rest) = some (JSON.obj [], rest)
    rw [List.cons_append]
    refine pv_obj_empty_gen hdd ?_
    rw [List.append_assoc, skipWs_append_Ws hw]
    show skipWs (125 :: rest) = 125 :: rest
    rw [skipWs, if_neg (by decide)]
  case obj =>
    intro w pp kvs hw hSM ih3 d rest hdep _
    have hdep' : (d + 1) + jdepthKV kvs ≤ nestingLimit := by simp only [jdepth] at hdep; omega
    have hdd : d < nestingLimit := by omega
    obtain ⟨t, hpeq⟩ := SMembers_head hSM
    have hsp : skipWs ((w ++ pp) ++ rest) = pp ++ rest := by
      rw [List.append_assoc, skipWs_append_Ws hw, SMembers_skipWs hSM]
    show pv d ((123 :: (w ++ pp)) ++ rest) = some (JSON.obj kvs, rest)
    rw [List.cons_append]
    have hws : skipWs ((w ++ pp) ++ rest) = 34 :: (t ++ rest) := by
      rw [hsp, hpeq, List.cons_append]
    refine pv_obj_cons_gen hdd hws (by decide) ?_
    rw [hsp]; exact ih3 (d + 1) rest hdep'
  case elast =>
    intro pp v w hv hw ih1 d rest hdep
    have hjd : d + jdepth v ≤ nestingLimit := by simp only [jdepthL] at hdep; omega
    have hst : SafeTail (w ++ [93] ++ rest) := by
      rw [List.append_assoc]; exact safeTail_ws hw (Or.inr (Or.inl (by decide)))
    have hv' : pv d (pp ++ (w ++ [93] ++ rest)) = some (v, w ++ [93] ++ rest) := ih1 d _ hjd hst
    show pe d ((pp ++ w ++ [93]) ++ rest) = some ([v], rest)
    rw [show (pp ++ w ++ [93]) ++ rest = pp ++ (w ++ [93] ++ rest) from by simp only [List.append_assoc]]
    refine pe_last_gen hv' ?_
    rw [List.append_assoc, skipWs_append_Ws hw]
    show skipWs (93 :: rest) = 93 :: rest
    rw [skipWs, if_neg (by decide)]
  case econs =>
    intro pp v w1 w2 q vs hv hw1 hw2 hSE ih1 ih2 d rest hdep
    have hjv : d + jdepth v ≤ nestingLimit := by simp only [jdepthL] at hdep; omega
    have hjt : d + jdepthL vs ≤ nestingLimit := by simp only [jdepthL] at hdep; omega
    have hst : SafeTail (w1 ++ [44] ++ (w2 ++ q ++ rest)) := by
      rw [List.append_assoc]; exact safeTail_ws hw1 (Or.inl (by decide))
    have hv' : pv d (pp ++ (w1 ++ [44] ++ (w2 ++ q ++ rest)))
        = some (v, w1 ++ [44] ++ (w2 ++ q ++ rest)) := ih1 d _ hjv hst
    show pe d ((pp ++ w1 ++ [44] ++ w2 ++ q) ++ rest) = some (v :: vs, rest)
    rw [show (pp ++ w1 ++ [44] ++ w2 ++ q) ++ rest = pp ++ (w1 ++ [44] ++ (w2 ++ q ++ rest))
        from by simp only [List.append_assoc]]
    refine pe_cons_gen (r2 := w2 ++ q ++ rest) hv' ?_ ?_
    · rw [List.append_assoc, skipWs_append_Ws hw1]
      show skipWs (44 :: (w2 ++ q ++ rest)) = 44 :: (w2 ++ q ++ rest)
      rw [skipWs, if_neg (by decide)]
    · rw [List.append_assoc, skipWs_append_Ws hw2, SElems_skipWs hSE]; exact ih2 d rest hjt
  case mlast =>
    intro k out w1 w2 pp v w3 hk hw1 hw2 hv hw3 ih1 d rest hdep
    have hjv : d + jdepth v ≤ nestingLimit := by simp only [jdepthKV] at hdep; omega
    obtain ⟨body, rfl, hchars⟩ := hk
    have hst : SafeTail (w3 ++ [125] ++ rest) := by
      rw [List.append_assoc]; exact safeTail_ws hw3 (Or.inr (Or.inr (by decide)))
    have hv' : pv d (pp ++ (w3 ++ [125] ++ rest)) = some (v, w3 ++ [125] ++ rest) := ih1 d _ hjv hst
    show pm d ((34 :: (body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pp ++ w3 ++ [125]) ++ rest)
        = some ([(out, v)], rest)
    rw [show (34 :: (body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pp ++ w3 ++ [125]) ++ rest
        = 34 :: ((body ++ [34]) ++ (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [125] ++ rest)))))
        from by simp only [List.cons_append, List.append_assoc]]
    refine pm_last_gen (k := out) (r1 := w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [125] ++ rest))))
      (sv := w2 ++ (pp ++ (w3 ++ [125] ++ rest))) (r := w3 ++ [125] ++ rest) ?_ ?_ ?_ ?_
    · have := parseStrBody_complete hchars (rest := w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [125] ++ rest))))
      rw [show body ++ (34 :: (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [125] ++ rest)))))
          = (body ++ [34]) ++ (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [125] ++ rest))))
          from by simp only [List.append_assoc, List.cons_append, List.nil_append]] at this
      exact this
    · rw [List.append_assoc, skipWs_append_Ws hw1]
      show skipWs (58 :: (w2 ++ (pp ++ (w3 ++ [125] ++ rest)))) = _
      rw [skipWs, if_neg (by decide)]
    · rw [skipWs_append_Ws hw2, SValue_skipWs hv]; exact hv'
    · rw [List.append_assoc, skipWs_append_Ws hw3]
      show skipWs (125 :: rest) = 125 :: rest
      rw [skipWs, if_neg (by decide)]
  case mcons =>
    intro k out w1 w2 pp v w3 w4 q kvs hk hw1 hw2 hv hw3 hw4 hSM ih1 ih3 d rest hdep
    have hjv : d + jdepth v ≤ nestingLimit := by simp only [jdepthKV] at hdep; omega
    have hjt : d + jdepthKV kvs ≤ nestingLimit := by simp only [jdepthKV] at hdep; omega
    obtain ⟨body, rfl, hchars⟩ := hk
    have hst : SafeTail (w3 ++ [44] ++ (w4 ++ q ++ rest)) := by
      rw [List.append_assoc]; exact safeTail_ws hw3 (Or.inl (by decide))
    have hv' : pv d (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest)))
        = some (v, w3 ++ [44] ++ (w4 ++ q ++ rest)) := ih1 d _ hjv hst
    show pm d ((34 :: (body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pp ++ w3 ++ [44] ++ w4 ++ q) ++ rest)
        = some ((out, v) :: kvs, rest)
    rw [show (34 :: (body ++ [34]) ++ w1 ++ [58] ++ w2 ++ pp ++ w3 ++ [44] ++ w4 ++ q) ++ rest
        = 34 :: ((body ++ [34]) ++ (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest))))))
        from by simp only [List.cons_append, List.append_assoc]]
    refine pm_cons_gen (k := out)
      (r1 := w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest)))))
      (sv := w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest))))
      (r := w3 ++ [44] ++ (w4 ++ q ++ rest)) (sr := w4 ++ q ++ rest) ?_ ?_ ?_ ?_ ?_
    · have := parseStrBody_complete hchars
        (rest := w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest)))))
      rw [show body ++ (34 :: (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest))))))
          = (body ++ [34]) ++ (w1 ++ [58] ++ (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest)))))
          from by simp only [List.append_assoc, List.cons_append, List.nil_append]] at this
      exact this
    · rw [List.append_assoc, skipWs_append_Ws hw1]
      show skipWs (58 :: (w2 ++ (pp ++ (w3 ++ [44] ++ (w4 ++ q ++ rest))))) = _
      rw [skipWs, if_neg (by decide)]
    · rw [skipWs_append_Ws hw2, SValue_skipWs hv]; exact hv'
    · rw [List.append_assoc, skipWs_append_Ws hw3]
      show skipWs (44 :: (w4 ++ q ++ rest)) = 44 :: (w4 ++ q ++ rest)
      rw [skipWs, if_neg (by decide)]
    · rw [List.append_assoc, skipWs_append_Ws hw4, SMembers_skipWs hSM]; exact ih3 d rest hjt

/-! ## Bridge: plain-Option view back to the dependent subtype return type -/

theorem pv_dep {d : Nat} {s : Bytes} {v : JSON} {rest : Bytes}
    (h : pv d s = some (v, rest)) :
    ∃ hh, parseValue d s = some ⟨(v, rest), hh⟩ := by
  unfold pv at h
  cases hp : parseValue d s with
  | none => rw [hp] at h; simp at h
  | some val =>
      obtain ⟨⟨v', rest'⟩, hh'⟩ := val
      rw [hp] at h
      simp only [Option.map_some, Option.some.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨hh', rfl⟩

/-! ## C4 — completeness (the exact Grammar.lean statement) -/

-- @attested-gap2 Cjson.Spec.C4
theorem C4 : ∀ p v rest, SValue p v → DepthOk v →
    (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
    ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩ := by
  intro p v rest hSV hDok hSafe
  have hdep : (0 : Nat) + jdepth v ≤ nestingLimit := by
    simp only [DepthOk] at hDok; omega
  have hpv : pv 0 (p ++ rest) = some (v, rest) := struct_complete hSV 0 rest hdep hSafe
  exact pv_dep hpv

/-! ## Adequacy = C2 (soundness) ∧ C4 (completeness)

    Stated as the conjunction of the exact C2 and C4 statements from `Grammar.lean`.
    This does NOT claim C3 (maximal munch) or C5 (rejection soundness). -/
-- @attested-gap2 Cjson.Spec.adequacy
theorem adequacy :
    (∀ s v, parseDoc s = some v → SDoc s v) ∧
    (∀ p v rest, SValue p v → DepthOk v →
      (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
      ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩) :=
  ⟨fun _ _ h => parseDoc_sound h, C4⟩

end Cjson.Spec
