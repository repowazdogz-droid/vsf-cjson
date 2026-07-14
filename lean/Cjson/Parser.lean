/-
  Cjson.Parser — total recursive-descent parser over `List UInt8`.

  Totality strategy (Phase 4a): NO FUEL. Every parser returns its unconsumed remainder,
  and every *successful* value parse consumes at least one byte. The mutual block then
  terminates on the lexicographic measure

      (remaining bytes, 0 for parseValue / 1 for the element+member loops)

  which Lean's termination checker discharges. There is no fuel parameter to exhaust and
  no fuel bound to declare: totality is structural, not budgeted. The nesting limit
  (1000) is a *semantic* limit from SPEC S2, not a termination device — the parser still
  terminates without it.

  Grammar follows the C oracle, not RFC 8259 (approved Phase 1). Two deliberate
  divergences, also approved: invalid `\uXXXX` hex is REJECTED rather than silently read
  as U+0000 (D-STR-1), and embedded NULs do not truncate strings (D-STR-2).
-/
import Cjson.Basic

namespace Cjson

/-! ## Whitespace (SPEC S1.1) -/

def skipWs : Bytes → Bytes
  | [] => []
  | c :: cs => if isWs c then skipWs cs else c :: cs

theorem skipWs_le (s : Bytes) : (skipWs s).length ≤ s.length := by
  induction s with
  | nil => simp [skipWs]
  | cons c cs ih =>
    simp only [skipWs]
    split
    · exact Nat.le_succ_of_le ih
    · simp

/-! ## Number scanning (SPEC S3.1) -/

def scanDigits : Bytes → (List Nat × Bytes)
  | [] => ([], [])
  | c :: cs =>
    if isDigitB c then
      (digitVal c :: (scanDigits cs).1, (scanDigits cs).2)
    else ([], c :: cs)

theorem scanDigits_le (s : Bytes) : (scanDigits s).2.length ≤ s.length := by
  induction s with
  | nil => simp [scanDigits]
  | cons c cs ih =>
    simp only [scanDigits]
    split
    · exact Nat.le_succ_of_le ih
    · simp

theorem scanDigits_lt {s : Bytes} (h : (scanDigits s).1 ≠ []) :
    (scanDigits s).2.length < s.length := by
  cases s with
  | nil => simp [scanDigits] at h
  | cons c cs =>
    simp only [scanDigits] at h ⊢
    by_cases hd : isDigitB c = true
    · rw [if_pos hd] at h ⊢
      have := scanDigits_le cs
      simp only [List.length_cons]
      omega
    · rw [if_neg hd] at h
      simp at h

/-- Optional leading `-`. -/
def scanSign : Bytes → (Bool × Bytes)
  | c :: cs => if c.toNat == 45 then (true, cs) else (false, c :: cs)
  | [] => (false, [])

theorem scanSign_le (s : Bytes) : (scanSign s).2.length ≤ s.length := by
  cases s with
  | nil => simp [scanSign]
  | cons c cs => simp only [scanSign]; split <;> simp

/-- Optional `.` followed by digits. `1.` is accepted with an empty fraction, matching
    `strtod` (SPEC S3.1). -/
def scanFrac : Bytes → (List Nat × Bytes)
  | c :: cs => if c.toNat == 46 then scanDigits cs else ([], c :: cs)
  | [] => ([], [])

theorem scanFrac_le (s : Bytes) : (scanFrac s).2.length ≤ s.length := by
  cases s with
  | nil => simp [scanFrac]
  | cons c cs =>
    simp only [scanFrac]
    split
    · exact Nat.le_succ_of_le (scanDigits_le cs)
    · simp

theorem scanFrac_lt {s : Bytes} (h : (scanFrac s).1 ≠ []) :
    (scanFrac s).2.length < s.length := by
  cases s with
  | nil => simp [scanFrac] at h
  | cons c cs =>
    simp only [scanFrac] at h ⊢
    by_cases hd : (c.toNat == 46) = true
    · rw [if_pos hd] at h ⊢
      have := scanDigits_le cs
      simp only [List.length_cons]
      omega
    · rw [if_neg hd] at h
      simp at h

def ofDigits (ds : List Nat) : Int :=
  ds.foldl (fun (acc : Int) (d : Nat) => acc * 10 + (d : Int)) (0 : Int)

/-- The digits of an exponent, after the `e`/`E`, with optional sign. `none` means "no
    digits", in which case `scanExp` declines to consume the `e` at all — matching
    `strtod`'s longest-valid-prefix rule, which is why `1e` parses as the number `1`
    leaving `e` behind (SPEC S3.1). -/
def scanExpDigits (s : Bytes) : Option (Int × Bytes) :=
  match s with
  | [] => none
  | sg :: cs' =>
    if sg.toNat == 43 then                            -- '+'
      if (scanDigits cs').1.isEmpty then none
      else some (ofDigits (scanDigits cs').1, (scanDigits cs').2)
    else if sg.toNat == 45 then                       -- '-'
      if (scanDigits cs').1.isEmpty then none
      else some (-(ofDigits (scanDigits cs').1), (scanDigits cs').2)
    else
      if (scanDigits (sg :: cs')).1.isEmpty then none
      else some (ofDigits (scanDigits (sg :: cs')).1, (scanDigits (sg :: cs')).2)

theorem scanExpDigits_le {s : Bytes} {e : Int} {r : Bytes}
    (h : scanExpDigits s = some (e, r)) : r.length ≤ s.length := by
  cases s with
  | nil => simp [scanExpDigits] at h
  | cons sg cs' =>
    have hcs := scanDigits_le cs'
    have hsg := scanDigits_le (sg :: cs')
    simp only [scanExpDigits] at h
    split at h
    · split at h
      · exact absurd h (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨-, hr⟩ := h; subst hr
        simp only [List.length_cons]; omega
    · split at h
      · split at h
        · exact absurd h (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hr⟩ := h; subst hr
          simp only [List.length_cons]; omega
      · split at h
        · exact absurd h (by simp)
        · simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨-, hr⟩ := h; subst hr
          exact hsg

def scanExp (s : Bytes) : (Int × Bytes) :=
  match s with
  | [] => (0, [])
  | c :: cs =>
    if c.toNat == 101 || c.toNat == 69 then          -- 'e' | 'E'
      match scanExpDigits cs with
      | some (e, r) => (e, r)
      | none => (0, c :: cs)
    else (0, c :: cs)

theorem scanExp_le (s : Bytes) : (scanExp s).2.length ≤ s.length := by
  cases s with
  | nil => simp [scanExp]
  | cons c cs =>
    simp only [scanExp]
    split
    · cases hx : scanExpDigits cs with
      | none => simp [hx]
      | some p =>
        obtain ⟨e, r⟩ := p
        have := scanExpDigits_le hx
        simp only [hx, List.length_cons]
        omega
    · simp

/-- Normalise raw scanned digits into a canonical `JNum` (SPEC S3 / Basic.lean).
    Strips leading zeros, then trailing zeros while incrementing the exponent. An
    all-zero mantissa collapses to `JNum.zero`, which is why `-0` normalises to `0` —
    agreeing with the oracle, and semantically right for an exact number. -/
def normNum (neg : Bool) (ds : List Nat) (e : Int) : JNum :=
  let ds1 := ds.dropWhile (· == 0)
  let ds2 := (ds1.reverse.dropWhile (· == 0)).reverse
  if ds2.isEmpty then JNum.zero
  else ⟨neg, ds2, e + ((ds1.length - ds2.length : Nat) : Int)⟩

/-- Full number. The caller must already have checked the SPEC S2 dispatch gate (first
    byte is `-` or a digit); this is what makes `+1` and `.5` parse errors even though
    the scanner below would accept them. -/
def scanNumber (s : Bytes) : Option (JNum × Bytes) :=
  let sg := scanSign s
  let ds := scanDigits sg.2
  let fr := scanFrac ds.2
  if ds.1.isEmpty && fr.1.isEmpty then none
  else
    let ex := scanExp fr.2
    some (normNum sg.1 (ds.1 ++ fr.1) (ex.1 - (fr.1.length : Int)), ex.2)

theorem scanNumber_lt {s : Bytes} {n : JNum} {r : Bytes}
    (h : scanNumber s = some (n, r)) : r.length < s.length := by
  simp only [scanNumber] at h
  split at h
  · exact absurd h (by simp)
  · next hne =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, hr⟩ := h
    subst hr
    have hsg := scanSign_le s
    have hfr := scanFrac_le (scanDigits (scanSign s).2).2
    have hex := scanExp_le (scanFrac (scanDigits (scanSign s).2).2).2
    -- the mantissa is non-empty, so either the int part or the fraction consumed a byte
    rcases Classical.em ((scanDigits (scanSign s).2).1 = []) with hd | hd
    · -- int part empty ⇒ fraction non-empty ⇒ scanFrac strictly consumed
      have hf : (scanFrac (scanDigits (scanSign s).2).2).1 ≠ [] := by
        intro hf0
        exact hne (by simp [hd, hf0])
      have := scanFrac_lt hf
      have hdle := scanDigits_le (scanSign s).2
      omega
    · have := scanDigits_lt hd
      omega

/-! ## T2 — the parser only ever BUILDS canonical numbers

Without this, T1's `Canonical v` hypothesis would be an unchecked promise. -/

theorem head?_dropWhile {p : Nat → Bool} {l : List Nat} {x : Nat}
    (h : (l.dropWhile p).head? = some x) : p x = false := by
  induction l with
  | nil => simp [List.dropWhile] at h
  | cons a as ih =>
    simp only [List.dropWhile] at h
    split at h
    · exact ih h
    · next hp => simp only [List.head?_cons, Option.some.injEq] at h
                 subst h
                 simpa using hp

/-- Dropping a PREFIX cannot change the last element. -/
theorem getLast?_dropWhile {p : Nat → Bool} {l : List Nat} (h : l.dropWhile p ≠ []) :
    (l.dropWhile p).getLast? = l.getLast? := by
  induction l with
  | nil => simp [List.dropWhile] at h
  | cons a as ih =>
    simp only [List.dropWhile] at h ⊢
    split
    · next hp =>
        rw [ih (by simpa [List.dropWhile, hp] using h)]
        cases as with
        | nil => simp [List.dropWhile] at h; simp [List.dropWhile, hp] at h
        | cons b bs => simp
    · rfl

theorem mem_dropWhile {p : Nat → Bool} {l : List Nat} {x : Nat}
    (h : x ∈ l.dropWhile p) : x ∈ l := by
  induction l with
  | nil => simp [List.dropWhile] at h
  | cons a as ih =>
    simp only [List.dropWhile] at h
    split at h
    · exact List.mem_cons_of_mem a (ih h)
    · exact h

/-- **T2 (numbers).** Every number the parser builds is canonical. -/
theorem normNum_canonical (neg : Bool) (ds : List Nat) (e : Int)
    (h10 : ∀ d ∈ ds, d < 10) : JNum.Canonical (normNum neg ds e) := by
  simp only [normNum]
  split
  · next hz => exact Or.inl ⟨rfl, rfl, rfl⟩
  · next hz =>
      have hne : ((ds.dropWhile (· == 0)).reverse.dropWhile (· == 0)).reverse ≠ [] := by
        intro hcon; rw [hcon] at hz; simp at hz
      refine Or.inr ⟨hne, ?_, ?_, ?_⟩
      · -- no leading zero: the head survives from `ds.dropWhile`, whose head is not 0
        intro hcon
        have hrev : ((ds.dropWhile (· == 0)).reverse.dropWhile (· == 0)).reverse.head?
            = ((ds.dropWhile (· == 0)).reverse.dropWhile (· == 0)).getLast? := by
          rw [← List.getLast?_reverse, List.reverse_reverse]
        rw [hrev] at hcon
        rw [getLast?_dropWhile (by
              intro hcon2
              rw [hcon2] at hne
              simp at hne)] at hcon
        rw [List.getLast?_reverse] at hcon
        exact absurd (head?_dropWhile hcon) (by simp)
      · -- no trailing zero: guaranteed by the reversed `dropWhile`
        intro hcon
        rw [← List.head?_reverse, List.reverse_reverse] at hcon
        exact absurd (head?_dropWhile hcon) (by simp)
      · intro d hd
        rw [List.mem_reverse] at hd
        exact h10 d (mem_dropWhile (List.mem_reverse.mp (mem_dropWhile hd)))


theorem scanDigits_lt10 (s : Bytes) : ∀ d ∈ (scanDigits s).1, d < 10 := by
  induction s with
  | nil => simp [scanDigits]
  | cons c cs ih =>
    simp only [scanDigits]
    split
    · next hd =>
        intro d hmem
        rcases List.mem_cons.mp hmem with h | h
        · subst h
          unfold isDigitB at hd
          simp only [Bool.and_eq_true, decide_eq_true_eq] at hd
          unfold digitVal
          omega
        · exact ih d h
    · simp

/-- **T2 (scanner).** Any number the scanner returns is canonical. -/
theorem scanNumber_canonical {s : Bytes} {n : JNum} {r : Bytes}
    (h : scanNumber s = some (n, r)) : JNum.Canonical n := by
  simp only [scanNumber] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    refine normNum_canonical _ _ _ ?_
    intro d hd
    rcases List.mem_append.mp hd with hm | hm
    · exact scanDigits_lt10 _ d hm
    · -- the fractional digits also come from `scanDigits`
      unfold scanFrac at hm
      split at hm
      · split at hm
        · exact scanDigits_lt10 _ d hm
        · simp at hm
      · simp at hm


/-! ## Strings (SPEC S4) -/

/-- UTF-8 encode a scalar value. -/
def utf8Enc (cp : Nat) : Bytes :=
  if cp < 0x80 then
    [UInt8.ofNat cp]
  else if cp < 0x800 then
    [UInt8.ofNat (0xC0 ||| (cp >>> 6)),
     UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]
  else if cp < 0x10000 then
    [UInt8.ofNat (0xE0 ||| (cp >>> 12)),
     UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]
  else
    [UInt8.ofNat (0xF0 ||| (cp >>> 18)),
     UInt8.ofNat (0x80 ||| ((cp >>> 12) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]

def hex4 (a b c d : UInt8) : Option Nat := do
  let a' ← hexVal? a
  let b' ← hexVal? b
  let c' ← hexVal? c
  let d' ← hexVal? d
  some (a' * 4096 + b' * 256 + c' * 16 + d')

def isHighSur (n : Nat) : Bool := 0xD800 ≤ n && n ≤ 0xDBFF
def isLowSur  (n : Nat) : Bool := 0xDC00 ≤ n && n ≤ 0xDFFF

/-- Parse the body of a string, i.e. everything after the opening quote. Returns the
    decoded bytes and the remainder after the closing quote.

    All recursion is on explicit structural sub-tails, so this is structurally recursive
    and needs no measure. -/
def parseStrBody : Bytes → Option (Bytes × Bytes)
  | [] => none
  -- closing quote
  | 34 :: r => some ([], r)
  -- single-character escapes (SPEC S4.1)
  | 92 :: 34  :: r => match parseStrBody r with | some (v, r') => some (34 :: v, r') | none => none
  | 92 :: 92  :: r => match parseStrBody r with | some (v, r') => some (92 :: v, r') | none => none
  | 92 :: 47  :: r => match parseStrBody r with | some (v, r') => some (47 :: v, r') | none => none
  | 92 :: 98  :: r => match parseStrBody r with | some (v, r') => some (8  :: v, r') | none => none
  | 92 :: 102 :: r => match parseStrBody r with | some (v, r') => some (12 :: v, r') | none => none
  | 92 :: 110 :: r => match parseStrBody r with | some (v, r') => some (10 :: v, r') | none => none
  | 92 :: 114 :: r => match parseStrBody r with | some (v, r') => some (13 :: v, r') | none => none
  | 92 :: 116 :: r => match parseStrBody r with | some (v, r') => some (9  :: v, r') | none => none
  -- \uXXXX
  | 92 :: 117 :: h1 :: h2 :: h3 :: h4 :: r =>
    match hex4 h1 h2 h3 h4 with
    | none => none                       -- D-STR-1: REJECT (cJSON accepts, yields U+0000)
    | some cp =>
      if isLowSur cp then none           -- lone low surrogate
      else if isHighSur cp then
        match r with
        | 92 :: 117 :: g1 :: g2 :: g3 :: g4 :: r2 =>
          match hex4 g1 g2 g3 g4 with
          | none => none
          | some cp2 =>
            if isLowSur cp2 then
              match parseStrBody r2 with
              | some (v, r') =>
                some (utf8Enc (0x10000 + (((cp &&& 0x3FF) <<< 10) ||| (cp2 &&& 0x3FF))) ++ v, r')
              | none => none
            else none
        | _ => none                      -- unpaired high surrogate
      else
        match parseStrBody r with
        | some (v, r') => some (utf8Enc cp ++ v, r')
        | none => none
  -- any other escape is an error (SPEC S4.1)
  | 92 :: _ :: _ => none
  | 92 :: [] => none
  -- ordinary byte: copied through verbatim, including raw control bytes (SPEC S4.2) and
  -- bytes ≥ 0x80 with no UTF-8 validation (SPEC S1.3)
  | c :: r => match parseStrBody r with | some (v, r') => some (c :: v, r') | none => none

/-- Non-strict is all we need: `parseValue` has already consumed the opening quote, so
    `≤` on the body gives `<` on the whole string. -/
theorem parseStrBody_le {s : Bytes} {v r : Bytes} (h : parseStrBody s = some (v, r)) :
    r.length ≤ s.length := by
  induction s using parseStrBody.induct generalizing v r <;>
    simp_all [parseStrBody] <;> omega


/-! ## Values, arrays, objects

`Res α s` is a parse result that *carries the proof it consumed at least one byte*.
Threading that proof through the subtype is what lets the mutual block below terminate
with no fuel: the recursive calls have the decrease in scope at the call site. It also
means the Phase-4a progress property is not a separate theorem — it is in the type. -/

/-- A parse result carrying TWO proofs: that it consumed at least one byte (which is what
    gives the mutual block below its fuel-free termination), and that the value it built is
    CANONICAL (which is what closes GAP-1).

    Canonicity is a `Prop`, so it is erased at runtime: the emitted bytes are unchanged.
    Discharging it at the ~8 construction sites here is what lets us avoid a 26-case mutual
    induction over `parseValue.induct` after the fact. -/
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }

mutual

/-- A single JSON value. `depth` is the SPEC S2 nesting counter (limit 1000). -/
def parseValue (depth : Nat) (s : List UInt8) :
    Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s :=
  match s with
  | [] => none
  | 110 :: 117 :: 108 :: 108 :: r =>
      some ⟨(.null, r), ⟨(by simp; omega), ⟨.null, by simp [jdepth]⟩⟩⟩
  | 116 :: 114 :: 117 :: 101 :: r =>
      some ⟨(.bool true, r), ⟨(by simp; omega), ⟨.bool true, by simp [jdepth]⟩⟩⟩
  | 102 :: 97 :: 108 :: 115 :: 101 :: r =>
      some ⟨(.bool false, r), ⟨(by simp; omega), ⟨.bool false, by simp [jdepth]⟩⟩⟩
  | 34 :: r =>                                                              -- '"'
    match hs : parseStrBody r with
    | none => none
    | some (v, r') => some ⟨(.str v, r'),
        ⟨(by have := parseStrBody_le hs; simp; omega), ⟨.str v, by simp [jdepth]⟩⟩⟩
  | 91 :: r =>                                                              -- '['
    if hd : depth ≥ nestingLimit then none
    else
      match hw : skipWs r with
      | 93 :: r' => some ⟨(.arr [], r'),
          ⟨(by have hle := skipWs_le r; rw [hw] at hle; simp at hle ⊢; omega),
           ⟨.arr [] .nil, by simp only [nestingLimit] at hd ⊢; simp only [jdepth, jdepthL]; omega⟩⟩⟩
      | _ =>
        match parseElems (depth + 1) (skipWs r) with
        | none => none
        | some ⟨(xs, r'), hr⟩ => some ⟨(.arr xs, r'),
            ⟨(by have hle := skipWs_le r; have h := hr.1; simp at h ⊢; omega),
             ⟨.arr xs hr.2.1, by have := hr.2.2; simp only [nestingLimit] at hd this ⊢; simp only [jdepth]; omega⟩⟩⟩
  | 123 :: r =>                                                             -- '{'
    if hd : depth ≥ nestingLimit then none
    else
      match hw : skipWs r with
      | 125 :: r' => some ⟨(.obj [], r'),
          ⟨(by have hle := skipWs_le r; rw [hw] at hle; simp at hle ⊢; omega),
           ⟨.obj [] .nil, by simp only [nestingLimit] at hd ⊢; simp only [jdepth, jdepthKV]; omega⟩⟩⟩
      | _ =>
        match parseMembers (depth + 1) (skipWs r) with
        | none => none
        | some ⟨(kvs, r'), hr⟩ => some ⟨(.obj kvs, r'),
            ⟨(by have hle := skipWs_le r; have h := hr.1; simp at h ⊢; omega),
             ⟨.obj kvs hr.2.1, by have := hr.2.2; simp only [nestingLimit] at hd this ⊢; simp only [jdepth]; omega⟩⟩⟩
  | c :: cs =>
    -- SPEC S2 dispatch gate: a number may only start with '-' or a digit. This is why
    -- `+1` and `.5` are rejected even though `scanNumber` would accept them.
    if c.toNat == 45 || isDigitB c then
      match hn : scanNumber (c :: cs) with
      | none => none
      | some (n, r) => some ⟨(.num n, r),
          ⟨scanNumber_lt hn, ⟨.num n (scanNumber_canonical hn), by simp [jdepth]⟩⟩⟩
    else none
termination_by (s.length, 0)
decreasing_by
  · have := skipWs_le r
    exact Prod.Lex.left _ _ (by simp only [List.length_cons]; omega)
  · have := skipWs_le r
    exact Prod.Lex.left _ _ (by simp only [List.length_cons]; omega)

/-- `value (ws ',' ws value)* ws ']'` — the non-empty array tail. -/
def parseElems (depth : Nat) (s : List UInt8) :
    Res (List JSON) (fun xs => JSON.CanonicalL xs ∧ jdepthL xs ≤ nestingLimit - depth) s :=
  match parseValue depth s with
  | none => none
  | some ⟨(v, r), hr⟩ =>
    match hw : skipWs r with
    | 44 :: r2 =>                                                           -- ','
      match parseElems depth (skipWs r2) with
      | none => none
      | some ⟨(vs, r3), hr3⟩ => some ⟨(v :: vs, r3),
          ⟨(by have h1 := skipWs_le r; have h2 := skipWs_le r2
               have ha := hr.1; have hb := hr3.1
               rw [hw] at h1; simp at h1 ha hb ⊢; omega),
           ⟨.cons v vs hr.2.1 hr3.2.1,
            by have ha := hr.2.2; have hb := hr3.2.2; simp only [nestingLimit] at ha hb ⊢; simp only [jdepthL]; omega⟩⟩⟩
    | 93 :: r2 => some ⟨([v], r2),                                          -- ']'
        ⟨(by have h1 := skipWs_le r; have ha := hr.1
             rw [hw] at h1; simp at h1 ha ⊢; omega),
         ⟨.cons v [] hr.2.1 .nil,
          by have ha := hr.2.2; simp only [nestingLimit] at ha ⊢; simp only [jdepthL]; omega⟩⟩⟩
    | _ => none
termination_by (s.length, 1)
decreasing_by
  · exact Prod.Lex.right _ (by omega)
  · have h1 := skipWs_le r; have h2 := skipWs_le r2; have ha := hr.1
    rw [hw] at h1; simp at h1 ha
    exact Prod.Lex.left _ _ (by omega)

/-- `member (ws ',' ws member)* ws '}'` — the non-empty object tail.
    Duplicate keys are kept, in source order (SPEC S2). -/
def parseMembers (depth : Nat) (s : List UInt8) :
    Res (List (List UInt8 × JSON))
      (fun kvs => JSON.CanonicalKV kvs ∧ jdepthKV kvs ≤ nestingLimit - depth) s :=
  match s with
  | 34 :: r =>
    match hk : parseStrBody r with
    | none => none
    | some (k, r1) =>
      match hw1 : skipWs r1 with
      | 58 :: r2 =>                                                         -- ':'
        match parseValue depth (skipWs r2) with
        | none => none
        | some ⟨(v, r3), hr3⟩ =>
          match hw2 : skipWs r3 with
          | 44 :: r4 =>                                                     -- ','
            match parseMembers depth (skipWs r4) with
            | none => none
            | some ⟨(kvs, r5), hr5⟩ => some ⟨((k, v) :: kvs, r5),
                ⟨(by have hb := parseStrBody_le hk
                     have h1 := skipWs_le r1; have h2 := skipWs_le r2
                     have h3 := skipWs_le r3; have h4 := skipWs_le r4
                     have ha := hr3.1; have hc := hr5.1
                     rw [hw1] at h1; rw [hw2] at h3
                     simp at h1 h3 ha hc ⊢; omega),
                 ⟨.cons k v kvs hr3.2.1 hr5.2.1,
                  by have ha := hr3.2.2; have hb := hr5.2.2; simp only [nestingLimit] at ha hb ⊢; simp only [jdepthKV]; omega⟩⟩⟩
          | 125 :: r4 => some ⟨([(k, v)], r4),                              -- '}'
              ⟨(by have hb := parseStrBody_le hk
                   have h1 := skipWs_le r1; have h2 := skipWs_le r2
                   have h3 := skipWs_le r3
                   have ha := hr3.1
                   rw [hw1] at h1; rw [hw2] at h3
                   simp at h1 h3 ha ⊢; omega),
               ⟨.cons k v [] hr3.2.1 .nil,
                by have ha := hr3.2.2; simp only [nestingLimit] at ha ⊢; simp only [jdepthKV]; omega⟩⟩⟩
          | _ => none
      | _ => none
  | _ => none
termination_by (s.length, 1)
decreasing_by
  · -- parseValue on (skipWs r2), strictly inside the key/colon
    have hb := parseStrBody_le hk
    have h1 := skipWs_le r1; have h2 := skipWs_le r2
    rw [hw1] at h1; simp only [List.length_cons] at h1
    exact Prod.Lex.left _ _ (by simp only [List.length_cons]; omega)
  · -- recursive parseMembers on (skipWs r4)
    have hb := parseStrBody_le hk
    have h1 := skipWs_le r1; have h2 := skipWs_le r2
    have h3 := skipWs_le r3; have h4 := skipWs_le r4
    have ha := hr3.1
    rw [hw1] at h1; rw [hw2] at h3
    simp at h1 h3 ha
    exact Prod.Lex.left _ _ (by simp only [List.length_cons]; omega)

end


/-! ## Document (SPEC S5) -/

/-- Skip a leading UTF-8 BOM. -/
def skipBom : Bytes → Bytes
  | 0xEF :: 0xBB :: 0xBF :: r => r
  | s => s

/-- Top-level parse. Per SPEC S5.1 (cJSON's `require_null_terminated = 0`) **trailing
    bytes after a complete value are ignored**, not an error. -/
def parseDoc (s : Bytes) : Option JSON :=
  match parseValue 0 (skipWs (skipBom s)) with
  | none => none
  | some ⟨(v, _), _⟩ => some v

/-- **T2 (structural) — GAP-1 CLOSED.** Every value the parser produces is canonical.
    This is not a separate induction: the parser's return type carries the proof, so this
    theorem is just the projection. -/
theorem parseDoc_canonical {s : Bytes} {v : JSON} (h : parseDoc s = some v) :
    JSON.Canonical v := by
  unfold parseDoc at h
  split at h
  · exact absurd h (by simp)
  · next v' r' hp hn =>
      simp only [Option.some.injEq] at h
      subst h
      exact hp.2.1

end Cjson
