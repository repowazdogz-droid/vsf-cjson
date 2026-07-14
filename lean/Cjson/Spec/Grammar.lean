/-
  GAP-2, Phase 1 — a DECLARATIVE grammar for the language SPEC.md describes.

  This file is written from SPEC.md (which was itself written before the Lean port and
  verified clause-by-clause against the compiled C oracle). It deliberately does NOT reuse
  `Cjson.Parser`: no `normNum`, no `scanNumber`, no `parseStrBody`. It imports only the AST
  (`Cjson.Basic`) so that the two sides can be compared at all.

  Why a RELATION and not a function. A recursive-descent recogniser written from the spec
  would be a *second implementation*, and "the parser agrees with my other parser" is a
  differential test, not a soundness theorem. `SValue : Bytes → JSON → Prop` instead relates
  text to MEANING without committing to an algorithm, so a soundness theorem against it says
  something the parser does not already say about itself.

  NOTHING IS PROVED HERE. Candidate theorem statements appear at the bottom as `Prop`s
  (they elaborate; they are not asserted). Zero `sorry`, zero axioms.
-/
import Cjson.Basic
-- `Cjson.Parser` is imported ONLY so the candidate theorems at the bottom can MENTION
-- `parseDoc`/`parseValue`. No DEFINITION in this file uses the parser: the grammar is written
-- from SPEC.md. Enforced mechanically by harness/gap2/check_independence.py.
import Cjson.Parser

namespace Cjson.Spec

open Cjson

/-! ## Lexical (SPEC §S1) -/

/-- §S1.1: whitespace is ANY byte ≤ 32 — including NUL and every C0 control byte. -/
def IsWs (c : UInt8) : Prop := c.toNat ≤ 32

def Ws (s : Bytes) : Prop := ∀ c ∈ s, IsWs c

/-- §S1.2: an optional leading UTF-8 BOM. -/
def Bom (s : Bytes) : Prop := s = [] ∨ s = [0xEF, 0xBB, 0xBF]

/-! ## Digits -/

inductive Digits : Bytes → List Nat → Prop where
  | nil  : Digits [] []
  | cons : ∀ {c d bs ds}, isDigitB c = true → digitVal c = d → Digits bs ds →
           Digits (c :: bs) (d :: ds)

/-- Denotation of a raw digit string as a natural number. This is a MEANING function, not a
    parser: it is what "3","1","4" denotes, nothing about how bytes are consumed. -/
def natOf : List Nat → Nat
  | []      => 0
  | d :: ds => d * 10 ^ ds.length + natOf ds

/-! ## Numbers (SPEC §S3)

    §S3.1: cJSON does not implement the RFC number grammar. It takes the longest prefix that
    C `strtod` accepts, over the charset `[0-9 + - e E .]`. The token grammar is therefore

        num := '-'? ( digit+ ('.' digit*)?  |  '.' digit+ ) exp?
        exp := ('e'|'E') ('+'|'-')? digit+

    with at least one mantissa digit, and the exponent consumed ONLY if it has ≥1 digit
    (which is why `1e` denotes 1, leaving `e`).

    §S2: a value may only START a number with '-' or a digit. This dispatch gate is what
    rejects `+1` and `.5` even though the token grammar above would accept them. It is a
    property of the VALUE position, so it lives in `SValue`, not here. -/

/-- `ExpPart p e` : `p` is an exponent suffix denoting `e`. -/
inductive ExpPart : Bytes → Int → Prop where
  | none  : ExpPart [] 0
  | plain : ∀ {c bs ds}, (c = 101 ∨ c = 69) → Digits bs ds → ds ≠ [] →
            ExpPart (c :: bs) (natOf ds)
  | pos   : ∀ {c bs ds}, (c = 101 ∨ c = 69) → Digits bs ds → ds ≠ [] →
            ExpPart (c :: 43 :: bs) (natOf ds)
  | neg   : ∀ {c bs ds}, (c = 101 ∨ c = 69) → Digits bs ds → ds ≠ [] →
            ExpPart (c :: 45 :: bs) (-(natOf ds))

/-- Two exact decimals `± m·10^e` denote the same number. Written as an EQUIVALENCE on the
    raw triple, so the grammar never has to mention the parser's normaliser. -/
def SameNum (neg₁ : Bool) (m₁ : Nat) (e₁ : Int) (neg₂ : Bool) (m₂ : Nat) (e₂ : Int) : Prop :=
  (m₁ = 0 ∧ m₂ = 0)                                    -- ±0 · 10^anything is 0, unsigned
  ∨ (neg₁ = neg₂ ∧ m₁ ≠ 0 ∧ m₂ ≠ 0 ∧
      ∃ k : Nat, (m₁ = m₂ * 10 ^ k ∧ e₁ + (k : Int) = e₂)
               ∨ (m₂ = m₁ * 10 ^ k ∧ e₂ + (k : Int) = e₁))

/-- The value a `JNum` denotes, as a raw triple. -/
def numDenote (n : JNum) : Bool × Nat × Int := (n.neg, natOf n.digits, n.exp)

/-- `SNumTok p n` : `p` is a number TOKEN (no dispatch gate — see `SValue`) denoting `n`.
    `n` is additionally required to be CANONICAL, so the relation pins a unique AST node. -/
inductive SNumTok : Bytes → JNum → Prop where
  | mk : ∀ {sgn : Bytes} {neg : Bool} {ip fp ep : Bytes} {ids fds : List Nat} {e : Int}
           {dot : Bytes} {n : JNum},
      (sgn = [] ∧ neg = false) ∨ (sgn = [45] ∧ neg = true) →
      Digits ip ids →
      -- optional fractional part: '.' then zero-or-more digits
      ((dot = [] ∧ fp = [] ∧ fds = []) ∨ (dot = [46] ∧ Digits fp fds)) →
      (ids ++ fds ≠ []) →                                   -- at least one mantissa digit
      ExpPart ep e →
      JNum.Canonical n →
      SameNum neg (natOf (ids ++ fds)) (e - (fds.length : Int))
              n.neg (natOf n.digits) n.exp →
      SNumTok (sgn ++ ip ++ dot ++ fp ++ ep) n

/-! ## Strings (SPEC §S4)

    §S4.1 escapes: `\" \\ \/ \b \f \n \r \t \uXXXX`.
    §S4.2 unescaped control bytes ARE accepted (RFC forbids them).
    §S1.3 no UTF-8 validation: bytes ≥ 0x80 pass through unexamined.
    §S4.3 DELIBERATE DIVERGENCE (D-STR-1): `\uXXXX` requires four VALID hex digits. cJSON
          accepts anything and yields U+0000; the Lean port rejects. The grammar follows the
          Lean port, and this is logged as an intentional extension, not a quirk we inherited.
    §S4.5 DELIBERATE DIVERGENCE (D-STR-2): an embedded NUL does NOT truncate. -/

/-- Bytes that may appear unescaped inside a string: anything but `"` and `\`. Note this
    ADMITS raw control bytes and invalid UTF-8, per §S4.2 / §S1.3. -/
def PlainStrByte (c : UInt8) : Prop := c ≠ 34 ∧ c ≠ 92

def IsHex (c : UInt8) : Prop := (hexVal? c).isSome

/-- UTF-8 encoding of a scalar value, as a MEANING (what the escape denotes). -/
def enc (cp : Nat) : Bytes :=
  if cp < 0x80 then [UInt8.ofNat cp]
  else if cp < 0x800 then
    [UInt8.ofNat (0xC0 ||| (cp >>> 6)), UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]
  else if cp < 0x10000 then
    [UInt8.ofNat (0xE0 ||| (cp >>> 12)), UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]
  else
    [UInt8.ofNat (0xF0 ||| (cp >>> 18)), UInt8.ofNat (0x80 ||| ((cp >>> 12) &&& 0x3F)),
     UInt8.ofNat (0x80 ||| ((cp >>> 6) &&& 0x3F)), UInt8.ofNat (0x80 ||| (cp &&& 0x3F))]

def hex4v (a b c d : UInt8) : Nat :=
  ((hexVal? a).getD 0) * 4096 + ((hexVal? b).getD 0) * 256
    + ((hexVal? c).getD 0) * 16 + ((hexVal? d).getD 0)

/-- `SChars p out` : `p` is the body of a string literal (between the quotes) denoting the
    byte string `out`. -/
inductive SChars : Bytes → Bytes → Prop where
  | nil   : SChars [] []
  | plain : ∀ {c p out}, PlainStrByte c → SChars p out → SChars (c :: p) (c :: out)
  | esc   : ∀ {c d p out}, SChars p out →
              ((c = 34 ∧ d = 34) ∨ (c = 92 ∧ d = 92) ∨ (c = 47 ∧ d = 47) ∨
               (c = 98 ∧ d = 8) ∨ (c = 102 ∧ d = 12) ∨ (c = 110 ∧ d = 10) ∨
               (c = 114 ∧ d = 13) ∨ (c = 116 ∧ d = 9)) →
              SChars (92 :: c :: p) (d :: out)
  -- \uXXXX, four VALID hex digits, not a surrogate half (D-STR-1: cJSON accepts junk here)
  | uni   : ∀ {h1 h2 h3 h4 p out}, IsHex h1 → IsHex h2 → IsHex h3 → IsHex h4 →
              ¬ (0xD800 ≤ hex4v h1 h2 h3 h4 ∧ hex4v h1 h2 h3 h4 ≤ 0xDFFF) →
              SChars p out →
              SChars (92 :: 117 :: h1 :: h2 :: h3 :: h4 :: p) (enc (hex4v h1 h2 h3 h4) ++ out)
  -- a surrogate PAIR, and only a pair (§S4.4)
  | pair  : ∀ {h1 h2 h3 h4 g1 g2 g3 g4 p out},
              IsHex h1 → IsHex h2 → IsHex h3 → IsHex h4 →
              IsHex g1 → IsHex g2 → IsHex g3 → IsHex g4 →
              (0xD800 ≤ hex4v h1 h2 h3 h4 ∧ hex4v h1 h2 h3 h4 ≤ 0xDBFF) →
              (0xDC00 ≤ hex4v g1 g2 g3 g4 ∧ hex4v g1 g2 g3 g4 ≤ 0xDFFF) →
              SChars p out →
              SChars (92 :: 117 :: h1 :: h2 :: h3 :: h4 ::
                      92 :: 117 :: g1 :: g2 :: g3 :: g4 :: p)
                     (enc (0x10000 + (((hex4v h1 h2 h3 h4 &&& 0x3FF) <<< 10)
                                       ||| (hex4v g1 g2 g3 g4 &&& 0x3FF))) ++ out)

def SStr (p : Bytes) (out : Bytes) : Prop :=
  ∃ body, p = 34 :: (body ++ [34]) ∧ SChars body out

/-! ## Values, arrays, objects (SPEC §S2)

    Duplicate keys are PRESERVED in source order (§S2) — the grammar therefore relates a
    document to a LIST of pairs, not to a map. -/

mutual
  inductive SValue : Bytes → JSON → Prop where
    | null  : SValue [110, 117, 108, 108] .null
    | true_ : SValue [116, 114, 117, 101] (.bool true)
    | false_: SValue [102, 97, 108, 115, 101] (.bool false)
    | str   : ∀ {p out}, SStr p out → SValue p (.str out)
    -- §S2 DISPATCH GATE: a number may only begin with '-' or a digit. This is why `+1` and
    -- `.5` are rejected at value position although `SNumTok` would accept them.
    | num   : ∀ {c p n}, (c = 45 ∨ isDigitB c = true) → SNumTok (c :: p) n →
              SValue (c :: p) (.num n)
    | arr0  : ∀ {w}, Ws w → SValue (91 :: (w ++ [93])) (.arr [])
    | arr   : ∀ {w p xs}, Ws w → SElems p xs → SValue (91 :: (w ++ p)) (.arr xs)
    | obj0  : ∀ {w}, Ws w → SValue (123 :: (w ++ [125])) (.obj [])
    | obj   : ∀ {w p kvs}, Ws w → SMembers p kvs → SValue (123 :: (w ++ p)) (.obj kvs)

  /-- `value (ws ',' ws value)* ws ']'` — the non-empty array tail, INCLUDING the `]`. -/
  inductive SElems : Bytes → List JSON → Prop where
    | last : ∀ {p v w}, SValue p v → Ws w → SElems (p ++ w ++ [93]) [v]
    | cons : ∀ {p v w1 w2 q vs}, SValue p v → Ws w1 → Ws w2 → SElems q vs →
             SElems (p ++ w1 ++ [44] ++ w2 ++ q) (v :: vs)

  /-- `member (ws ',' ws member)* ws '}'` — the non-empty object tail, INCLUDING the `}`. -/
  inductive SMembers : Bytes → List (Bytes × JSON) → Prop where
    | last : ∀ {k out w1 w2 p v w3}, SStr k out → Ws w1 → Ws w2 → SValue p v → Ws w3 →
             SMembers (k ++ w1 ++ [58] ++ w2 ++ p ++ w3 ++ [125]) [(out, v)]
    | cons : ∀ {k out w1 w2 p v w3 w4 q kvs},
             SStr k out → Ws w1 → Ws w2 → SValue p v → Ws w3 → Ws w4 → SMembers q kvs →
             SMembers (k ++ w1 ++ [58] ++ w2 ++ p ++ w3 ++ [44] ++ w4 ++ q) ((out, v) :: kvs)
end

/-! ## The document level (SPEC §S5)

    §S5.1: **trailing bytes after a complete top-level value are ACCEPTED** (`cJSON_Parse`
    runs with `require_null_terminated = 0`). This is the single most consequential clause in
    the whole spec, and it is what makes the accept-set an EXISTENTIAL over prefixes. -/

/-- The nesting limit (§S2). A *semantic* bound, enforced by both implementations. -/
def DepthOk (v : JSON) : Prop := jdepth v ≤ nestingLimit

/-- `SDoc s v` : the spec accepts `s` as denoting `v`.

    Note the shape forced on us by §S5.1: `s` need only have a grammatical PREFIX (after an
    optional BOM and leading whitespace). Everything after it is ignored. -/
def SDoc (s : Bytes) (v : JSON) : Prop :=
  ∃ bom w p rest, Bom bom ∧ Ws w ∧ SValue p v ∧ DepthOk v ∧ s = bom ++ w ++ p ++ rest

def SAccepts (s : Bytes) : Prop := ∃ v, SDoc s v

/-! ## CANDIDATE THEOREMS — stated, NOT proved

    Each elaborates as a `Prop`. Nothing below is asserted; there is no `sorry` and no axiom.
    See GAP2.md for which of these is the right theorem and why. -/

/-- **C1 — naive soundness.** The theorem as literally posed in the mission. -/
example : Prop := ∀ s v, parseDoc s = some v → SAccepts s

/-- **C2 — value soundness.** Strictly stronger and, we argue, the RIGHT statement: the
    parser does not merely accept a member of the language, it returns the value the grammar
    assigns to the prefix it consumed. C1 follows from C2. -/
example : Prop := ∀ s v, parseDoc s = some v → SDoc s v

/-- **C3 — maximal munch.** C2 leaves the parser free to pick ANY grammatical prefix. The
    real parser takes the longest (`1.2.3` ⇒ `1.2`, not `1`). Stating this needs the consumed
    prefix, which `parseDoc` discards — so it must be phrased on `parseValue`. -/
example : Prop :=
  ∀ d s v r h, parseValue d s = some ⟨(v, r), h⟩ →
    ∃ p, s = p ++ r ∧ SValue p v ∧
         (∀ p' v' r', s = p' ++ r' → SValue p' v' → p'.length ≤ p.length)

/-- **C4 — completeness (the converse).** Soundness alone is nearly vacuous for a parser that
    accepts trailing garbage; completeness is where the content is. Note the side condition:
    it is FALSE without it, because of maximal munch (`p = "1"`, `rest = ".5"` re-parses as
    `1.5`). `SafeTail` is exactly the condition already used by T1a. -/
example : Prop :=
  ∀ p v rest, SValue p v → DepthOk v →
    (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
    ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩

/-- **C5 — rejection soundness (the theorem a reviewer actually wants).** If NO prefix is
    grammatical, the parser rejects. This is the contrapositive of C1 and is what rules out
    the degenerate "accept everything, return null" parser. -/
example : Prop := ∀ s, ¬ SAccepts s → parseDoc s = none

end Cjson.Spec
