/-
  Cjson.Basic — the JSON AST and the exact-number representation.

  Per SPEC.md S6 (option B, approved): a JSON number is modelled by its EXACT value,
  not by an IEEE double. The representation is canonical scientific notation:

      value  =  (-1)^neg  *  (digits as a decimal integer)  *  10^exp

  with `digits` held as a *canonical digit list*:
    - zero is represented by `digits = []`, and then `neg = false`, `exp = 0`;
    - otherwise `digits` has no leading zero and no trailing zero.

  Canonicity makes the representation UNIQUE per value: any nonzero decimal x can be
  written as ±D * 10^E with D having no trailing zero in exactly one way. That is what
  keeps the Phase-4b round-trip theorem a real normalisation statement rather than a
  tautology: `100`, `1e2` and `1.0e2` all parse to the same node ⟨false,[1],2⟩, so
  `parse ∘ serialize = id` genuinely has to reconstruct the same normal form.

  Strings are `List UInt8` (raw bytes), matching cJSON's byte-oriented, non-UTF-8-aware
  posture (SPEC S1.3). We do not impose UTF-8 validity.
-/

namespace Cjson

abbrev Bytes := List UInt8

-- NOTE: a decimal digit 0-9 is just `Nat`. We deliberately do NOT introduce an
-- `abbrev Digit := Nat`: `omega` does not unfold reducible type abbreviations, so the
-- alias silently disables the arithmetic automation. See REPORT.md.

/-- Exact decimal number: `(-1)^neg * digits * 10^exp`. See `Canonical`. -/
structure JNum where
  neg    : Bool
  digits : List Nat
  exp    : Int
deriving DecidableEq, Repr

namespace JNum

def zero : JNum := ⟨false, [], 0⟩

/-- Canonicity: the representation is unique per value. -/
def Canonical (n : JNum) : Prop :=
  (n.digits = [] ∧ n.neg = false ∧ n.exp = 0)
  ∨ (n.digits ≠ [] ∧ n.digits.head? ≠ some 0 ∧ n.digits.getLast? ≠ some 0
     ∧ ∀ d ∈ n.digits, d < 10)

end JNum

/-- The JSON value AST. -/
inductive JSON where
  | null
  | bool (b : Bool)
  | num  (n : JNum)
  | str  (s : Bytes)
  | arr  (xs : List JSON)
  | obj  (kvs : List (Bytes × JSON))
deriving Repr, Inhabited

namespace JSON

/-! `Canonical v` — every number reachable in the tree is canonical. This is the
invariant the parser establishes (T2) and the round-trip theorem (T1) consumes. -/
mutual
  inductive Canonical : JSON → Prop where
    | null : Canonical .null
    | bool : ∀ b, Canonical (.bool b)
    | num  : ∀ n, JNum.Canonical n → Canonical (.num n)
    | str  : ∀ s, Canonical (.str s)
    | arr  : ∀ xs, CanonicalL xs → Canonical (.arr xs)
    | obj  : ∀ kvs, CanonicalKV kvs → Canonical (.obj kvs)

  inductive CanonicalL : List JSON → Prop where
    | nil  : CanonicalL []
    | cons : ∀ x xs, Canonical x → CanonicalL xs → CanonicalL (x :: xs)

  inductive CanonicalKV : List (Bytes × JSON) → Prop where
    | nil  : CanonicalKV []
    | cons : ∀ k v kvs, Canonical v → CanonicalKV kvs → CanonicalKV ((k, v) :: kvs)
end

end JSON

/-! ## Byte predicates (SPEC S1, S2) -/

/-- SPEC S1.1: cJSON treats ANY byte ≤ 32 as whitespace — including NUL, VT, FF and every
    C0 control character. Much laxer than RFC 8259's `{0x20,0x09,0x0A,0x0D}`. -/
def isWs (c : UInt8) : Bool := c.toNat ≤ 32

def isDigitB (c : UInt8) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

def digitVal (c : UInt8) : Nat := c.toNat - 48

def digitByte (d : Nat) : UInt8 := UInt8.ofNat (d + 48)

/-- Hex-digit value. Unlike cJSON's `parse_hex4` — which returns `0` for BOTH the valid
    input "0000" and for any invalid digit, and whose caller cannot tell them apart —
    this DISTINGUISHES invalid from zero. That distinction is divergence D-STR-1
    (SPEC S4.3), a deliberate semantic change approved in Phase 1. -/
def hexVal? (c : UInt8) : Option Nat :=
  let n := c.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48)        -- '0'-'9'
  else if 65 ≤ n && n ≤ 70 then some (n - 55)   -- 'A'-'F'
  else if 97 ≤ n && n ≤ 102 then some (n - 87)  -- 'a'-'f'
  else none

/-! ## Nesting depth of a value -/

mutual
def jdepth : JSON → Nat
  | .arr xs => 1 + jdepthL xs
  | .obj kvs => 1 + jdepthKV kvs
  | _ => 0

def jdepthL : List JSON → Nat
  | [] => 0
  | x :: xs => max (jdepth x) (jdepthL xs)

def jdepthKV : List (Bytes × JSON) → Nat
  | [] => 0
  | (_, v) :: kvs => max (jdepth v) (jdepthKV kvs)
end

/-! ## Limits (SPEC S2) -/

/-- Matches `CJSON_NESTING_LIMIT`. Explicit, not stack-dependent. -/
def nestingLimit : Nat := 1000

end Cjson
