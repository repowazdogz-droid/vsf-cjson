/-
  Cjson.Printer — serializer, matching cJSON_PrintUnformatted's *shape* (no spaces) but
  with EXACT number rendering rather than cJSON's lossy double pipeline (SPEC S3.2/S6-B).

  The number printer emits a canonical decimal form chosen so that re-parsing it recovers
  the same canonical `JNum`. That is the content of the Phase-4b round-trip theorem: it is
  a genuine normalisation statement, because e.g. `100`, `1e2` and `1.0e2` all parse to
  the same node and must all print back as the single canonical `100`.
-/
import Cjson.Basic
import Cjson.Parser

namespace Cjson

/-! ## Numbers -/

def digitBytes (ds : List Nat) : Bytes := ds.map digitByte

/-- Decimal digits of a `Nat`, most significant first. -/
def natToDigits (n : Nat) : List Nat :=
  if h : n < 10 then [n]
  else natToDigits (n / 10) ++ [n % 10]
termination_by n
decreasing_by omega

/-- Render an `Int` exponent: optional `-`, then digits. No `+` for positive exponents
    (cJSON's `%g` emits `e+21`; we emit `e21`. Both are valid RFC 8259 — logged as a
    formatting divergence, not a value divergence). -/
def renderInt (e : Int) : Bytes :=
  if e < 0 then 45 :: digitBytes (natToDigits e.natAbs)
  else digitBytes (natToDigits e.natAbs)

/-- Optional sign. -/
def signBytes (neg : Bool) : Bytes := if neg then [45] else []

/-- Optional fractional part: nothing, or `.` followed by digits. -/
def dotPart (F : List Nat) : Bytes :=
  match F with
  | [] => []
  | _ => 46 :: digitBytes F

/-- Which digit lists and exponent each printing branch selects. Factoring this out of
    `renderNum` separates the ARITHMETIC (which branch, and what it does to the exponent)
    from the BYTE-LEVEL scanning. The round-trip proof then needs one scanning lemma plus
    one arithmetic lemma, instead of four of each.

      1. plain integer          (exp ≥ 0, decimal point ≤ 21 places out)
      2. fixed point with a dot (exp < 0, point falls inside the digits)
      3. `0.000ddd`             (exp < 0, point just left of the digits, ≤ 6 zeros)
      4. scientific `d.dddeX`   (everything else — including `1e400`, rendered EXACTLY
                                 rather than collapsed to `null` as cJSON does) -/
def numParts (ds : List Nat) (exp : Int) : List Nat × List Nat × Option Int :=
  let pp : Int := (ds.length : Int) + exp        -- value = 0.ds × 10^pp
  if 0 ≤ exp ∧ pp ≤ 21 then
    (ds ++ List.replicate exp.toNat 0, [], none)
  else if exp < 0 ∧ 0 < pp ∧ pp ≤ 21 then
    (ds.take pp.toNat, ds.drop pp.toNat, none)
  else if exp < 0 ∧ -6 < pp ∧ pp ≤ 0 then
    ([0], List.replicate (-pp).toNat 0 ++ ds, none)
  else
    (ds.take 1, ds.drop 1, some (pp - 1))

/-- Optional exponent suffix. -/
def expPart : Option Int → Bytes
  | none => []
  | some E => 101 :: renderInt E                 -- 'e'

/-- The canonical decimal rendering of an exact number. -/
def renderNum (n : JNum) : Bytes :=
  match n.digits with
  | [] => [48]                                   -- "0"  (also covers -0 → 0)
  | d :: rest =>
    let p := numParts (d :: rest) n.exp
    signBytes n.neg ++ digitBytes p.1 ++ dotPart p.2.1 ++ expPart p.2.2

/-! ## Strings (SPEC S4.6) -/

def hexDigitLower (n : Nat) : UInt8 :=
  if n < 10 then UInt8.ofNat (n + 48) else UInt8.ofNat (n + 87)

/-- cJSON escapes `" \ \b \f \n \r \t` and any byte < 32 as `\u00xx` (lowercase hex).
    Everything else — including `/` and every byte ≥ 0x80 — goes out raw. -/
def escapeByte (c : UInt8) : Bytes :=
  if c == 34 then [92, 34]
  else if c == 92 then [92, 92]
  else if c == 8 then [92, 98]
  else if c == 12 then [92, 102]
  else if c == 10 then [92, 110]
  else if c == 13 then [92, 114]
  else if c == 9 then [92, 116]
  else if c.toNat < 32 then
    [92, 117, 48, 48, hexDigitLower (c.toNat / 16), hexDigitLower (c.toNat % 16)]
  else [c]

def renderStr (s : Bytes) : Bytes := 34 :: (s.flatMap escapeByte ++ [34])

/-! ## Values -/

mutual

def serialize : JSON → Bytes
  | .null => [110, 117, 108, 108]
  | .bool true => [116, 114, 117, 101]
  | .bool false => [102, 97, 108, 115, 101]
  | .num n => renderNum n
  | .str s => renderStr s
  | .arr xs => 91 :: (serializeL xs ++ [93])
  | .obj kvs => 123 :: (serializeKV kvs ++ [125])

/-- Elements joined by `,` — no separator after the last. -/
def serializeL : List JSON → Bytes
  | [] => []
  | [x] => serialize x
  | x :: xs => serialize x ++ (44 :: serializeL xs)

def serializeKV : List (Bytes × JSON) → Bytes
  | [] => []
  | [(k, v)] => renderStr k ++ (58 :: serialize v)
  | (k, v) :: kvs => renderStr k ++ (58 :: (serialize v ++ (44 :: serializeKV kvs)))

end

end Cjson
