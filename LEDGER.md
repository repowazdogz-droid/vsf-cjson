# LEDGER.md

Everything preserved, changed, assumed, and left unproved. This is the document to read
if you want to know how far the proofs actually reach.

Target: cJSON `fb16e5cf358798aabb049655975cde8427101056` (vendored unmodified in `./oracle/`).
Toolchain: Lean 4.32.0, Std only. **No Mathlib, no Batteries, no FFI, no dependencies added.**

---

## 1. What is PROVEN

All statements are machine-checked. `#print axioms` output is in §6.

| # | theorem | statement |
|---|---|---|
| **T0** | totality | `parseValue` / `parseElems` / `parseMembers` are accepted by Lean's termination checker. **No fuel parameter exists.** |
| **T1** | round-trip | `parseDoc_serialize : Canonical v → jdepth v ≤ 1000 → parseDoc (serialize v) = some v` |
| **T1a** | numbers | `scanNumber_renderNum : JNum.Canonical n → SafeTail rest → scanNumber (renderNum n ++ rest) = some (n, rest)` |
| **T1b** | strings | `parseStrBody_renderStr : ∀ s rest, parseStrBody (s.flatMap escapeByte ++ (34 :: rest)) = some (s, rest)` |
| **T2a** | canonicity (numbers) | `normNum_canonical : (∀ d ∈ ds, d < 10) → JNum.Canonical (normNum neg ds e)` |
| **T2b** | canonicity (scanner) | `scanNumber_canonical : scanNumber s = some (n, r) → JNum.Canonical n` |
| **T2** | canonicity (**structural**) | `parseDoc_canonical : parseDoc s = some v → JSON.Canonical v` and `parseDoc_depth : parseDoc s = some v → jdepth v ≤ nestingLimit` |
| **T3** | **idempotence** | `parseDoc_idempotent : parseDoc s = some v → parseDoc (serialize v) = some v` — **unconditional** |

### T0 — totality. What it does NOT cover.

Termination is by **well-founded recursion on the lexicographic measure
`(remaining bytes, 0 for parseValue / 1 for the loops)`**, discharged by Lean. Every parser
returns a *subtype* carrying the proof that it consumed at least one byte, which is what
makes the decrease available at each recursive call site.

So there is **no fuel bound to declare**: totality is structural, not budgeted, and there is
no "fuel exhausted" outcome to worry about. The 1000-deep nesting limit is a *semantic*
limit from the spec, not a termination device — the parser would still terminate without it.

*Does not cover:* stack depth of the compiled binary. Lean's WF recursion compiles to a
recursive function; a 1000-deep nest is fine in practice (verified: depth 1000 accepted,
1001 rejected, matching the oracle), but I did not prove anything about the generated code's
stack usage. Totality is a statement about the Lean function, not about the machine.

### T1 — round-trip. What it does NOT cover.

*Does not cover:*
* **Values outside the depth limit.** A value nested deeper than 1000 serializes fine but
  does **not** re-parse. The hypothesis `jdepth v ≤ 1000` is not removable — the theorem
  would be false without it. This is a real limitation, stated rather than hidden.
* **Non-canonical ASTs.** If you hand-construct `JNum.mk false [1,0] 0` (a mantissa with a
  trailing zero — not canonical), `serialize` will produce `10` and the round-trip node will
  be `⟨false,[1],1⟩`, not what you put in. The theorem does not apply; T2 is what says the
  parser never produces such a node.
* **The other direction.** T1 is `parse ∘ serialize = id`. It says *nothing* about
  `serialize ∘ parse`, and nothing about which inputs `parse` accepts.

### T1a — number round-trip. What it does NOT cover.

The `SafeTail rest` hypothesis is **load-bearing, not a technicality**. The theorem is FALSE
for arbitrary `rest`: `renderNum 1 = "1"`, and `scanNumber ("1" ++ "2") = 12`, not `1`. A JSON
number has no terminator. `SafeTail` says the next byte cannot continue a number token (not
a digit, not `.`, not `e`/`E`), which is exactly what holds at every site where the
serializer actually emits a number: `,`, `]`, `}`, or end of input.

*Does not cover:* IEEE doubles. This is a theorem about **exact decimal numbers**. It says
nothing about what happens when you convert to a `Float`.

### T1b — string round-trip. What it does NOT cover.

*Does not cover:* UTF-8 validity. Strings are `List UInt8` and are round-tripped as bytes.
Invalid UTF-8 in, invalid UTF-8 out — deliberately, matching cJSON (SPEC S1.3). The theorem
is true of arbitrary byte strings, which is *why* it needs no `SafeTail`: the closing quote
is an unambiguous terminator.

### T2 — canonicity. What it does NOT cover.

**GAP-1 is now CLOSED (v1.0).** The parser's return type carries both invariants:

```lean
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }

def parseValue (depth : Nat) (s : List UInt8) :
    Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s
```

so `parseDoc_canonical` and `parseDoc_depth` are projections rather than a 26-case mutual
induction over `parseValue.induct`. Both invariants are `Prop`s and are erased at runtime; the
emitted bytes were re-verified **byte-identical** (JSONTestSuite 297/318 and fuzz
116,476/120,000 reproduced exactly, before and after the change).

*Does not cover:* anything about which inputs the parser accepts (GAP-2). T2 says the parser's
*output* is well-formed; it says nothing about its *input* language.

### T3 — idempotence. What it does NOT cover.

*Does not cover:* the compiled binary. T3 is a theorem about the Lean function. The 20,318-input
idempotence run is the only bridge to the executable (GAP-EXTRACT).

*Does not cover:* correctness. A parser that accepted every byte string and returned `null` would
satisfy T3 exactly as well. T3 says the parser is *self-consistent*, not that it is *right*.

---

## 2. Semantic changes (deliberate, approved in Phase 1)

| id | change | why |
|---|---|---|
| **NUM-EXACT** | JSON numbers are modelled as **exact decimals** (`± digits × 10^exp`), not IEEE doubles. | cJSON's number pipeline is lossy *by its own evident intent* (`compare_double` accepts a ~1-ULP error, so the "can I recover the original double?" check passes on values that are not the original). The round-trip property asked for in Phase 4b is therefore **false of cJSON**. Modelling exactly makes the theorem true and makes the loss visible as a divergence rather than hiding it inside a hand-rolled `strtod`. |
| **D-STR-1** | Invalid `\uXXXX` hex is **rejected**. cJSON accepts it as U+0000. | cJSON's `parse_hex4` returns `0` for both valid `0000` and any invalid digit; the caller cannot distinguish. Formalizing "accepts invalid input as valid" as correct behaviour was the one thing I declined to do. |
| **D-STR-2** | Embedded NULs **do not truncate** strings. cJSON drops everything after a NUL. | Same reason: silent data loss. |
| **D-FMT** | Exponent printed as `e21`, not `e+21`; plain-integer form preferred up to 21 significant places. | Both are valid RFC 8259. Fewer printer branches ⇒ shorter round-trip proof. Value-identical (checked by re-parsing with an independent parser). |

## 3. Preserved from the C (following the oracle, not the RFC — approved Phase 1)

* Whitespace is **any byte ≤ 32** (including NUL and every C0 control character), not the
  RFC's `{0x20,0x09,0x0A,0x0D}`.
* **Trailing bytes after a complete top-level value are accepted** (`[1]garbage` → `[1]`).
  This is `cJSON_Parse`'s `require_null_terminated = 0`. RFC 8259 rejects it. It is the
  single biggest source of cJSON's 32 shared `n_` failures on JSONTestSuite.
* The **lax number scanner**: `strtod`'s longest-valid-prefix over `[0-9+-eE.]`, so `007` →
  `7`, `1.` → `1`, `-.5` → `-0.5`, `1.2.3` → `1.2` (+ trailing garbage), `1e` → `1`.
* The **dispatch gate**: a value may only start a number with `-` or a digit, which is why
  `+1` and `.5` are still rejected even though the scanner would take them.
* **Unescaped control characters accepted inside strings** (re-escaped as `\uXXXX` on output).
* **No UTF-8 validation.** Bytes ≥ 0x80 pass through unexamined.
* **Duplicate object keys preserved**, both retained, in source order.
* **Nesting limit 1000**, matching `CJSON_NESTING_LIMIT`.
* **`-0` normalises to `0`** — agreeing with the oracle, though for a different reason
  (cJSON: `-0.0 == (double)0` takes the integer path. Us: an exact zero has no sign.)

## 4. UNPROVED — the honest gaps

### GAP-1 — CLOSED in v1.0 (recorded here for the audit trail)

**Both versions of the theorem, as required by claim discipline:**

*Originally shipped (v0.x) — weaker:*
```lean
theorem scanNumber_canonical : scanNumber s = some (n, r) → JNum.Canonical n   -- numbers only
-- structural lifting NOT proved; T3 NOT mechanized
```

*Now (v1.0) — full:*
```lean
theorem parseDoc_canonical  : parseDoc s = some v → JSON.Canonical v
theorem parseDoc_depth      : parseDoc s = some v → jdepth v ≤ nestingLimit
theorem parseDoc_idempotent : parseDoc s = some v → parseDoc (serialize v) = some v
```

No theorem was weakened. A theorem was **strengthened**, by strengthening the parser's return
type rather than by proving a separate induction. The historical statement of the gap is kept
below for the record.

<details><summary>Original gap statement (v0.x) — now closed</summary>

#### (historical) structural lifting of T2

**Not proven:**
```lean
theorem parseDoc_canonical :
    ∀ (s : Bytes) (v : JSON), parseDoc s = some v → JSON.Canonical v
```
and its two mutual companions
```lean
    ∀ d s xs r, pe d s = some (xs, r) → JSON.CanonicalL xs
    ∀ d s kvs r, pm d s = some (kvs, r) → JSON.CanonicalKV kvs
```

I proved that the *number scanner* only builds canonical numbers (**T2b**). I did **not**
prove that every number reachable *inside a parsed tree* is canonical. The two are separated
only by a mutual induction over `parseValue.induct` (which Lean does generate — it has ~20
cases, each requiring the same dependent-match plumbing described in REPORT.md). It is
mechanical, not deep. I ran out of the effort budget (Hard Rule 6) and stopped rather than
fake it.

**Consequence, stated plainly:** the composite theorem

> **T3** `parseDoc s = some v → parseDoc (serialize v) = some v`
> ("anything my parser produces re-parses to itself")

**is not mechanized.** T3 follows immediately from T1 + GAP-1, and GAP-1 is the only missing
link. Since T3 is the theorem a user actually cares about, this gap is material and I am not
going to bury it.

**What I did instead:** T3 is directly observable at the CLI — running the binary twice must
equal running it once. Measured on the full JSONTestSuite corpus plus 20,000 fuzz inputs:

```
inputs checked : 20,318
accepted       :  3,021
VIOLATIONS     :      0
```

That was **evidence, not proof**, and was reported as such.

</details>

**Status of the idempotence measurement now:** since T3 is PROVEN, the 20,318-input run is no
longer a stand-in for an unproved property. It is a **cross-check that the extracted binary
agrees with the theorem's model** — i.e. the only evidence we have about the extraction step
(GAP-EXTRACT). That is a different and weaker guarantee, and it is labelled as such in CLAIMS.md.

### GAP-EXTRACT — the compiled binary is not the verified artifact

**Not proven.** All theorems are about Lean functions. The binary is produced by Lean's compiler
and linked against its runtime; neither is verified here. Every number in DIVERGENCES.md is a
statement about *the binary*; every theorem is about *the function*. The 20,318-input idempotence
run (0 violations) is the only bridge.

### GAP-2 — soundness against the SPEC grammar (Phase 4c)

**Not proven.** Phase 4 asked for:

> parse succeeds only on inputs the spec grammar accepts

I did not state an independent inductive grammar predicate `Grammar : Bytes → Prop` mirroring
SPEC §S2, and I did not prove `parseDoc s = some v → Grammar s`. Nothing in this deliverable
certifies that the parser rejects everything it should.

What *is* proven is the **converse direction, restricted to the serializer's image**: T1 shows
that `serialize v` is accepted for every canonical `v` within the depth limit. That is a
completeness statement about a subset, not soundness. **Do not read T1 as evidence that the
parser rejects bad input.** The only support for that is the differential corpus, where the
Lean port and the oracle agreed on accept/reject for 317/318 JSONTestSuite files and for
119,999/120,000 fuzz inputs.

Honest summary: **the parser's accept-set is tested, not proved.**

### GAP-3 — no exponent bound

The exact-number model will faithfully emit an exponent of any magnitude
(`1e400030000000000000004`). This is syntactically valid RFC 8259 but overflows most JSON
consumers (Python's `Decimal` raises on it). See DIVERGENCES.md D-LEAN-1. I did not add a
limit, because inventing one that neither the RFC nor cJSON has would be a silent third
semantics. A production port should add one — and say so in its spec.

### GAP-4 — the oracle wrapper's entry point is a choice, not a proof

The wrapper uses `cJSON_ParseWithLength(buf, len + 1)` over a NUL-appended copy. This is
byte-for-byte the buffer `cJSON_Parse()` builds for any NUL-free input. Everything measured
here is relative to that choice. `cJSON_ParseWithLength(buf, len)` (without the extra byte)
has a *different* and buggier BOM behaviour — see SPEC §S7. Not in scope; not tested.

## 5. Theorems weakened or restated

**None.** No theorem in this deliverable was weakened, narrowed, or restated to make a proof
pass. The `SafeTail` and `Canonical` and depth hypotheses were present in the statements from
the first draft, because they are *true preconditions* — the theorems are false without them,
which I established before attempting the proofs (§T1, §T1a above).

**One implementation change was made after v0.x, to close GAP-1:** the parser's return type was
strengthened from `Res α s` to `Res α P s` (carrying canonicity and the depth bound). The
`if depth ≥ nestingLimit` was made dependent (`if h : ...`) so the bound is in scope. **No
behaviour changed** — the invariants are `Prop`s and are erased. Verified by re-running the
entire differential suite: JSONTestSuite 297/318 and fuzz 116,476/120,000, byte-for-byte
identical to the pre-change numbers.

The one thing that changed shape during the earlier work was the **printer**, not a theorem:
`renderNum` was refactored twice (into `signBytes`/`digitBytes`/`dotPart`/`expPart`, then
factored again into `numParts` + `expPart`) to make its four branches share one scanning
lemma. **The emitted bytes were verified unchanged after each refactor** by re-running the
differential harness (identical 6/28 divergence profile before and after). No behaviour was
traded for provability.

## 6. `#print axioms` — the trusted base

```
'Cjson.parseValue'             depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseDoc'               depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.serialize'              depends on axioms: [propext, Quot.sound]
'Cjson.scanNumber_renderNum'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseStrBody_renderStr' depends on axioms: [propext, Quot.sound]
'Cjson.roundtrip_value'        depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseDoc_serialize'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseDoc_canonical'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseDoc_depth'         depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.parseDoc_idempotent'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

These three are **Lean's standard axioms**, not project-specific ones. Hard Rule 1 bans
`sorry`, `admit`, `native_decide`, and **custom** axioms; there are none of any:

```
$ grep -rn "sorry\|admit\|native_decide\|^axiom \|@\[extern\]" lean/Cjson/ lean/Main.lean
(only a comment in Str.lean explaining that `decide` is kernel reduction, not native_decide)
```

`decide` **is** used (e.g. 16 concrete hex-digit cases). That is kernel reduction and is
sound; it is not `native_decide`, which would move the check outside the kernel.

I did not attempt to eliminate `propext` / `Classical.choice` / `Quot.sound`. They enter
through `simp`, `omega`, and well-founded recursion. Removing them was not a requirement and
would have cost more than it is worth here.


---

## 7. GAP-2 adequacy proof — boundary statements (branch `gap2-adequacy-proof`)

One sentence per major lemma, saying what it does **not** establish. Nothing in this section is
released; v1.0.1 is untouched.

* **A10 `canonical_unique`** — establishes that two *canonical* `JNum`s denoting the same exact
  decimal are equal, so "the value the grammar assigns" is well-defined.
  *This theorem does NOT establish that a number has a unique syntactic spelling* — `100`, `1e2`
  and `1.0e2` are three different byte strings and must remain so; it says only that they land on
  the same AST node.

* **`natOf_inj`** — establishes that the positional denotation is injective on digit lists with
  no leading zero and all digits `< 10`.
  *This theorem does NOT establish anything about lists that violate either condition* — both are
  necessary (`[12]` vs `[1,2]`; `[0,1]` vs `[1]`).

* **`normNum_denote`** — establishes that the parser's normaliser lands in the grammar's
  `SameNum` equivalence class, which is what lets the grammar keep parser-independent number
  semantics.
  *This theorem does NOT establish that `normNum` produces a canonical result* (that is
  `normNum_canonical`, proved separately in v1.0.1), and it does NOT say the parser consumed the
  right bytes.

* **`ofDigits_natOf`** — establishes that the parser's Horner fold and the grammar's positional
  denotation agree.
  *This theorem does NOT establish anything about digit lists containing values `≥ 10`* — it is
  an identity of two denotations, not a well-formedness check.

* **`scanDigits_sound` / `scanFrac_sound` / `scanExpDigits_sound` / `scanExp_sound` /
  `scanSign_sound`** — each establishes that the bytes the corresponding scanner consumed form a
  grammatical fragment denoting exactly what the scanner returned.
  *These theorems do NOT establish maximal munch (C3, deferred): they say the consumed bytes are
  grammatical, not that no longer grammatical prefix exists.*

* **`scanNumber_sound`** — establishes NUMBER SOUNDNESS: the bytes `scanNumber` consumed form a
  token that the SPEC grammar assigns exactly the value returned.
  *This theorem does NOT establish the §S2 dispatch gate* (that `+1` and `.5` are rejected at
  value position — that gate lives in `parseValue`, not in `scanNumber`), *does NOT establish
  maximal munch*, and *does NOT establish completeness* (that every grammatical number token is
  accepted).

* **`hex4_isHex` / `not_surrogate` / `isHigh_range` / `isLow_range` / `enc_eq`** — establish the
  bridge lemmas between the parser's boolean surrogate tests and hex decoder and the grammar's
  numeric ranges and encoder.
  *These theorems do NOT establish string-body soundness* — that is `parseStrBody_sound`, which
  is BLOCKED (see `BLOCKER.md`), not proved.

* **`parseStrBody_sound` / `parseStrBody_sound'`** — establishes STRING-BODY SOUNDNESS: for every
  input the released `parseStrBody` accepts, the bytes it consumed (up to the closing quote) form
  a string body that the independently-written `SChars` grammar decodes to exactly the byte string
  the parser returned.
  *This theorem does NOT establish completeness* (that every grammatical body is accepted — C4),
  *does NOT establish maximal munch* (C3, deferred), *does NOT establish anything about UTF-8
  validity* (the grammar, like the parser, passes bytes ≥ 0x80 through unexamined, SPEC §S1.3),
  *and says nothing about the surrounding quotes or about `parseValue`* — a `"` is consumed by the
  caller, not here.

* **`psb_esc` / `psb_esc34…psb_esc116` / `psb_bad_esc`** — establish branch equations for the
  released parser: each simple escape decodes to its byte, and a backslash followed by anything
  that is neither a simple escape nor `u` is rejected.
  *These theorems do NOT establish anything about the grammar* — they are facts about the parser
  alone, and are the only place where the parser's byte-level branch structure is exposed.

* **`struct_sound` / `pv_sound` / `pe_sound` / `pm_sound`** — establish STRUCTURAL SOUNDNESS:
  every input the released `parseValue`/`parseElems`/`parseMembers` accepts, the consumed bytes
  form a fragment (value / element-list-with-`]` / member-list-with-`}`) that the independent
  grammar (`SValue`/`SElems`/`SMembers`) assigns exactly the returned AST.
  *These theorems do NOT establish completeness* (that every grammatical input is accepted — C4),
  *do NOT establish maximal munch* (C3, deferred), *and do NOT bound nesting depth* — the
  parser's depth check only makes the hypothesis harder to satisfy; the grammar `SValue`/`SElems`/
  `SMembers` carry no depth bound (that lives at the document level).

* **`parseDoc_sound` (C2)** — establishes DOCUMENT-LEVEL VALUE SOUNDNESS:
  `parseDoc s = some v → SDoc s v`, i.e. `s` decomposes as `bom ++ ws ++ valuePrefix ++ trailing`
  with the value prefix denoting exactly `v` under the SPEC grammar, and `jdepth v ≤ 1000`.
  *This theorem does NOT establish completeness (C4)* — it says every accepted document is
  grammatical, NOT that every grammatical document is accepted; because SPEC §S5.1 accepts
  trailing garbage, C2 alone is satisfiable by a lazy parser, so C2 ∧ C4 (not C2 alone) is the
  adequacy target. *It also does NOT establish the §S2 dispatch gate as a rejection property*
  (it uses the gate as a hypothesis, discharged by the parser having accepted).

* **`skipWs_split` / `skipBom_split` / `isWs_IsWs` / `SValue_ne_nil` / `gate_of`** — bridge lemmas.
  *These do NOT establish anything about grammaticality on their own*; `SValue_ne_nil` is what
  recovers the strict-decrease measure from the grammar rather than from the parser's stripped
  result subtype.

* **`scanNumber_complete`** — `SNumTok p n → SafeTail rest → scanNumber (p ++ rest) = some (n, rest)`.
  For an *arbitrary* grammatical number spelling `p` (the unmodified `SNumTok`: `01`, `1.0`, `1e2`,
  `.5`, arbitrary leading/trailing zeros and exponent forms), the parser's scanner consumes exactly
  `p` and returns the grammar's canonical `n`, leaving `rest`. The value clause routes through
  `normNum_denote` + `SameNum_symm`/`SameNum_trans` + **A10 (`canonical_unique`)**; the grammar is
  NOT narrowed to canonical renderings.
  *This theorem does NOT establish maximal munch* (C3, deferred — it relies on `SafeTail` to stop
  over-consumption rather than proving no-longer-prefix-exists), *does NOT establish the §S2 dispatch
  gate* (that lives in `parseValue`, not `scanNumber`), *and does NOT establish completeness of the
  string or structural cases* (separate leaves).

* **`SameNum_symm` / `SameNum_trans`** — the grammar's number-value equivalence `SameNum` is symmetric
  and transitive. *These do NOT establish it is decidable or a full setoid API*; only the two facts
  needed to bridge `normNum`'s output and the grammar's `n` through the shared `(M,E)` class.

* **`scanDigits_complete` / `scanFrac_complete` / `scanExp_complete` / `scanExpDigits_complete` /
  `scanSign_complete` / digit bridge (`Digits_eq_digitBytes`, `Digits_lt10`)** — each converse scanner
  consumes exactly its grammatical piece given the appropriate tail condition.
  *These do NOT establish the scanners reject anything*; they are one-directional (grammar → scan).

* **`parseStrBody_complete`** — `SChars body v → ∀ rest, parseStrBody (body ++ 34 :: rest) = some (v, rest)`.
  For every grammatical string body (an *arbitrary* `SChars` spelling — escaped `\/` and unescaped
  `/`, mixed-case `\uXXXX`, valid surrogate pairs, raw bytes ≥ 0x80 with no UTF-8 validation per
  SPEC §S1.3 — NOT the canonical rendering only), the released parser is forced into the branch the
  grammar dictates and returns the grammar-decoded `v`, leaving `rest`. Direct induction on
  `SChars.rec`; reuses the released reverse escape equations (`psb_esc34…psb_esc116`,
  `parseStrBody_other`) and the StrSound bridge `enc_eq`; adds `hex4_complete` and the reverse
  surrogate-range lemmas.
  *This theorem does NOT establish that the parser REJECTS non-grammatical bodies* (it is
  one-directional, grammar → parse), *does NOT establish UTF-8 validity of the raw bytes* (the
  grammar, like the parser, passes bytes ≥ 0x80 through unexamined), *and says nothing about the
  opening quote* (consumed by `parseValue`, not here).

* **`hex4_complete` / surrogate-range converses (`isHigh_true`/`isLow_true`/`isLow_false_of_high`/
  `isLow_false_of_not`/`isHigh_false_of_not`)** — the reverse of the StrSound bridges: valid hex
  digits make `hex4` succeed with `hex4v`, and the grammar's surrogate ranges pin the parser's
  boolean tests. *These do NOT establish the parser rejects invalid hex* (that is D-STR-1, a
  soundness-side/oracle fact).
