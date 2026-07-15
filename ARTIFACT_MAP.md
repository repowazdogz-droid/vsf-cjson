# ARTIFACT_MAP.md — frozen inventory of the vsf-cjson artifact

A complete map of the repository: every theorem, every report, every harness. It is written
so an external researcher can understand what this artifact **is** and **claims** without
reading a single line of Lean. Nothing here is generated; it is a hand-authored freeze snapshot.

- **Repository:** a Lean 4 re-implementation of cJSON's core parse/serialize path, with
  machine-checked proofs, plus a GAP-2 adequacy proof against an independent grammar.
- **Branch at freeze:** `gap2-adequacy-proof`. **Released tag:** `v1.0.1`.
- **Toolchain:** `leanprover/lean4:v4.32.0`, Std only — no Mathlib, no external Lake packages,
  no FFI. Verified `lake-manifest.json` packages = `[]`.
- **Trusted axiom base:** Lean's three standard axioms only —
  `propext`, `Classical.choice`, `Quot.sound`. No `sorry`/`sorryAx`, no `admit`, no
  `native_decide`, no custom `axiom`. (Established directly on all exported roots; see §3.)
- **Two artifacts, one repo.** The **released artifact** (`lean/Cjson.lean` and its imports)
  is byte-identical to tag `v1.0.1` and does **not** import the spec chain. The **GAP-2
  adequacy proof** lives under `lean/Cjson/Spec/` with its own root `Cjson.Spec`, is verified
  separately, and is the newer work. Keeping them separate is deliberate: the released parser
  is the *oracle-checked implementation*; the grammar is an *independent specification* the
  parser is proved adequate against.

---

## 1. How to read this document

- **§3** is the trust base: axioms and provenance (AI vs human).
- **§4** is the theorem catalog. The **21 exported claims** (18 theorems + 3 attested
  definitions — the artifact's actual claims) get full treatment. The **174 supporting lemmas**
  are catalogued per module with role and the exported root they feed.
- **§5 / §6** inventory the reports and the verification harness.
- **§7** states, in one place, what the whole artifact does **NOT** prove.
- **§8** is the freeze manifest (counts, how to reproduce).

Terminology:
- **Exported / load-bearing claim** — an *attested* theorem or definition: a terminal result
  the artifact stands behind, gated by CI. There are 11 released + 10 GAP-2.
- **Support→X** — a lemma authored as a step toward exported claim `X`.
- **Statement** — the theorem's type. For exported theorems the exact Lean statement is given;
  the pretty-printed forms of the GAP-2 ten are also in the machine-generated `ADEQUACY_SUMMARY.md`.

---

## 2. Repository topology

```
vsf-cjson/
├── lean/
│   ├── Cjson.lean               root of the RELEASED artifact (imports released modules only)
│   ├── Main.lean                CLI entry (imports Cjson) → binary lean/.lake/build/bin/cjson
│   ├── Cjson/
│   │   ├── Basic.lean           AST (JSON, JNum), jdepth, isDigitB, nestingLimit=1000   [defs]
│   │   ├── Parser.lean          parseValue/parseElems/parseMembers, scanNumber, parseStrBody,
│   │   │                        skipWs/skipBom/parseDoc   [defs + 17 lemmas]
│   │   ├── Printer.lean         serialize / renderNum / escapeByte   [defs]
│   │   ├── Proofs/{Digits,Num,Str,RoundTrip}.lean   released proofs (7/26/6/34 theorems)
│   │   └── Spec/                GAP-2 adequacy chain (root: Cjson.Spec.lean)
│   │       ├── Grammar.lean     declarative grammar SValue/SElems/SMembers/SChars/SNumTok,
│   │       │                    SDoc/DepthOk/SameNum/enc, and the C1–C5 candidate Props  [defs]
│   │       ├── Uniqueness.lean  (11)  NumSound.lean (15)  StrSound.lean (17)
│   │       ├── StructSound.lean (14)  NumComplete.lean (17)  StrComplete.lean (7)
│   │       ├── StructComplete.lean (21)  Checks.lean (0 — statement pins, examples only)
│   │       └── Spec.lean        aggregator importing the eight modules above
│   ├── lakefile.toml  lean-toolchain   (both byte-identical to v1.0.1)
├── oracle/            pinned unmodified cJSON (commit fb16e5cf…) + wrapper.c CLI + PROVENANCE
├── harness/           differential + gate scripts (see §6); JSONTestSuite/ vendored corpus
│   └── gap2/          GAP-2 gate + summary generator + reference decider/hunter
├── figures/          make_figures.py → 3 deterministic SVGs
├── results/canonical/ measurement JSON (suite/fuzz/idempotence/claims)
├── release/          manifest.json (v1.0.1)  +  gap2_manifest.json (adequacy)
├── .github/workflows/verify.yml   CI: verify.sh + mutation_tests.sh
├── verify.sh  reproduce.sh        the two driver commands
└── *.md              reports (see §5)
```

---

## 3. Trust base and provenance

### 3.1 Axioms (verified, not asserted)

`#print axioms` was run on every exported root. Results:

| axiom set | exported theorems / defs with this set |
|---|---|
| `propext, Classical.choice, Quot.sound` | `parseValue`, `parseDoc`, `scanNumber_renderNum`, `scanNumber_canonical`, `roundtrip_value`, `parseDoc_serialize`, `parseDoc_canonical`, `parseDoc_depth`, `parseDoc_idempotent`; `scanNumber_sound`, `struct_sound`, `parseDoc_sound`, `scanNumber_complete`, `parseStrBody_complete`, `struct_complete`, `C4`, `adequacy` |
| `propext, Quot.sound` (no choice) | `serialize`, `parseStrBody_renderStr`; `canonical_unique`, `parseStrBody_sound'` |

**Every supporting lemma's axioms ⊆ `{propext, Classical.choice, Quot.sound}`.** This is not
21 spot-checks extrapolated — it is a closure fact: `#print axioms X` reports the *transitive*
axiom closure of `X`, so any lemma used by an exported root cannot carry an axiom the root does
not report. The two topmost roots (`adequacy` over the whole spec chain, `parseDoc_idempotent`/
`parseDoc_serialize`/`roundtrip_value` over the whole released chain) already report exactly the
standard three; therefore no lemma in either cone carries anything else. `sorryAx` would appear
if any `sorry` were reachable — it does not.

### 3.2 Provenance — AI-generated vs human-guided

**All Lean 4 source in this repository — every definition, every theorem statement, every
proof — was written by an AI system (Claude), across multiple sessions, under human mission
direction. There are no human-authored proofs.** So for **every** theorem below: *generated by
AI = yes; human-wrote-the-proof = no.*

"Human-guided" is therefore not a per-line distinction but a set of **documented human decision
points** that shaped what was proved and how. The load-bearing ones:

| human-directed decision | where logged | which theorems it shaped |
|---|---|---|
| Hard rules: no `sorry`/`admit`/`native_decide`/custom axiom/Mathlib; oracle unmodified; divergences logged not patched | mission / `LEDGER.md` | all |
| Number model = **exact decimal** `± m·10^e`, not IEEE double | `LEDGER.md` §2 (NUM-EXACT), `SPEC.md` | `SNumTok`, `SameNum`, `normNum_denote`, `scanNumber_*` |
| Reject shortcut: define grammar numbers as `normNum` (the parser's normaliser) | `INDEPENDENCE_RISK.md` Risk 1 | `normNum_denote`, `scanNumber_sound/complete` |
| Reject shortcut: carry a grammar witness in the parser's return type | `INDEPENDENCE_RISK.md` Risk 2 | `struct_sound`, `struct_complete`, `parseStrBody_sound'` |
| Staged length induction for soundness (same-length `parseElems→parseValue` hazard) | `BLOCKER.md`, `ADEQUACY_REPORT.md` | `hV_step`/`hE_step`/`hM_step`, `struct_sound` |
| Reuse audit: released assembly lemmas are canonical-specific → prove whitespace-tolerant generalizations | `INDEPENDENCE_RISK.md` Risk 5 | `pv_arr_cons_gen`…`pm_cons_gen`, `struct_complete`, `C4` |
| D-STR-1 (reject invalid `\uXXXX`), D-STR-2 (NUL non-truncating) | `SPEC.md`, `DIVERGENCES.md` | `SChars`, `parseStrBody_sound'/complete` |

Everything else is mechanical proof engineering the AI performed to discharge those choices.

---

## 4. Theorem catalog

192 theorems total: **90 released** (Parser 17, Proofs/Digits 7, Proofs/Num 26, Proofs/Str 6,
Proofs/RoundTrip 34) + **102 GAP-2** (Uniqueness 11, NumSound 15, StrSound 17, StructSound 14,
NumComplete 17, StrComplete 7, StructComplete 21). `Basic`, `Printer`, `Grammar`, `Checks`
contribute 0 theorems (definitions / statement-pins).

### 4.1 The released artifact — exported claims (11)

`parseValue`/`parseDoc`/`serialize` are *definitions* but are attested (their axiom footprint
is load-bearing); the rest are theorems. All are byte-identical to v1.0.1.

**`parseValue` / `parseDoc` (defs)** — the total parser. Purpose: parse bytes to a `JSON`
value via well-founded recursion (no fuel), returning a subtype carrying `Canonical v ∧
jdepth v ≤ nestingLimit - depth`. Load-bearing: yes (the object of every theorem). Axioms:
`propext, Classical.choice, Quot.sound`. Does NOT establish: anything about the *compiled*
binary (GAP-EXTRACT); the language accepted (that is the GAP-2 chain).

**`serialize` (def)** — the printer. Purpose: render a `JSON` to canonical bytes. Axioms:
`propext, Quot.sound`. Does NOT establish: that arbitrary (non-canonical) ASTs round-trip.

| theorem | statement (exact) | purpose | proof | does NOT prove |
|---|---|---|---|---|
| `scanNumber_canonical` | `scanNumber s = some (n,r) → JNum.Canonical n` | the number scanner only ever builds canonical `JNum`s | 20 L | that *tree-internal* numbers are canonical (that is `parseDoc_canonical`) |
| `parseDoc_canonical` | `parseDoc s = some v → JSON.Canonical v` | every parsed value is canonical (structural, via the return-type invariant) | 10 L | which inputs are accepted |
| `parseDoc_depth` | `parseDoc s = some v → jdepth v ≤ nestingLimit` | parsed values respect the 1000 nesting limit | 13 L | binary stack depth |
| `scanNumber_renderNum` | `Canonical n → SafeTail rest → scanNumber (renderNum n ++ rest) = some (n,rest)` | number round-trip (print→scan) for a safe tail | 58 L | IEEE-double behaviour; arbitrary trailing bytes (`SafeTail` load-bearing) |
| `parseStrBody_renderStr` | `parseStrBody (s.flatMap escapeByte ++ 34::rest) = some (s,rest)` | string round-trip (escape→parse) | 7 L | UTF-8 validity — bytes are opaque |
| `roundtrip_value` | `Canonical v → d+jdepth v ≤ nestingLimit → SafeTail rest → pv d (serialize v ++ rest) = some (v,rest)` | value round-trip for the canonical rendering | 154 L | acceptance of *non-canonical* spellings (that is C4); values over the depth limit |
| `parseDoc_serialize` | `Canonical v → jdepth v ≤ nestingLimit → parseDoc (serialize v) = some v` | document round-trip parse∘serialize = id (on canonical, in-limit values) | 11 L | `serialize∘parse`; which inputs parse |
| `parseDoc_idempotent` | `parseDoc s = some v → parseDoc (serialize v) = some v` | idempotence (T3), unconditional on the parsed value | 4 L | correctness (a null-returning parser also satisfies it); the binary |

### 4.2 The GAP-2 adequacy proof — exported claims (10)

The top-level claim is `adequacy = C2 ∧ C4`, "the parser is adequate w.r.t. the frozen grammar."
Exact statements are also machine-printed in `ADEQUACY_SUMMARY.md`.

| theorem | statement (exact) | purpose | LB | proof | axioms | does NOT prove |
|---|---|---|---|---|---|---|
| `canonical_unique` (A10) | `Canonical n₁ → Canonical n₂ → SameNum … → n₁ = n₂` | the value the grammar assigns a number is well-defined | ✔→scanNumber_complete, C2 | 47 L | `propext, Quot.sound` | that a number has a unique *spelling* (`100`,`1e2`,`1.0e2` differ) |
| `scanNumber_sound` | `scanNumber s = some (n,r) → ∃ p, s = p++r ∧ SNumTok p n` | number soundness: consumed bytes are a grammatical token denoting the returned value | ✔→C2 | 91 L | `…Classical.choice…` | the §S2 dispatch gate; maximal munch; completeness |
| `parseStrBody_sound'` | `parseStrBody s = some (v,r) → ∃ p, s = p++(34::r) ∧ SChars p v` | string-body soundness against the independent `SChars` grammar | ✔→C2 | 4 L (wraps 148 L `parseStrBody_sound`) | `propext, Quot.sound` | UTF-8 validity; the quotes/`parseValue`; completeness |
| `struct_sound` | `∀ n, PVsound n ∧ PEsound n ∧ PMsound n` | structural soundness for value/element/member (staged length induction) | ✔→C2 | 24 L (+`hV/hE/hM_step` 93/41/69 L) | `…Classical.choice…` | completeness; depth bound (lives at doc level); maximal munch |
| `parseDoc_sound` (**C2**) | `parseDoc s = some v → SDoc s v` | **document value soundness** — every accepted doc denotes, under the grammar, the returned value | **exported** | 16 L | `…Classical.choice…` | completeness (§S5.1 trailing-garbage makes soundness alone satisfiable by a lazy parser); the dispatch gate as a rejection |
| `scanNumber_complete` | `SNumTok p n → SafeTail rest → scanNumber (p++rest) = some (n,rest)` | number completeness for *arbitrary* grammatical spellings (`01`,`1.0e2`,…) | ✔→C4 | 63 L | `…Classical.choice…` | maximal munch (relies on `SafeTail`); dispatch gate; rejection |
| `parseStrBody_complete` | `SChars body v → parseStrBody (body++34::rest) = some (v,rest)` | string completeness for arbitrary `SChars` (escaped/unescaped `/`, mixed-case `\u`, surrogate pairs) | ✔→C4 | 43 L | `…Classical.choice…` | that the parser *rejects* non-grammatical bodies (one-directional); UTF-8 validity |
| `struct_complete` | `SValue p v → ∀ d rest, d+jdepth v ≤ nestingLimit → SafeTail rest → pv d (p++rest) = some (v,rest)` | structural completeness by one mutual induction on the grammar derivation (`SValue.rec`, 13 cases) | ✔→C4 | 163 L | `…Classical.choice…` | soundness; maximal munch; rejection; **remains false of a canonical-only parser** |
| `C4` (**C4**) | `SValue p v → DepthOk v → (SafeTail rest) → ∃ h, parseValue 0 (p++rest) = some ⟨(v,rest),h⟩` | **completeness** — every grammatical value within depth, with a number-safe tail, is accepted at exactly those bytes | **exported** | 9 L | `…Classical.choice…` | maximal munch (C3; `SafeTail` non-removable — `p="1"`,`rest=".5"`→`1.5`); soundness; rejection (C5) |
| `adequacy` | `(∀ s v, parseDoc s = some v → SDoc s v) ∧ (C4 Prop)` | **adequacy = C2 ∧ C4** | **exported (top)** | 7 L (`⟨parseDoc_sound, C4⟩`) | `…Classical.choice…` | C3, C5, RFC 8259 conformance, cJSON behavioural equivalence, the compiled binary, "fully verified JSON parser" |

The C4 side condition `(∀ c t, rest = c::t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ ≠ 101 ∧ ≠ 69)`
is definitionally `SafeTail rest`; `DepthOk v` is definitionally `jdepth v ≤ nestingLimit`. Both
are the frozen grammar's own definitions (pinned by hash — see §6). `Cjson.Spec.Checks` re-asserts
the exact `Grammar.lean` C2/C4 Props against these theorems, so a statement change breaks the build.

### 4.3 Supporting lemmas (174) — role catalog

Each lemma is authored toward the exported root of its module. Axioms of all ⊆ the standard
three (§3.1 closure). Sizes are proof lines. `H` marks a proof > 40 L.

**Released — `Cjson/Parser.lean` (17)** → feed `scanNumber_canonical`, `parseDoc_canonical`,
and termination:
`skipWs_le`, `scanDigits_le`, `scanDigits_lt`, `scanSign_le`, `scanFrac_le`, `scanFrac_lt`,
`scanExpDigits_le`, `scanExp_le`, `scanNumber_lt`, `head`, `getLast`, `mem_dropWhile`,
`normNum_canonical`, `scanDigits_lt10`, `scanNumber_canonical`\*, `parseStrBody_le`,
`parseDoc_canonical`\*.  (\* = exported.)

**Released — `Cjson/Proofs/Digits.lean` (7)** → digit denotation bridges feeding `Num`/`RoundTrip`:
`toNat_digitByte`, `digitVal_digitByte`, `isDigitB_digitByte`, `scanDigits_digitBytes`,
`natToDigits_lt10`, `ofDigits_snoc`, `ofDigits_natToDigits`.

**Released — `Cjson/Proofs/Num.lean` (26)** → feed `scanNumber_renderNum` (number round-trip)
and the `SafeTail` API (reused by GAP-2):
`canon_of_JNum`, `dropWhile_zeros`, `head`, `head`, `dropWhile_reverse_canon`, `normNum_trailing`,
`normNum_leading`, `normNum_exact`, `safeTail_nil`, `safeTail_struct`, `safeTail_notDigit`,
`natToDigits_ne_nil`, `digitBytes_head_notSign`, `scanExpDigits_renderInt`, `scanExp_renderExp`,
`scanFrac_notDot`, `scanExp_notE`, `digitBytes_append`, `safeTail_notDot`, `notDigit_dotPart`,
`scanFrac_dotPart`, `scanSign_render`, `scanNumber_shape`, `normNum_zero`, `numParts_spec` (H,77L),
`scanNumber_renderNum`\* (58L).

**Released — `Cjson/Proofs/Str.lean` (6)** → feed `parseStrBody_renderStr` (string round-trip):
`hexVal`, `hex4_ctrl`, `utf8Enc_lt128`, `parseStrBody_other`, `parseStrBody_escapeByte` (H,51L),
`parseStrBody_renderStr`\*.

**Released — `Cjson/Proofs/RoundTrip.lean` (34)** → the assembly layer + `roundtrip_value` →
`parseDoc_serialize`/`parseDoc_depth`/`parseDoc_idempotent`. Also defines the plain-Option
views `pv`/`pe`/`pm` and the parametric leaf lemmas the GAP-2 chain reuses:
`skipWs_id`, `renderNum_head`, `renderNum_ne_nil`, `serialize_head`, `serialize_ne_nil`,
`noLeadWs_serialize`, `pv_str_known`, `pv_num_known` (H,43L), `pv_arr_empty`, `pv_obj_empty`,
`pv_arr_cons`, `pv_obj_cons` — **canonical-specific (assume no interior whitespace); NOT reused
by C4, see Risk 5** —, `skipWs_struct`, `skipWs_44/58/93/125`, `pe_last`, `pe_cons`, `pm_last` (H),
`pm_cons` (H,45L), `pv_null`, `pv_true`, `pv_false`, `serializeL_head`, `serializeKV_head`,
`roundtrip_value`\* (H,154L), `skipBom_serialize`, `noLeadWs_serialize'`, `pv_congr`,
`parseDoc_eq`, `parseDoc_serialize`\*, `parseDoc_depth`\*, `parseDoc_idempotent`\*.

**GAP-2 — `Cjson/Spec/Uniqueness.lean` (11)** → `canonical_unique` (A10):
`snocRec`, `natOf_snoc`, `natOf_pos`, `natOf_mod_ten`, `exists_snoc`, `noLead_of_snoc`,
`lt10_of_snoc`, `natOf_inj` (H), `canon_parts`, `canon_not_div_ten`, `canonical_unique`\* (H,47L).

**GAP-2 — `Cjson/Spec/NumSound.lean` (15)** → `scanNumber_sound`; `normNum_denote` also feeds
`NumComplete` (the independence crux — the parser's normaliser lands in the grammar's `SameNum`
class): `natOf_cons_zero`, `natOf_dropWhile_zero`, `mem_takeWhile`, `natOf_append_zeros`,
`split_trailing`, `normNum_denote` (H,60L), `scanDigits_sound`, `scanDigits_lt10'`,
`ofDigits_natOf`, `scanFrac_sound`, `scanExpDigits_sound` (H,48L), `scanExp_sound`,
`scanFrac_lt10`, `scanSign_sound`, `scanNumber_sound`\* (H,91L).

**GAP-2 — `Cjson/Spec/StrSound.lean` (17)** → `parseStrBody_sound'`; the `enc_eq`/`hex4_isHex`/
surrogate-range bridges are reused by `StrComplete`:
`enc_eq`, `hex4_isHex`, `not_surrogate`, `isHigh_range`, `isLow_range`,
`psb_esc34/92/47/98/102/110/114/116` (the 8 escape equations), `psb_esc`, `psb_bad_esc`,
`parseStrBody_sound` (H,148L — the length-indexed engine), `parseStrBody_sound'`\* (4L wrapper).

**GAP-2 — `Cjson/Spec/StructSound.lean` (14)** → `struct_sound` → `parseDoc_sound` (C2):
`isWs_IsWs`, `skipWs_split`, `SStr_ne_nil`, `SValue_ne_nil` (recovers the strict-decrease
measure from the grammar, not the parser), `gate_of`, `hV_step` (H,93L), `hE_step` (H,41L),
`hM_step` (H,69L), `struct_sound`\*, `pv_sound`, `pe_sound`, `pm_sound`, `skipBom_split`,
`parseDoc_sound`\* (C2).

**GAP-2 — `Cjson/Spec/NumComplete.lean` (17)** → `scanNumber_complete`:
`SameNum_symm`, `pow_cancel`, `mul_pow_comm`, `SameNum_trans`, `digitByte_digitVal`,
`Digits_eq_digitBytes`, `Digits_lt10`, `scanDigits_complete`, `head_notDigit_notDot`,
`expTail`, `Digits_head_digit`, `scanExpDigits_complete`, `scanExp_complete`, `scanFrac_complete`,
`scanSign_complete`, `afterIntTail`, `scanNumber_complete`\* (H,63L).

**GAP-2 — `Cjson/Spec/StrComplete.lean` (7)** → `parseStrBody_complete`:
`hex4_complete`, `isHigh_true`, `isLow_true`, `isLow_false_of_high`, `isLow_false_of_not`,
`isHigh_false_of_not`, `parseStrBody_complete`\* (43L).

**GAP-2 — `Cjson/Spec/StructComplete.lean` (21)** → `struct_complete` → `C4` → `adequacy`.
The `_gen` lemmas are the whitespace-tolerant generalizations that replace the canonical-specific
released assembly lemmas (Risk 5):
`skipWs_append_Ws`, `SValue_head`, `head_props`, `SValue_skipWs`, `pv_arr_empty_gen`,
`pv_arr_cons_gen`, `pv_obj_empty_gen`, `pv_obj_cons_gen`, `pe_last_gen`, `pe_cons_gen`,
`pm_last_gen` (H), `pm_cons_gen` (H,39L), `SElems_head`, `SElems_skipWs`, `SMembers_head`,
`SMembers_skipWs`, `safeTail_ws`, `struct_complete`\* (H,163L), `pv_dep`, `C4`\*, `adequacy`\*.

### 4.4 Dependency graph (module level)

```
RELEASED artifact (root: Cjson.lean)
  Basic ─┬─ Printer ── Proofs/Str ─────────────┐
         ├─ Parser ── Proofs/Digits ── Proofs/Num ─┐
         └───────────────────────────────────────  ├─ Proofs/RoundTrip
                                                    │     ├─ roundtrip_value ─ parseDoc_serialize
                                                    │     ├─ parseDoc_depth
                                                    │     └─ parseDoc_idempotent   (T3)
        Parser ── scanNumber_canonical, parseDoc_canonical            (canonicity, T2)

GAP-2 chain (root: Cjson.Spec; imports the released modules above)
  Grammar (declarative; imports Basic + Parser ONLY so C1–C5 Props can *mention* parseDoc)
     │
     ├─ Uniqueness ─ canonical_unique (A10) ──────────────┐
     ├─ NumSound  ─ scanNumber_sound ; normNum_denote ─┐   │
     ├─ StrSound  ─ parseStrBody_sound' ──────────────┐│   │
     │                                                ││   │
     ├─ StructSound (staged hV/hE/hM_step) ─ struct_sound ─ parseDoc_sound  ── C2 ┐
     │                                                     ▲                       │
     ├─ NumComplete ─ scanNumber_complete ────────────────┘ (uses A10,normNum_denote,
     │                                                          released Digits/Num)      │
     ├─ StrComplete ─ parseStrBody_complete (uses StrSound bridges)                       │
     ├─ StructComplete ─ struct_complete ─ C4 (uses scanNumber_complete,                  │
     │                    parseStrBody_complete, released pv/pe/pm + parametric leaves)  ── C4 ┤
     └─ Checks (statement pins; imports Cjson.Spec)                                            │
                                                          adequacy = ⟨ C2 , C4 ⟩ ◀───────────┘
```

**Cross-chain fact:** the GAP-2 proof *depends on* the released artifact (it imports and reuses
`Cjson.Parser`, `Cjson.Proofs.Digits/Num/RoundTrip`). But **`Cjson.Parser` has zero dependency
on the grammar** — no `import`, no reference. The arrow is Parser → Grammar → Theorem, never
inverted (the grammar's only mention of the parser is inside the C1–C5 `example` Props, and no
grammar *definition* uses the parser). This is the independence property adequacy rests on.

---

## 5. Reports inventory

One generated file; all others hand-authored. "Docs-gate" = `verify.sh` step 15
(`check_claims.py`) parses `<!-- claim:key=value -->` markers and byte-compares those numbers
against `results/canonical/claims.json` (generated by `gen_claims.py` from measurements); it
does **not** regenerate prose.

| file | purpose | origin | inputs | reproducibility / gate |
|---|---|---|---|---|
| `ADEQUACY_SUMMARY.md` | exact compiled statements + axioms of the 10 GAP-2 theorems | **GENERATED** by `harness/gap2/gen_adequacy_summary.py` (in-file `DO NOT EDIT` marker) | `gap2_manifest.json` + live `#check`/`#print axioms` | **deterministic; byte-compared** by verify.sh 8d & reproduce.sh via `--check` |
| `README.md` | entry point: toolchain, pins, how to verify | handwritten | prose + 12 claim markers | docs-gate on marked numbers |
| `PAPER.md` | paper-style writeup | handwritten | prose + 7 markers | docs-gate on marked numbers |
| `CLAIMS.md` | every claim tagged PROVEN/MEASURED/OBSERVED/NOT PROVEN | handwritten | prose | scanned by docs-gate (no own markers) |
| `RESULTS.md` | differential measured results | handwritten | measurement JSON via 15 markers | docs-gate (primary target) |
| `GAPS.md` | what is NOT established | handwritten | prose + 1 marker | docs-gate on that number |
| `DIVERGENCES.md` | oracle-vs-Lean behavioural diffs, classified | handwritten | hand-classified observations | scanned by docs-gate |
| `REPORT.md` | narrative engineering report | handwritten | prose + 10 markers | docs-gate on marked numbers |
| `SPEC.md` | the behavioral contract (written before Lean; oracle-verified) | handwritten (APPROVED 2026-07-14) | hand-authored spec | not gated; frozen by approval, not hash |
| `LEDGER.md` | preserved/changed/assumed/UNPROVED ledger — authoritative status | handwritten | prose | not gated |
| `REPRODUCE.md` | reproducibility guide (describes verify.sh steps) | handwritten | prose | not gated |
| `CHANGELOG.md` | version history incl. B1–B3 defect fixes | handwritten | prose | not gated |
| `ADEQUACY_REPORT.md` | GAP-2 result narrative (C2∧C4, what is/isn't proved) | handwritten | prose (1 marker, not gated) | not gated; machine companion = `ADEQUACY_SUMMARY.md` |
| `BLOCKER.md` | string-body soundness blocker + resolutions | handwritten | prose | not gated |
| `INDEPENDENCE_RISK.md` | grammar/parser independence risk register (Risks 1–5) | handwritten | prose | not gated |
| `C4_ARCHITECTURE.md` | design-only C4 architecture (pre-proof) | handwritten | prose + empirical probes | not gated |
| `GAP2.md` | spec-soundness research-phase log | handwritten | prose | not gated |
| `PRE_RELEASE_AUDIT.md` | independent adversarial audit (branch vs v1.0.1) | handwritten | source rebuild | not gated |
| `ARTIFACT_MAP.md` | *this document* | handwritten (freeze snapshot) | the whole repo | not gated |

`harness/JSONTestSuite/**/*.md` are vendored third-party corpus docs (commit `1ef36fa`), not
project artifacts.

---

## 6. Harness inventory

The overriding design theme (documented in the scripts themselves): v1.0.0 shipped several gates
that were **green but dead** (an axiom check that could never fire; `lake build` not rejecting
`sorry`; a docs check comparing the artifact to its own literals; `PORT_WRONG` read off a
non-existent counter; proof modules outside the build target). `harness/mutation_tests.sh` is the
standing evidence that each current gate actually fires.

### 6.1 Driver commands

- **`verify.sh`** — the master release gate (16 steps + GAP-2 8b/8c/8d). Each failure calls
  `die → exit 1`. `--quick` shrinks fuzz/idempotence and skips steps 13–15.
- **`reproduce.sh`** — one command for the GAP-2 proof only: clean `.lake/build`, build the
  released root, build `Cjson.Spec.Checks`, run `check_gap2.py`, run `gen_adequacy_summary.py
  --check`. Exits non-zero on any failure. Wipes stale oleans first.

### 6.2 `verify.sh` gate ladder (what each step fails on)

| # | gate | fails when |
|---|---|---|
| 1 | oracle pinned-input hash | `oracle/cJSON.{c,h}` sha256 ≠ manifest pin |
| 2 | corpus pin | JSONTestSuite unavailable or HEAD ≠ pinned commit |
| 3 | build C oracle | `cc … wrapper.c cJSON.c` fails |
| 4 | clean `lake build` | elaboration/type error (wipes `.lake/build` first) |
| 5 | sorry gate | build output matches `declaration uses \`sorry\`` |
| 6 | axiom gate (`check_axioms.py`) | disallowed axiom / `sorryAx` / marker↔manifest drift / unparseable |
| 7 | banned-construct scan | `sorry`/`admit`/`native_decide`/`@[extern]` in released source |
| 8 | manifest (`check_manifest.py`) | released theorem count ≠ 90 / module not in build / pin/toolchain drift |
| **8b** | GAP-2 statement pins | `lake build Cjson.Spec.Checks` fails (a C2/C4/adequacy statement changed) |
| **8c** | GAP-2 gate (`check_gap2.py`) | disallowed axiom, marker↔manifest drift, Grammar-hash change, Spec count ≠ 102, released file ≠ v1.0.1 |
| **8d** | summary freshness | `gen_adequacy_summary.py --check` byte-mismatch |
| 9–11 | differential (suite/fuzz 120k/idempotence 20k) | harness error |
| 12 | divergence count | any `PORT_WRONG` or `UNCLASSIFIED` on either corpus |
| 13 | regenerate claims | `gen_claims.py` fails |
| 14 | figure gate | a committed SVG ≠ fresh regeneration (`cmp -s`) |
| 15 | docs gate (`check_claims.py`) | a marked number ≠ canonical / phantom / self-contradiction / marker not adjacent to prose |
| 16 | clean tree | `git diff` shows tracked changes |

### 6.3 Gate scripts — responsibility, failure modes, validation evidence

| script | responsibility | fails closed on | validation evidence |
|---|---|---|---|
| `harness/check_axioms.py` | `#print axioms` per released attested decl vs allow-list; marker↔manifest both directions | build fail, sorry warning, probe non-zero, unparseable line, missing decl, disallowed axiom | docstring records the v1.0.0 dead-path (inverted grep could never fire); rebuilds first so stale oleans can't hide a mutation (mutation tests 1,2,3,9,10) |
| `harness/check_manifest.py` | released theorem count, module-in-build, pins, toolchain/packages, artefacts exist | count ≠ 90, module not imported by `Cjson.lean`, hash/commit/toolchain drift, missing artefact | records v1.0.0 bug (proof modules outside build target → "checking zero theorems"); count now released-only after the spec chain broke the old glob (tests 7,10) |
| `harness/gap2/check_gap2.py` | GAP-2 axioms, marker↔`gap2_manifest.json`, Grammar-Prop **hash freeze**, Spec count, **released byte-identity to v1.0.1** | all of the above; `--update-grammar-pin` recomputes the hash | independent of the released gate (verifies the chain the root omits); greedy-regex note for primed names |
| `harness/gap2/gen_adequacy_summary.py` | generate `ADEQUACY_SUMMARY.md` from `#check`/`#print axioms`; `--check` byte-compares | probe non-zero, missing decl output, out-of-date file | whitespace normalized so output is toolchain-stable, not pp-wrap dependent |
| `harness/check_claims.py` | non-circular docs check: `.md` markers vs `claims.json` | missing claims.json, marker-not-adjacent-to-prose, phantom key, self-contradiction, falsified value, unattested key | docstring records v1.0.0 defect (never opened a .md; compared to its own literals); adjacency check defends the human-readable number (tests 4,6) |
| `harness/gen_claims.py` | derive `claims.json` FROM measurements (nothing hardcoded) | any input JSON/source missing/malformed | non-circularity contract: no documented number appears as a literal in it or in `check_claims.py` |
| `harness/run_suite.py` | differential over full JSONTestSuite (agreement + per-binary conformance) | (no exit 1; feeds gate 12) | insists the two measures not be conflated (cJSON lax by design) |
| `harness/fuzz.py` | differential fuzzing, `SEED=20260714`, 120k inputs | (no exit 1; feeds gate 12) | conservative classifier; only `UNCLASSIFIED`/`PORT_WRONG` matter |
| `harness/idempotence.py` | empirical stand-in for the one unmechanized theorem T3 (run binary twice) | (records violations; feeds a claim) | explicitly labelled EVIDENCE not proof |
| `harness/classify.py` | assign exactly one label per differential case | (pure function; emits `UNCLASSIFIED` when no rule matches) | records the v1.0.0 "absence of an absence" (PORT_WRONG had no counter); discloses `TARGET_REL_TOL=1e-15`; human-judgement caveat |
| `harness/gap2/spec_ref.py` | reference grammar decider written from SPEC.md (not the parser) | raises `Reject` vs `HarnessError` (never fail-open) | records a fail-open recursion bug (RecursionError once reported as a grammar rejection); now `setrecursionlimit(50000)` |
| `harness/gap2/hunt.py` | adversarial hunt for a parser↔grammar disagreement (kill C2/C4/value) | (reports findings; nonzero count = finding) | exhaustive short inputs + boundary nesting 998–1002 + corpus + 20k mutations |
| `figures/make_figures.py` | 3 deterministic SVGs from `claims.json`/`fuzz_results.json` | raises if a canonical JSON missing | determinism is load-bearing; byte-gated (tests 5,6) |
| `harness/mutation_tests.sh` | **meta-gate**: 20 attacks each mutate the repo and require the gate to FAIL, + 1 control that must PASS; restores via `git checkout` trap | a mutated artifact PASSES a gate (BYPASS), or clean tree FAILS, or tree dirty at start | this IS the validation that every gate fires |
| `.github/workflows/verify.yml` | CI: clean build + GAP-2 build/gate + `verify.sh` + `mutation_tests.sh` + tree-clean | any step non-zero; honest note that the `v*` trigger can't fire for v1.0.1 (predates workflow) so it asserts byte-identity to the tag instead | elan downloaded outside the workspace so the clean-tree gate isn't tripped |

### 6.4 The oracle

`oracle/cJSON.{c,h}` — **unmodified** upstream cJSON (commit `fb16e5cf…`, sha256-pinned in
`release/manifest.json`, `PROVENANCE.txt`). `oracle/wrapper.c` is a differential CLI: stdin =
bytes; exit 0/1/2/3 = parse+print ok / parse fail / print fail / harness error; success prints
`cJSON_PrintUnformatted()` with no newline. Entry point `cJSON_ParseWithLength(buf, len+1)` over
a NUL-appended copy (the buffer `cJSON_Parse` builds). Built at verify.sh step 3; invoked by
`run_suite.py`/`fuzz.py`/`diff.py` against the Lean binary `lean/.lake/build/bin/cjson`.

---

## 7. What the artifact as a whole does NOT prove

Consolidated from the per-theorem "does NOT prove" columns and the ledgers:

1. **A fully verified JSON parser.** The proved property is *adequacy relative to the frozen
   `Grammar.lean`* — itself a spec that deliberately diverges from RFC 8259 and cJSON.
2. **RFC 8259 conformance / cJSON behavioural equivalence.** The grammar preserves cJSON's lax
   behaviour (whitespace ≤ 32, trailing bytes accepted, lax number scanner, duplicate keys) and
   *deliberately* diverges: **NUM-EXACT** (exact decimal, not IEEE double), **D-STR-1** (reject
   invalid `\uXXXX` — cJSON yields U+0000), **D-STR-2** (NUL non-truncating), **D-FMT** (`e21`
   not `e+21`). Differential agreement with the C oracle is *measured* (§6), not proved.
3. **C3 — maximal munch.** Not proved. C4's `SafeTail` side condition is load-bearing precisely
   because C4 does not pin the *longest* grammatical prefix; a parser choosing a shorter
   grammatical prefix where the tail is number-unsafe is not excluded by C2 ∧ C4.
4. **C5 — rejection completeness (direct).** Not built as a standalone theorem (though it
   follows from C2). Nothing here proves rejection of non-grammatical input by a negative statement.
5. **The compiled binary (GAP-EXTRACT).** Every theorem is about the Lean *function*. The
   binary is produced by Lean's compiler + runtime, neither verified here. Idempotence over
   20,318 inputs is the only bridge, and is EVIDENCE not proof.
6. **IEEE-double semantics, UTF-8 validity, an exponent bound.** Numbers are exact decimals;
   string bytes ≥ 0x80 pass through unexamined; no exponent magnitude limit (GAP-3).
7. **BOM/entry-point choices** beyond the wrapper's `cJSON_ParseWithLength(buf, len+1)` (GAP-4).

**Strongest honest claim:** *adequacy relative to the frozen SPEC grammar, its depth model, its
deliberate semantic choices, and the exclusions above.*

---

## 8. Freeze manifest

- **Theorems:** 192 total = 90 released + 102 GAP-2. **Definitions of note:** parser
  (`parseValue`/`parseElems`/`parseMembers`), `serialize`, and the grammar inductives.
- **Exported/attested:** 11 released (`release/manifest.json`) + 10 GAP-2
  (`release/gap2_manifest.json`). `Grammar` Props frozen by sha256
  `28765891d7985c81c576bc24aeef470300a7388b64810428020e8c50fb4356d5`.
- **Axioms:** every theorem ⊆ `{propext, Classical.choice, Quot.sound}` (§3.1).
- **Released artifact byte-identical to `v1.0.1`:** `Cjson.lean`, `Parser.lean`, `Basic.lean`,
  `Printer.lean`, `Proofs/{Digits,Num,Str,RoundTrip}.lean`, `lakefile.toml`, `lean-toolchain`
  (asserted by `check_gap2.py` against the tag).
- **Rebuild everything from a clean checkout:**

  ```
  ./reproduce.sh          # GAP-2 adequacy: build + axioms + statement pins + summary
  ./verify.sh             # full release gate (16 steps + GAP-2 8b/8c/8d) + differential
  ./harness/mutation_tests.sh   # proof that every gate actually fires
  ```

- **Provenance:** all Lean authored by AI under human mission direction; no human-written
  proofs; human decision points logged in `INDEPENDENCE_RISK.md`, `BLOCKER.md`,
  `C4_ARCHITECTURE.md`, `LEDGER.md`, `SPEC.md` (§3.2).

*End of frozen inventory. This document describes the artifact as of branch `gap2-adequacy-proof`;
it does not itself participate in any verification gate.*
