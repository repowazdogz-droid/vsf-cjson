# PRE_RELEASE_AUDIT.md

Independent adversarial pre-release audit of the GAP-2 adequacy result.
Branch `gap2-adequacy-proof` audited against tag `v1.0.1`. Everything below was
rebuilt and re-checked from source; no summary, report, or claimed axiom output
was trusted. Nothing was modified, committed, pushed, or tagged. This report file
is the sole new artifact.

- Auditor build: Lean **4.32.0** (`leanprover/lean4:v4.32.0`), Lake 5.0.0, arm64-darwin.
- HEAD: `4731c0d43e06666b51108dff278f756dc2820063` (branch `gap2-adequacy-proof`)
- v1.0.1: `6c0b6b192abe115e3b7e4da1ff315ef6ccc8211b`

---

## 1. Executive verdict

### VERDICT: **PASS WITH TECHNICAL FIXES**

The mathematics is sound and independently reproduced. `C2 ∧ C4` (adequacy relative
to the frozen SPEC grammar) is machine-checked; the theorems inhabit the **exact**
Props declared in `Grammar.lean`; only Lean's three standard axioms appear; the
grammar is genuinely independent of the parser; completeness genuinely covers
arbitrary (non-canonical) grammatical spellings; the released v1.0.1 artifact is
byte-identical. **No mathematical or claim defect was found in the core result.**

It is **not** a plain PASS because the audited result is not in a releasable state:

1. **The proof is uncommitted.** `lean/Cjson/Spec/StructComplete.lean` — which
   contains `struct_complete`, `C4`, and `adequacy` — is an **untracked** file, and
   `lean/Cjson/Spec.lean` (the import that pulls it in) is **modified but uncommitted**.
   Four record files are likewise uncommitted. The primary claim currently exists only
   in the working tree.
2. **No automated gate covers the adequacy chain.** `verify.sh` and `.github/workflows/verify.yml`
   run the default `lake build`, which builds the released `Cjson` root; that root does
   **not** import `Cjson.Spec`, so C2/C4/adequacy are never elaborated by CI, and no
   GAP-2 theorem is in the `@attested` axiom-gated set. The adequacy proof is verified
   only by the separate, un-gated command `lake build Cjson.Spec`.

Both are release-blocking process gaps, not proof defects. Fix them (commit; wire the
Spec chain into CI/verify.sh with a sorry+axiom gate) and the result is releasable
under correctly qualified wording (§11).

---

## 2. Exact verified claim

Proved, machine-checked, standard axioms only:

```
adequacy : (∀ s v, parseDoc s = some v → SDoc s v)          -- C2 (Grammar.lean:229)
         ∧ (∀ p v rest, SValue p v → DepthOk v →            -- C4 (Grammar.lean:243-246)
              (∀ c t, rest = c :: t →
                 isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
              ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩)
```

Honest reading: **the released parser is adequate with respect to the frozen
`Grammar.lean` specification** — every accepted document denotes the value the grammar
assigns to the consumed prefix (C2), and every grammatical value within the depth limit,
followed by a number-safe tail, is accepted at exactly those bytes (C4). This is
adequacy **relative to that grammar, its depth model, its deliberate divergences
(NUM-EXACT, D-STR-1/2, D-FMT), and its explicit exclusions** — NOT a fully verified
JSON parser, NOT RFC 8259 conformance, NOT behavioural equivalence to cJSON, and NOT
C3 (maximal munch) or C5 (rejection).

---

## 3. Build and repository integrity

**Repository state.**
- `git merge-base --is-ancestor v1.0.1 HEAD` → v1.0.1 IS an ancestor of HEAD.
- Committed diff `v1.0.1..HEAD`: adds the GAP-2 spec tree (`lean/Cjson/Spec/*`), the
  harness, four reports, CI workflow; modifies `LEDGER.md`. **No released `.lean`,
  lakefile, or toolchain file is in the committed diff.**
- **Uncommitted working tree** (`git status --porcelain`):
  `?? lean/Cjson/Spec/StructComplete.lean` (untracked — the C4/adequacy proof),
  `M lean/Cjson/Spec.lean`, `M ADEQUACY_REPORT.md M BLOCKER.md M INDEPENDENCE_RISK.md M LEDGER.md`.
  **→ Finding F1: the load-bearing proof file is untracked; the claim is not committed.**

**Released / core byte-identity (working tree `git hash-object` vs `v1.0.1:` blob).**

| file | status |
|---|---|
| `lean/Cjson.lean` | SAME (`ebbb30ff5c82`) |
| `lean/Cjson/Parser.lean` | SAME (`aa72ec027948`) |
| `lean/Cjson/Basic.lean` | SAME (`835a2d21eb6d`) |
| `lean/Cjson/Proofs/RoundTrip.lean` | SAME (`77cc0d74d7a4`) |
| `lean/Cjson/Proofs/Num.lean` | SAME (`7cddfe58a9de`) |
| `lean/Cjson/Proofs/Digits.lean` | SAME (`ca7051247e79`) |
| `lean/Cjson/Proofs/Str.lean` | SAME (`b8832078954a`) |
| `lean/lakefile.toml` | SAME (`927e70157316`) |
| `lean/lean-toolchain` | SAME (`94b9f495baff`, = `leanprover/lean4:v4.32.0`) |

`Grammar.lean` is not in the uncommitted-modified set, so **the grammar was not touched
by the uncommitted proof work.** The "v1.0.1 byte-identical" claim for the released
parser/serializer/proofs/toolchain is **TRUE**.

**Clean build (`.lake` removed first).**
- `rm -rf lean/.lake && lake build` (released root) → `Build completed successfully (20 jobs)`, ~6 s.
- `lake build Cjson.Spec` (adequacy chain, incl. untracked `StructComplete.lean`) →
  `Build completed successfully (17 jobs)`, ~3 s.
- No external dependencies (`lake-manifest.json` packages: `[]`); "Std only" = Lean's
  bundled Std, no lake deps, no Mathlib.
- **Two non-fatal lint warnings** (unused simp argument): `NumSound.lean:306`,
  `NumComplete.lean:278`. Cosmetic. → Finding F3 (minor).

**CI/verify coverage.** `.github/workflows/verify.yml` and `verify.sh` run `lake build`
(default target = released `Cjson`). That root does **not** import `Spec`. → **Finding F2:
the adequacy chain is built/gated by neither CI nor `verify.sh`.**

---

## 4. Theorem statement audit

Independently confirmed by a fresh file that copies the `Grammar.lean` Props **verbatim**
and assigns the theorems (elaboration = inhabitation; any drift would fail to typecheck):

- `parseDoc_sound` inhabits the exact **C2** Prop `∀ s v, parseDoc s = some v → SDoc s v`. ✔
- `C4` inhabits the exact **C4** Prop, including the dependent field
  `∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩`. ✔
- `adequacy.1 : C2` and `adequacy.2 : C4` — `adequacy` is **literally** `C2 ∧ C4`. ✔
- **Depth premise is exactly the grammar's**: `DepthOk v ↔ jdepth v ≤ nestingLimit` holds
  by `Iff.rfl`; `nestingLimit = 1000` (`Basic.lean:127`), matching `CJSON_NESTING_LIMIT`.
  C4 uses `DepthOk` directly; `struct_complete` at `d = 0` reduces `0 + jdepth v ≤ nestingLimit`
  to it. No stronger or weaker bound was substituted. ✔
- **Dependent field preserved / not weakened.** The `∃ h` in C4 is the parser's real `Res`
  subtype witness `rest.length < (p++rest).length ∧ Canonical v ∧ jdepth v ≤ nestingLimit - 0`,
  reconstructed by `pv_dep` from the actual `parseValue` result — not erased or trivialised. ✔
- **No friendlier restatement / narrowing.** `struct_complete` quantifies over all `SValue p v`
  (13-case induction on `SValue.rec`); `C4` is proved for the exact declared Prop, not a
  canonical-only or serializer-image specialisation (see §6, §8). ✔
- **`pv` is the released parser**: `pv d s := (parseValue d s).map Subtype.val`
  (`RoundTrip.lean:20`) — no shadow parser. ✔

---

## 5. Axiom audit

`#print axioms`, run by the auditor on a fresh `import Cjson.Spec`:

```
canonical_unique      : [propext, Quot.sound]
scanNumber_sound      : [propext, Classical.choice, Quot.sound]
parseStrBody_sound'   : [propext, Quot.sound]
struct_sound          : [propext, Classical.choice, Quot.sound]
parseDoc_sound        : [propext, Classical.choice, Quot.sound]   -- C2
scanNumber_complete   : [propext, Classical.choice, Quot.sound]
parseStrBody_complete : [propext, Classical.choice, Quot.sound]
struct_complete       : [propext, Classical.choice, Quot.sound]
C4                    : [propext, Classical.choice, Quot.sound]
adequacy              : [propext, Classical.choice, Quot.sound]
```

Only Lean's three documented standard axioms. **No `sorryAx`** (a reachable `sorry`
would surface it), **no `Lean.ofReduceBool`** (the marker `native_decide` would add),
**no custom axiom**. `propext`/`Quot.sound` enter via `simp`/quotient types;
`Classical.choice` via `omega` and well-founded recursion. Trusted base is exactly
Lean core.

**Forbidden-construct scan** (whole tree, executable vs comment): every textual hit for
`sorry`/`axiom`/`native_decide` is inside a docstring or a `--` comment explaining the ban.
`grep` for executable `sorry|admit|native_decide|unsafe|partial|^axiom |^opaque |@[extern]|import Mathlib`
across `Cjson/` and `Main.lean` → **none in code.** The released parser uses well-founded
recursion (no `partial`), and `decide` (kernel reduction, permitted) — not `native_decide`.

---

## 6. Independence audit

The parser → grammar → theorem arrow is **intact**; it was not inverted.

- **Grammar does not reference the parser in any definition.** `Grammar.lean` imports
  `Cjson.Parser` *only* so the bottom `example` Props (C1–C5) can mention
  `parseDoc`/`parseValue`; every inductive (`SValue`/`SElems`/`SMembers`/`SChars`/`SNumTok`/
  `Digits`/`ExpPart`) and every def (`SDoc`/`SStr`/`DepthOk`/`Ws`/`enc`/…) is parser-free.
  No grammar constructor encodes a parser execution or carries a parser-success witness.
- **Parser was not changed to carry a grammar witness.** `parseValue`'s return type is
  `Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s` — its **own**
  invariants only; `Parser.lean` has **zero** reference to `SValue`/`Spec` and is
  byte-identical to v1.0.1. The rejected "return-type witness" shortcut (INDEPENDENCE_RISK
  Risk 2) is genuinely unused.
- **Number/string grammars are not narrowed to canonical serialization.** `SNumTok` admits
  leading zeros (`01`), trailing-zero mantissa (`1.0`), all exponent spellings; only the
  *output node* `n` is `Canonical`, tied to the raw triple by `SameNum` (an equivalence on
  `± m·10^e`, **not** the parser's `normNum`). `SChars` admits escaped **and** unescaped `/`
  (`PlainStrByte 47`), mixed-case `\uXXXX`, surrogate pairs, and raw bytes ≥ 0x80.
- **Completeness is NOT derived only for `serialize v`.** `struct_complete` inducts over
  arbitrary `SValue p v`; its proof invokes **only** the whitespace-tolerant `_gen` assembly
  lemmas and the parametric leaves (`pv_null/true/false`, `pv_num_known`, `pv_str_known`,
  `scanNumber_complete`, `parseStrBody_complete`) — verified by extracting every lemma name
  called in the proof body; **no** canonical-specific released lemma (`pv_arr_cons`,
  `pe_last`, …) appears.

**Defective-parser probe.** Because C2∧C4 are theorems *about the specific released parser*,
the meaningful question is what they fail to *exclude*. A parser could satisfy C2∧C4 yet:
(a) pick a non-maximal grammatical prefix where `SafeTail` doesn't pin the split (e.g. on
`1.2.3`, both `1` and `1.2` leave a non-SafeTail tail) — this is exactly **C3**, correctly
not claimed; (b) differ once compiled/extracted — **GAP-EXTRACT**, correctly not claimed.
C2 already *implies* C5 (`¬SAccepts s → parseDoc s = none` follows by contradiction from
`parseDoc s = some v → SDoc s v`), so the "C5 not proved" stance is **conservative, not a
hole**. No defective parser was found that C2∧C4 falsely certify as adequate within the
claimed scope.

---

## 7. Semantic correspondence audit

Checked against primary sources (RFC 8259; pinned cJSON `fb16e5cf…` in `oracle/`; Lean defs):

| aspect | grammar / SPEC | cJSON (pinned) | RFC 8259 | framing |
|---|---|---|---|---|
| numbers | exact decimal `± m·10^e` | `strtod`→`double` (`cJSON.c:309,323`) | decimal, impl-defined precision | **NUM-EXACT** divergence, disclosed; adequacy is w.r.t. exact model, **not** cJSON's lossy double |
| number spellings | lax token grammar (`01`,`1.`,`1e`), `+1`/`.5` gated out at value pos | same lax `strtod` prefix + `-`/digit dispatch | stricter | preserved, disclosed |
| invalid `\uXXXX` | **rejected** (`SChars.uni` needs 4 valid hex) | `parse_hex4` returns 0 → U+0000 (`cJSON.c:688`) | invalid | **D-STR-1** divergence, disclosed |
| embedded NUL | does not truncate | truncates | n/a | **D-STR-2** divergence, disclosed |
| bad UTF-8 / ≥0x80 | passed through unexamined | passed through | forbids | preserved, disclosed |
| duplicate keys | preserved, in order (list, not map) | preserved | undefined | matches (verified: `{ "k":1,"k":2 }` → both) |
| trailing bytes | accepted (`SDoc` = grammatical **prefix**) | `require_null_terminated=0` (`cJSON.c:1179`; wrapper `len+1`) | rejects | preserved, disclosed |
| whitespace | any byte ≤ 32 (`IsWs c := c.toNat ≤ 32`) | `buffer[0] <= 32` (`cJSON.c:1102`) | `{20,09,0A,0D}` | preserved, disclosed |
| BOM | optional leading EF BB BF | `skip_utf8_bom` (`cJSON.c:1172`) | discouraged | matches |
| depth limit | `nestingLimit = 1000` | `CJSON_NESTING_LIMIT 1000` (`cJSON.h:137`) | none | matches |
| formatting | `e21` not `e+21`, etc. | — | both valid | **D-FMT**, disclosed |

The framing is **honest**: adequacy is stated relative to a grammar that deliberately
diverges from both RFC and cJSON in documented ways. The single most consequential framing
point for a reader: the number grammar is **exact-decimal**, so adequacy says nothing about
cJSON's actual `double`-precision behaviour.

---

## 8. Completeness-strength audit (operational, not a substitute for proof)

`pv 0` on non-canonical grammatical spellings (released parser) — all accepted with the
canonical value, confirming C4's `∀ SValue` is not silently specialised:

| input | result |
|---|---|
| `01` | `num ⟨-,[1],0⟩` (=1), fully consumed |
| `1.0e2` | `num ⟨-,[1],2⟩` (=100) |
| `[ 1 , 2 ]` (whitespace) | `arr [1,2]` |
| `{ "k":1 , "k":2 }` | `obj [(k,1),(k,2)]` — **duplicate keys preserved** |
| `"a/b"` (unescaped `/`) | `str [97,47,98]` |
| `"a\/b"` (escaped `/`) | `str [97,47,98]` (identical) |
| `"é"` (mixed-case hex) | `str [195,169]` (é) |
| `"😀"` (surrogate pair) | `str [240,159,152,128]` (U+1F600) |
| `1  trailing garbage` | `num 1`, trailing bytes left (SafeTail permits) |
| `.5` | `none` (dispatch gate) |
| `+1` | `none` (dispatch gate) |

`.5` is admitted by `SNumTok` but excluded at value position by `SValue.num`'s
`c = 45 ∨ isDigitB c` gate — so C4 correctly need not accept it as a value. Consistent.

---

## 9. Reuse-finding audit

The recorded finding is **accurate**. Released `RoundTrip.lean`:
- `pv_arr_cons` requires `hws : skipWs (c :: t) = c :: t` — i.e. `skipWs` is the identity on
  the array interior (no leading whitespace); `serialize` emits none.
- `pe_last` requires `h : pv d s = some (x, 93 :: rest)` — the closer `]` is **literally**
  adjacent to the value.

The generalizations remove the restriction:
- `pv_arr_cons_gen` takes arbitrary `pre` with `hws : skipWs pre = c :: t`.
- `pe_last_gen` takes arbitrary tail `r` with `hw : skipWs r = 93 :: rest`.

`struct_complete`/`C4` invoke only the `_gen` (and parametric-leaf) lemmas — **no canonical-
format assumption survives in C4.** The operational evidence in §8 (interior whitespace
accepted) corroborates this.

---

## 10. Classification of major public-facing claims

| claim | verdict |
|---|---|
| "adequacy (C2 ∧ C4) is proved" | **Proven** (exact Props, standard axioms, reproduced from clean) |
| "C4 is the exact Grammar.lean statement, unweakened, dependent field preserved" | **Proven** |
| "grammar is independent of the parser" | **Proven / structurally verified** |
| "completeness holds for arbitrary grammatical spellings (not just `serialize v`)" | **Proven** (and operationally corroborated) |
| "released v1.0.1 is byte-identical / untouched" | **Proven true** (hashes match; grammar not modified this run) |
| "zero custom axioms / no sorry / no native_decide" | **Proven true** |
| "not a fully verified JSON parser; C3/C5/RFC/cJSON-equivalence not claimed" | **Accurate** (correctly scoped; C5 in fact follows from C2 — conservative) |
| "the two build warnings" | **Empirically confirmed** (cosmetic, unused simp args) |
| "verified" used **unqualified** | Would be **Overstated** — must always carry "relative to the frozen grammar + exclusions" (see §11) |

No claim was found **False**. The only overstatement risk is *wording drift* if "adequacy"
or "verified" is ever stated without the relative-to-grammar qualifier.

---

## 11. Recommended public wording

Safe:
> "The released cJSON-port parser is proved **adequate with respect to its frozen SPEC
> grammar** (Lean 4, `C2 ∧ C4`): every accepted document denotes the grammar's value for
> the consumed prefix, and every grammatical value within the 1000-deep nesting limit,
> followed by a number-safe tail, is accepted at exactly those bytes. Machine-checked under
> Lean's three standard axioms; no `sorry`, no custom axiom. Adequacy is **relative to the
> frozen grammar**, which deliberately diverges from RFC 8259 and cJSON (exact-decimal
> numbers, strict `\uXXXX`, non-truncating NUL, formatting). **Not** claimed: maximal munch
> (C3), rejection completeness (C5), RFC conformance, cJSON behavioural equivalence, the
> compiled binary, or a 'fully verified JSON parser'."

Do **not** say: "verified JSON parser", "proved correct against cJSON", "RFC 8259 compliant",
or "adequacy" without the "relative to the frozen grammar" qualifier.

---

## Required fixes before release

- **[BLOCKER F1] Commit the proof.** `lean/Cjson/Spec/StructComplete.lean` is untracked and
  `lean/Cjson/Spec.lean` is modified. Commit them (and the four updated reports) so the
  audited claim is part of the branch, not loose working-tree state.
- **[BLOCKER F2] Gate the adequacy chain in CI/`verify.sh`.** Add `lake build Cjson.Spec`
  plus a sorry-scan and `#print axioms` gate over `parseDoc_sound`, `scanNumber_complete`,
  `parseStrBody_complete`, `struct_complete`, `C4`, `adequacy` (attest them). As shipped,
  no automated gate builds or checks the primary claim; a future edit could silently break
  it. The CI "working tree clean" gate will also fail until F1 is done.
- **[MINOR F3] Clear the two unused-simp-arg warnings** (`NumSound.lean:306`,
  `NumComplete.lean:278`) so a clean build is warning-free (or document them as accepted).
- **[WORDING] Enforce the §11 qualifier** everywhere "adequacy"/"verified" appears in
  release copy.

None of these is a defect in the proof. With F1–F2 done, the result is releasable.

---

### Auditor note on scope / skills
Adversarial verification only; the proof was not extended or repaired. Per the standing
skill-visibility rule: **no skill fired** — this was direct Lean rebuild/inspection, git
integrity checking, and primary-source (cJSON/RFC) comparison, none of which maps to an
available skill. Nothing was modified, committed, pushed, tagged, or released; the sole new
file is this report.
