# ADEQUACY_REPORT.md — GAP-2, branch `gap2-adequacy-proof`

**Target: C2 ∧ C4 (adequacy). Status: A10, number soundness, string-body soundness, STRUCTURAL
SOUNDNESS and C2 (value soundness) all PROVED. C4 (completeness) not started — deferred to the
next phase, as instructed. C3 (maximal munch) intentionally deferred.**

v1.0.1 is untouched. Nothing here is released. Zero `sorry`, zero custom axioms, no
`native_decide`, no Mathlib.

**Building the GAP-2 proofs.** The released root `lean/Cjson.lean` is kept **byte-identical to
v1.0.1** (it does NOT import the Spec modules), so a plain `lake build` compiles only the released
artifact. The GAP-2 chain has its own root `lean/Cjson/Spec.lean`; build and axiom-check it with:

```
cd lean && lake build Cjson.Spec            # compiles Grammar, Uniqueness, NumSound, StrSound, StructSound
lake env lean <file with #print axioms>     # audits canonical_unique … parseDoc_sound
```

---

## 1. Proof architecture

The architecture is the one the research phase proposed, **minus** the return-type technique,
which was rejected on independence grounds (`INDEPENDENCE_RISK.md` §Risk 2).

```
SPEC.md ──(written first, oracle-verified)──> Cjson/Spec/Grammar.lean      (declarative, no parser)
                                                        │
                                    Cjson/Spec/Uniqueness.lean   A10  ✅
                                                        │
                                    Cjson/Spec/NumSound.lean     numbers ✅
                                                        │
                                    Cjson/Spec/StrSound.lean     strings ✅ (body + bridges)
                                                        │
                                    Cjson/Spec/StructSound.lean  structural ✅ + C2 ✅
                                                        │
                                                    C2 ✅ ; C4      ✗ not started (next phase)
```

The load-bearing design decision, and the one a reviewer should check first: **the grammar's
number semantics are an equivalence on raw triples (`SameNum : ± m·10^e`), not the parser's
normaliser.** The shortcut — defining the grammar in terms of `normNum` — would have made
`scanNumber_sound` nearly `rfl` and destroyed the independence argument. It was rejected, and
the honest obligation (`normNum_denote`: the parser's normaliser *lands in* the grammar's
equivalence class) was proved instead. That lemma is the crux of this branch.

## 2. Theorem dependency graph

```
natOf_snoc ─┬─> natOf_pos ────────┬─> natOf_inj ──┐
            ├─> natOf_mod_ten ────┤               ├─> canonical_unique   (A10) ✅
            ├─> exists_snoc ──────┤               │
            └─> natOf_append_zeros┘               │
                                                  │
mem_takeWhile ─> split_trailing ──┐               │
natOf_dropWhile_zero ─────────────┼─> normNum_denote ✅ ──┐
head?_dropWhile (v1.0.1) ─────────┘                       │
                                                          │
scanDigits_sound ✅ ─┬─> scanFrac_sound ✅ ──────┐        │
ofDigits_natOf ✅ ───┼─> scanExpDigits_sound ✅ ─┼──> scanNumber_sound ✅  (NUMBER SOUNDNESS)
scanSign_sound ✅ ───┘         └─> scanExp_sound ✅┘      │
normNum_canonical (v1.0.1) ───────────────────────────────┘

hex4_isHex ✅, enc_eq ✅, surrogate-range ✅ ─> parseStrBody_sound ✅  (STRING-BODY SOUNDNESS)
                                                        │
skipWs_split ✅, skipBom_split ✅, SValue_ne_nil ✅, gate_of ✅
scanNumber_sound ✅, parseStrBody_sound' ✅
                          │
  staged Nat.rec:  hV_step ✅ ── hE_step ✅ ── hM_step ✅  ──> struct_sound ✅
                          │                                    (pv_sound/pe_sound/pm_sound)
                          └────────────────────────────────> parseDoc_sound ✅  (C2)
                                                        │
                                                    C2 ✗ ──> C1 ✗, C5 ✗
                                                    C4 ✗
```

## 3. `#print axioms`

```
'Cjson.Spec.canonical_unique'   depends on axioms: [propext, Quot.sound]
'Cjson.Spec.natOf_inj'          depends on axioms: [propext, Quot.sound]
'Cjson.Spec.normNum_denote'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.Spec.ofDigits_natOf'     depends on axioms: [propext, Quot.sound]
'Cjson.Spec.scanDigits_sound'   depends on axioms: [propext]
'Cjson.Spec.scanFrac_sound'     depends on axioms: [propext, Quot.sound]
'Cjson.Spec.scanExpDigits_sound' depends on axioms: [propext, Quot.sound]
'Cjson.Spec.scanExp_sound'      depends on axioms: [propext, Quot.sound]
'Cjson.Spec.scanSign_sound'     depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.Spec.scanNumber_sound'   depends on axioms: [propext, Classical.choice, Quot.sound]
'Cjson.Spec.hex4_isHex'         depends on axioms: [propext, Quot.sound]
'Cjson.Spec.enc_eq'             depends on axioms: [propext]
```

Lean's standard axioms only. **No project axiom. No `sorry`.** `Grammar.lean`'s five candidate
theorems (C1–C5) are stated as `Prop`-valued `example`s: they elaborate, and **none is asserted**.

## 4. Remaining proof obligations

| # | obligation | status |
|---|---|---|
| 1 | `parseStrBody_sound` | ✅ **PROVED** (architecture 1, previous run). |
| 2 | `SValue`/`SElems`/`SMembers` soundness | ✅ **PROVED.** Single `Nat.rec` on a length bound with a 3-stage successor step (`hV_step`, `hE_step`, `hM_step`). The same-length `parseElems → parseValue` call is closed by establishing value soundness at `n+1` *before* element soundness at `n+1`; the strict decrease is recovered from `SValue_ne_nil`, not the parser's stripped subtype. |
| 3 | **C2** (`parseDoc_sound`) | ✅ **PROVED** as a direct consequence of `pv_sound` plus `skipBom_split`/`skipWs_split` and the released `parseDoc_depth`. |
| 4 | **C1**, **C5** | corollaries of C2; **not built** (out of frozen scope this run). |
| 5 | **C4** (completeness) | **not started — the next phase's target.** Mutual induction on `SValue`, mirrors `roundtrip_value`. This is the remaining half of adequacy. |
| 6 | **C3** (maximal munch) | **INTENTIONALLY DEFERRED** — out of the frozen scope. It needs a *negative* statement (no longer grammatical prefix exists) and is a different, harder induction. C2 ∧ C4 do not depend on it. |

Revised estimate for the remainder: **~2,000–2,700 lines**. **The remaining obligations are
structurally understood, but their difficulty and truth remain unestablished until mechanised.**

## 5. What the proof certifies (today)

* **A10.** Two canonical `JNum`s denoting the same exact decimal are equal. Therefore *the value
  the grammar assigns* is well-defined and **C2 is well-posed**. This was the go/no-go gate and
  it passed.
* **Number soundness.** For every input the parser's number scanner accepts, the bytes it
  consumed form a token that the **SPEC grammar** — written from the spec, not from the parser,
  and independently validated against the third-party C oracle on 8,847/8,849 inputs — assigns
  **exactly** the value the parser returned.

  This is the piece the research phase identified as *the hard part*, and it is the piece where
  the independence contract was actually under pressure. It held.
* **String-body soundness.** For every input `parseStrBody` accepts, the consumed bytes form a
  string body that the independent `SChars` grammar decodes to exactly the byte string returned.
  Not vacuous, and demonstrably so: **this theorem is FALSE of the C oracle**, which accepts
  `"\uZZZZ"` as U+0000 while `SChars.uni` demands four valid hex digits.
* **Structural soundness + C2.** For every document `parseDoc` accepts, `s` decomposes as
  `bom ++ ws ++ valuePrefix ++ trailing` with the value prefix denoting exactly the returned `v`
  under the independent SPEC grammar, and `jdepth v ≤ 1000`. This is the piece that finally
  connects the parser's *top-level entry point* to the grammar — every earlier lemma was about a
  scanner or a component.

## 6. What it explicitly does NOT certify

* **Completeness (C4).** Every lemma proved runs parser → grammar. **Nothing yet runs
  grammar → parser.** Because §S5.1 accepts trailing garbage, `SAccepts` is an existential over
  prefixes, so C2 *alone* is satisfiable by a parser that accepts only `null`. **C2 is one half of
  adequacy; C4 is the other and is not started.** The GAP-2 adequacy gap from v1.0.1 is therefore
  **still open** — narrowed to completeness.
* **Rejection properties.** C5 (`¬SAccepts s → parseDoc s = none`) is a corollary of C1/C2 but was
  **not built** this run (frozen scope). Nothing here proves the parser *rejects* a non-grammatical
  input; that reading of "the parser accepts the right language" awaits C4 + C5.
* **The §S2 dispatch gate as a rejection.** C2 *uses* the gate as a discharged hypothesis; it does
  not prove `+1`/`.5` are rejected. That is a completeness-side statement.
* **Not maximal munch** (C3, deferred by design).
* **Not completeness** (C4). Every lemma proved so far runs parser → grammar. Nothing yet runs
  grammar → parser, and **soundness without completeness is nearly vacuous here**, because §S5.1
  accepts trailing garbage: a parser that accepted only `null` would be sound.
* **Not arrays or objects.** Structural soundness is not started, so nothing yet connects
  `parseValue`/`parseDoc` to `SValue`/`SDoc`.
* **Nothing empirical is being cited as proof.** The 55,589-input hunt from the research phase is
  evidence that no counterexample exists; it is not, and is nowhere claimed to be, a proof.

## 7. Semantic changes considered and rejected

Two, both recorded in `INDEPENDENCE_RISK.md`. **Neither was made.**

1. **Define the grammar's number semantics as `normNum`.** Would have made `scanNumber_sound`
   trivial in its interesting component and turned the theorem into "the parser's number is the
   parser's number". Rejected; `normNum_denote` was proved instead.
2. **Carry the `SValue` witness in the parser's return type.** The technique that gave fuel-free
   totality (v1.0.0) and closed GAP-1 (v1.0.1), and which would very likely finish C2. Rejected
   because it **inverts the independence arrow**: `Cjson.Parser` would import the grammar, C2
   would become a projection, and the parser would be *made to carry the answer*.

   The asymmetry is worth stating precisely, because it is the intellectual content of this
   branch: in v1.0.1 the invariant carried in the type (canonicity) was **our own internal
   invariant**, so carrying it proved something real. Here the invariant would be **the
   specification we are supposed to be checking the parser against**. Carrying that is assuming
   the conclusion. The same technique is sound in one case and circular in the other.

   This is why the string and structural proofs are *blocked and slow* rather than *fast and
   worthless*.

## 8. Progress toward closing the v1.0.1 adequacy gap

**Yes — and nothing short of both does.**

v1.0.1's own self-criticism: *"a parser that accepted every byte string and returned `null` would
satisfy T0–T3 exactly as well as this one does."*

* **C5** (a corollary of C2) refutes that parser: if no prefix of `s` is grammatical, `parseDoc s`
  must be `none`. **No v1.0.1 theorem does this.**
* **C2** goes further: the value returned is the one the grammar assigns, not merely *some* value.
* **C4** is indispensable. Because §S5.1 accepts trailing garbage, `SAccepts` is an existential
  over prefixes, so soundness alone is satisfiable by a lazy parser that accepts only `null`.
  C4 forces the parser to accept everything the language contains.

So the pair is the right target, and **it remains the right target** — this branch has not
weakened it. **C2 is now PROVED; C4 is not.** Half of adequacy is mechanised. The remaining
obligation (C4 completeness) is structurally understood — a mutual induction on `SValue` mirroring
`roundtrip_value` — but its difficulty and truth remain unestablished until mechanised.

**Assessment.** The gate the research phase set (A10) has passed. The obligation that carried the
real intellectual risk (keeping the grammar's number semantics independent of the parser, and
still proving the parser meets them) has been **discharged**. What remains is large and is now *bounded* in shape — two known induction principles, 31 and 26
cases, with every supporting lemma in place. **But the remaining obligations are structurally
understood, not routine: their difficulty and truth remain unestablished until mechanised.**

**The adequacy gap is not closed.** It is the only thing between this artifact and a defensible
use of the word "verified". The path to closing it is structurally understood — but its
difficulty and truth remain unestablished until mechanised.


---

## 9. C4 completeness — architecture assessment (design run, no proof code)

Full design in **`C4_ARCHITECTURE.md`**. Summary:

* **C4 statement** (`Grammar.lean:243`): `SValue p v → DepthOk v → SafeTail rest →
  ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩`. The inline tail condition is
  definitionally `SafeTail` (`Num.lean:133`).
* **Truth: TRUE and well-posed.** No missing premise; nothing to weaken. `SafeTail` is exactly
  calibrated (stops number extension; permits trailing garbage; byte-class only, not circular).
  `DepthOk` (≤1000) exactly matches parser depth-0 acceptance. A10 supplies number-value
  uniqueness. Confidence probes (parser binary) all consistent; **no counterexample**, so no
  `C4_COUNTEREXAMPLE.md`.
* **Central finding:** `roundtrip_value` (v1.0.1, `RoundTrip.lean:469–481`) already proves C4's
  *exact* shape (`SafeTail` + `d + jdepth v ≤ nestingLimit`) **specialised to `serialize v`**.
  C4 = that theorem generalised from the canonical rendering to an arbitrary grammatical `p`. The
  structural assembly lemmas (`pv_arr_cons`, `pe_cons`, `pm_cons`, …) are therefore **already
  proven**; the two genuinely new pieces are the leaf lemmas **`scanNumber_complete`** and
  **`parseStrBody_complete`** (converses of the soundness scanners, for *arbitrary* grammatical
  spellings, not just the canonical one).
* **Recommended architecture:** one mutual structural induction on `SValue.rec` (3 motives), depth
  threaded as `d + jdepth ≤ nestingLimit`, `SafeTail` on the value motive only (element/member
  motives self-terminate on `]`/`}`). No staging (unlike soundness) — the grammar derivation is the
  well-founded measure, so the same-length hazard that forced staging in soundness does not arise.
* **Independence:** preserved by construction (views only; no parser/grammar change; no witness
  carried). The one risk is the `scanNumber_complete` shortcut (proving it only for the canonical
  rendering would narrow the grammar's byte-freedom) — to be avoided, and recorded in
  `INDEPENDENCE_RISK.md` only if reached for.
* **Estimated size:** ~1000–1400 lines; top risk `scanNumber_complete` (exact-consumption of an
  arbitrary `SNumTok`). Proposed thin slice: `null`, then empty array.

**C4 remains unproved.** This run designed its architecture; the difficulty and truth of the two
hard leaf lemmas remain unestablished until mechanised.

### C4 leaf progress (2026-07-15): `scanNumber_complete` PROVED

The highest-risk C4 leaf identified in the architecture run is **done**:
`scanNumber_complete : SNumTok p n → SafeTail rest → scanNumber (p ++ rest) = some (n, rest)`,
for arbitrary grammatical spellings (grammar unmodified). `#print axioms` → `[propext,
Classical.choice, Quot.sound]`. Zero `sorry`. Built via: (1) `SameNum` symm/trans algebra;
(2) a digit bridge (`Digits ip ids → ip = digitBytes ids`) reusing the released
`scanDigits_digitBytes`; (3) converse completeness for each scanner (`scanSign`, `scanDigits`,
`scanFrac`, `scanExpDigits`, `scanExp`); (4) assembly, with the value closed by
`normNum_denote` + `SameNum_symm`/`_trans` + **A10**. Independence preserved: the hypothesis is
the unchanged `SNumTok`, and no grammar/parser definition was touched.

Remaining for C4: `parseStrBody_complete` (the other leaf) and the structural mutual induction
(assembly lemmas already exist in v1.0.1). C4 is expected to close via the architecture in §8–10
unchanged, now that its hardest leaf is proved.

### C4 leaf 2 (2026-07-15): `parseStrBody_complete` PROVED

Both hard C4 leaves are now done. `parseStrBody_complete : SChars body v → ∀ rest,
parseStrBody (body ++ 34 :: rest) = some (v, rest)`, for arbitrary grammatical spellings
(grammar unmodified). `#print axioms` → `[propext, Classical.choice, Quot.sound]`. Zero `sorry`.
Direct induction on `SChars.rec`, covering all 5 constructors (nil / plain / esc / uni / pair);
reuses the released reverse escape equations and `enc_eq`, adds `hex4_complete` + surrogate-range
converses. Independence confirmed concretely: escaped `\/` (via `SChars.esc`) and unescaped `/`
(via `SChars.plain`) both decode to `/` and both go through the *same* theorem — the grammar's
spelling-freedom is preserved, not collapsed to the serializer's canonical form.

**Both C4 leaves (`scanNumber_complete`, `parseStrBody_complete`) are proved.** The remaining C4
work is the structural mutual induction lifting these (plus the literal/array/object cases) to
`parseValue`/`parseDoc` — whose assembly lemmas already exist in v1.0.1 (`pv_arr_cons`, `pe_cons`,
`pm_cons`, …). The §8 architecture remains unchanged; full structural completeness can now begin.