# ADEQUACY_REPORT.md — GAP-2, branch `gap2-adequacy-proof`

**Target: C2 ∧ C4 (adequacy). Status: A10 proved; number soundness proved; string-body soundness
BLOCKED; structural soundness, C2 and C4 not started.**

v1.0.1 is untouched. Nothing here is released. Zero `sorry`, zero custom axioms, no
`native_decide`, no Mathlib.

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
                                    Cjson/Spec/StrSound.lean     bridge lemmas ✅ / body ⛔
                                                        │
                                              structural soundness  ✗ not started
                                                        │
                                                    C2, C4          ✗ not started
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

hex4_isHex ✅, enc_eq ✅, not_surrogate ✅,
isHigh_range ✅, isLow_range ✅  ──────────> parseStrBody_sound  ⛔ BLOCKED (31-case induct)
                                                        │
                                             SValue/SElems/SMembers soundness  ✗
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
| 1 | `parseStrBody_sound` | **BLOCKED** — 31-case `parseStrBody.induct`. All the *mathematics* is done (`hex4_isHex`, `enc_eq`, the surrogate-range lemmas); what remains is ~400–600 lines of mechanical case plumbing. `BLOCKER.md`. |
| 2 | `SValue` / `SElems` / `SMembers` soundness | not started. `parseValue.induct` has 26 minor premises — the same shape of grind, ~800–1200 lines. |
| 3 | **C2** (value soundness) | not started; follows from 1 + 2 plus a document-level lift. |
| 4 | **C1**, **C5** | corollaries of C2. |
| 5 | **C4** (completeness) | not started; mutual induction on `SValue`, mirrors `roundtrip_value`. ~600–900 lines. |
| 6 | **C3** (maximal munch) | **INTENTIONALLY DEFERRED** — out of the frozen scope. It needs a *negative* statement (no longer grammatical prefix exists) and is a different, harder induction. C2 ∧ C4 do not depend on it. |

Revised estimate for the remainder: **~2,000–2,700 lines**, essentially all of it mechanical
case work, none of it requiring new mathematics.

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

## 6. What it explicitly does NOT certify

* **Nothing about which inputs the parser accepts.** C1, C2 and C5 are all unproved. The GAP-2
  adequacy gap from v1.0.1 is **still open**. Number soundness is a statement about
  `scanNumber`, a component; it says nothing about `parseDoc`.
* **Not the §S2 dispatch gate.** That `+1` and `.5` are rejected at value position is enforced in
  `parseValue`, not `scanNumber`. Unproved.
* **Not maximal munch** (C3, deferred by design).
* **Not completeness** (C4). Every lemma proved so far runs parser → grammar. Nothing yet runs
  grammar → parser, and **soundness without completeness is nearly vacuous here**, because §S5.1
  accepts trailing garbage: a parser that accepted only `null` would be sound.
* **Not strings, arrays or objects.** Only the bridge lemmas exist.
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

## 8. Does C2 ∧ C4 genuinely close the v1.0.1 adequacy gap?

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
weakened it. What has changed is the honest cost estimate: the research phase said ~2,000–2,500
lines; with the return-type shortcut ruled out on independence grounds, it is ~2,000–2,700 lines
of *mechanical* work on top of what is proved here.

**Assessment.** The gate the research phase set (A10) has passed. The obligation that carried the
real intellectual risk (keeping the grammar's number semantics independent of the parser, and
still proving the parser meets them) has been **discharged**. What remains is large, tedious and
mathematically routine — and, importantly, it is now *bounded*: two known induction principles,
31 and 26 cases, with every supporting lemma already in place.

**The adequacy gap is not closed. It is now the only thing between this artifact and a
defensible use of the word "verified", and the path to closing it contains no unknowns.**
