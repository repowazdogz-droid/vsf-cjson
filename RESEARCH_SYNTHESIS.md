# RESEARCH_SYNTHESIS.md — GAP-2 final research retrospective

A retrospective on what the GAP-2 project *discovered*, as distinct from what it *built*. Primary
evidence: the Lean sources, `git log`, `GAP2.md`, `INDEPENDENCE_RISK.md`, `BLOCKER.md`,
`ADEQUACY_REPORT.md`, `LEDGER.md`, `CHANGELOG.md`, `PRE_RELEASE_AUDIT.md`, `ARTIFACT_MAP.md`.
Where a summary conflicts with source, source wins.

**Classification.** Every substantive statement carries exactly one tag:
**[MP]** Machine proved · **[ED]** Empirically demonstrated · **[RE]** Repository evidence
(logs/commits/reports) · **[INF]** Inference · **[OQ]** Open question.

---

## Section 1 — Executive Summary

The project attempted to move a Lean 4 re-implementation of cJSON's core from *"self-consistent"*
to *"adequate against an independent specification."* v1.0.1 could already prove the parser was
total, produced canonical output, and round-tripped its own serializer — but, in its own words,
*"a parser that accepted every byte string and returned `null` would satisfy those theorems
exactly as well."* **[RE]** GAP-2 set out to close that hole. **[RE]**

What it ultimately established, machine-checked: an **independent declarative grammar**
(`Grammar.lean`), and **adequacy** = `C2 ∧ C4` against it — soundness (`parseDoc_sound`: every
accepted document denotes, under the grammar, the value returned) and completeness (`C4`: every
grammatical value within the depth limit, followed by a number-safe tail, is accepted at exactly
those bytes). **[MP]** Both directions were needed: because §S5.1 accepts trailing garbage,
soundness alone is satisfiable by a parser that accepts only `null`, so completeness is what makes
the claim non-vacuous. **[MP for C2/C4; INF for the vacuity argument]**

What remains outside the boundary: **maximal munch (C3)** and **rejection completeness (C5) as a
direct theorem** were not proved; equivalence to RFC 8259 or to cJSON's actual (IEEE-double)
behaviour was not proved; the compiled binary is unverified (all theorems are about the Lean
function). **[RE]** The grammar itself deliberately diverges from both RFC and cJSON in documented
ways (exact-decimal numbers, strict `\uXXXX`, non-truncating NUL, formatting). **[RE]**

**Strongest honest claim:** *the released parser is adequate with respect to the frozen SPEC
grammar — its depth model, its deliberate semantic choices, and its explicit exclusions — not a
fully verified JSON parser.* **[MP for adequacy; INF for the scoping]** The single most important
qualifier, established empirically, is that this grammar's accept-set matches a third-party C
oracle on 99.977% of 8,849 probes, so "the language SPEC.md describes" is anchored externally at
the accept/reject level — but the number *value* semantics and two string divergences are anchored
only to our own design. **[ED]**

---

## Section 2 — Timeline of Intellectual Progress

Reconstructed from `git log` (13 commits, v1.0.0 → `362b7d7`) and the logs. Each turning point:
previous belief → new evidence → resulting change.

**T0. v1.0.0 shipped "verified"; hostile audit rejected it.** **[RE]**
Previous belief: the mathematics being clean (no `sorry`, standard axioms) meant the artifact was
sound. New evidence: six harness defects — the axiom gate's inverted `grep` could never fire, so an
injected `evilAxiom` in `parseDoc_idempotent` printed on screen and still passed; `lake build`
does not reject `sorry`; the docs check never opened a `.md`; figures could drift; corpus unpinned;
`--quick` dirtied results. **[RE]** Change: v1.0.1 rebuilt the *harness* (`check_axioms.py`,
manifest, `gen_claims`/`check_claims`, figure gate, pinned corpus, `classify.py`, and
`mutation_tests.sh` — "20 attacks; every gate must FAIL"). **The mathematics was unchanged.** **[RE]**

**T1. GAP-2 research phase: C1 is the wrong theorem.** **[RE]**
Previous belief (the mission's literal ask): prove `parseDoc s = some v → SAccepts s` (C1). New
evidence: C1 only says *some* prefix is grammatical and says nothing about the value; a lazy parser
returning `null` satisfies it. The right target is `C2 ∧ C4` (adequacy); C1 and C5 are corollaries
of C2. **[RE, and C2⇒C5 is INF]** Change: target reset to A10 + C2 + C4; **C3 dropped at planning
time** and logged (it needs a negative statement). **[RE]**

**T2. A10 named as a go/no-go gate before any proof.** **[RE]**
Previous belief: canonical-representative uniqueness is "obviously true." New evidence: C2 says the
parser returns *the* value, which is only well-defined if a canonical `JNum` is unique per number —
a **proof obligation, not something testable.** **[RE]** Change: A10 (`canonical_unique`) proved
first; it held. **[MP]**

**T3. Counterexample hunt found nothing — but first found an instrument bug.** **[RE/ED]**
55,589 adversarial inputs (exhaustive short strings, all 318 corpus files, per-branch attacks,
depth boundaries 998–1001, 20k mutations) produced **0 soundness / 0 value / 0 completeness
violations**, with a positive control: the same hunt aimed at the C oracle finds the known cJSON
bugs. **[ED]** But the first `spec_ref.py` caught Python's `RecursionError` as a grammar rejection —
a fail-open bug that would have manufactured phantom violations at depth. **[RE]** This was logged
as *"the sixth instrument failure of the project and the same shape as all the others: fail-open,
in the harness, not in the mathematics."* **[RE]**

**T4. The planned proof architecture was rejected mid-flight.** **[RE]**
Previous belief (`GAP2.md` Phase 4): reuse the return-type-witness device that gave fuel-free
totality and closed GAP-1 — extend `parseValue`'s `Res` predicate with `∃ pre, s = pre ++ r ∧
SValue pre v`. New evidence (`INDEPENDENCE_RISK.md` Risk 2): that **inverts the independence arrow**
— the parser would import the grammar and carry the answer, making soundness a projection. Change:
**rejected**; soundness re-proved by a *staged length induction* over plain-Option views
(`pv`/`pe`/`pm`), with the strict-decrease measure recovered *from the grammar* (`SValue_ne_nil`),
not the parser. **[RE; the proofs themselves MP]**

**T5. String-body soundness blocked, then unblocked by a different architecture.** **[RE]**
Previous belief: `parseStrBody.induct` (31 minor premises) is the route. New evidence: the generated
induction principle is an unmanageable, plumbing-heavy grind, and `tauto` (which would discharge the
8-way escape disjunction) is Mathlib. **[RE]** Change (`BLOCKER.md`): abandoned functional induction
for a **strong induction on input length** with by-hand byte dispatch, collapsing the eight escapes
into one lemma. Proved. **[MP]**

**T6. The completeness "mirror roundtrip_value" plan was partly wrong.** **[RE]**
Previous belief (`GAP2.md` step 6): C4 mirrors `roundtrip_value`; its assembly lemmas
(`pv_arr_cons`, `pe_last`, …) are "already proven." New evidence (reuse audit,
`INDEPENDENCE_RISK.md` Risk 5): those lemmas are **canonical-specific** — they assume `skipWs
(c::t) = c::t`, i.e. no interior whitespace, because `serialize` emits none. They cannot assemble
`[ 1 , 2 ]`. Change: proved whitespace-tolerant generalizations (`pv_arr_cons_gen`, … `pm_cons_gen`);
`struct_complete` uses only these and the parametric leaves — never a canonical-specific lemma.
**[RE; the generalizations MP]**

**T7. Adequacy proved — then the audit found it uncommitted and ungated.** **[RE]**
Previous belief: proving `C4`/`adequacy` completed the work. New evidence
(`PRE_RELEASE_AUDIT.md`): the load-bearing file `StructComplete.lean` was **untracked** and the
adequacy chain was built by **no CI/`verify.sh` gate** (the released root doesn't import `Spec`; no
GAP-2 theorem was attested). The project's own thesis — the harness is the weak link — recurred at
the finish line. **[RE]** (Confirmed from `git`: `StructComplete.lean` did not exist at commit
`4731c0d`; C4/adequacy were committed only at `362b7d7`.) **[RE]**

**T8. Reproducibility integration exposed a pre-existing dead gate.** **[RE]**
New evidence: `check_manifest.py`'s theorem-count gate counted `Cjson/**` including the research
tree, so it expected 90 but the tree already held 171 — the gate had silently broken the moment the
spec chain landed. Change: scoped it to the released set (90), gave GAP-2 its own count (102), added
statement-pin + axiom + grammar-hash gates and a one-command reproducer. **[RE]**

---

## Section 3 — Proven Results (machine-checked only)

All depend only on `{propext, Classical.choice, Quot.sound}`; several use only `{propext,
Quot.sound}`. No `sorryAx`, no custom axiom. **[MP]** (Implementation excluded per instructions.)

**Soundness**
- `parseDoc_sound` (**C2**): `parseDoc s = some v → SDoc s v` — every accepted document decomposes
  as `bom ++ ws ++ prefix ++ trailing` with the prefix denoting `v` under the grammar. **[MP]**
- `scanNumber_sound`, `parseStrBody_sound'`, `struct_sound` (value/element/member) — component and
  structural soundness feeding C2. **[MP]**

**Completeness**
- `C4`: `SValue p v → DepthOk v → SafeTail rest → ∃ h, parseValue 0 (p++rest) = some ⟨(v,rest),h⟩`.
  **[MP]**
- `scanNumber_complete`, `parseStrBody_complete`, `struct_complete` — for **arbitrary grammatical
  spellings** (leading zeros, `1.0e2`, mixed-case `\u`, surrogate pairs, interior whitespace), not
  just `serialize`'s output. **[MP]**

**Adequacy**
- `adequacy` = `⟨parseDoc_sound, C4⟩` = `C2 ∧ C4`, stated as the exact `Grammar.lean` Props. **[MP]**

**Supporting mathematics**
- `canonical_unique` (**A10**): canonical `JNum`s denoting the same exact decimal are equal — makes
  "the value the grammar assigns" well-defined. **[MP]**
- `normNum_denote`: the parser's normaliser lands in the grammar's `SameNum` class — the
  independence crux that lets the grammar keep parser-independent number semantics. **[MP]**
- Released (v1.0.1, retained): `parseDoc_canonical`, `parseDoc_depth`, `parseDoc_idempotent` (T3),
  `parseDoc_serialize`, `roundtrip_value`, `scanNumber_renderNum`, `parseStrBody_renderStr`. **[MP]**

**Release integrity (machine-enforced facts, not theorems)**
- The released parser/serializer/toolchain are byte-identical to tag `v1.0.1`, asserted by
  `check_gap2.py`. **[RE]**
- The frozen grammar Props are pinned by sha256; a statement change breaks `Cjson.Spec.Checks`.
  **[RE]**

---

## Section 4 — Empirical Findings (not proof)

- **The grammar tracks a third party.** Grammar vs the unmodified C oracle: **8,847 / 8,849**
  agree on accept/reject; the 2 disagreements are the one declared intentional divergence
  (D-STR-1). **[ED]** This is the evidence that the grammar is not "whatever `parseDoc` accepts."
- **No counterexample exists (within the probe budget).** 55,589 adversarial inputs → 0 soundness,
  0 value, 0 completeness violations. **[ED]** Positive control: the same hunt on the C oracle finds
  the known cJSON bugs (invalid `\u`→U+0000, `1e400`→null, `1e-400`→0, NUL truncation). **[ED]**
- **Differential agreement (released binary vs oracle).** 116,476/120,000 fuzz and 297/318
  JSONTestSuite agree; `PORT_WRONG = 0`, `UNCLASSIFIED = 0` on both corpora; 0 idempotence
  violations over 20,318 inputs. **[ED]**
- **cJSON behavioural differences catalogued (not bugs to patch, findings).** IEEE-double number
  collapse (`1e400`→null, `1e-400`→0), invalid-`\u`→U+0000, NUL truncation, whitespace = any byte
  ≤ 32, trailing-bytes accepted, duplicate keys preserved. **[ED]**
- **Mutation evidence that the gates fire.** `mutation_tests.sh`: 20 attacks each must be caught
  (custom axiom, section-scoped axiom, `sorry`, falsified doc markers, tampered SVG, stale data,
  broken corpus pin, broken proof, dropped attestation, unattested theorem) + 1 control that must
  pass. **[ED]** For GAP-2 specifically, verified this session: an injected `sorry` on `adequacy`
  surfaced as `DISALLOWED AXIOM(S) ['sorryAx']` and a build-warning; a `True →` added to `C4`'s
  statement failed the build. **[ED]**
- **The proof-size estimate landed.** `GAP2.md` predicted ≈2,000–2,500 Lean lines "comparable to
  the entire existing artifact (2,240)"; the actual spec chain is **2,509** lines vs the released
  **2,248**. **[RE]**

---

## Section 5 — Methodological Discoveries (candidate reusables)

| discovery | why it mattered | appears general? |
|---|---|---|
| **Grammar-as-relation, not a second recogniser** (`SValue : Bytes → JSON → Prop`) | makes "soundness" relate text to *meaning*, not a differential test between two of our own parsers | **[INF] general** to any parser-vs-spec verification |
| **Independence anchored to a third-party oracle, and measured** (8,849 probes, 99.977%) | converts "the spec is independent" from an argument into evidence; localises residual circularity to the number-value layer + 2 divergences | **[INF] general**; the anchor is the reusable idea |
| **Theorem-selection reasoning: adequacy = soundness ∧ completeness** | soundness alone is vacuous when trailing input is accepted; the *pair* is the real claim | **[INF] general** to any lenient/prefix-accepting parser |
| **Views-only + staged length induction** to keep parser and spec independent | avoided inverting the Parser→Grammar→Theorem arrow; recovered the decrease measure from the grammar | **[INF] general** where a return-type-witness would smuggle the conclusion |
| **Semantic ledgers** (`LEDGER.md`, `DIVERGENCES.md`, `INDEPENDENCE_RISK.md`, `BLOCKER.md`) recording rejected shortcuts and their reasons | the negative decisions are the load-bearing ones; without the log they are invisible to a reviewer | **[INF] general** |
| **Regression gates that must be shown to FAIL** (`mutation_tests.sh`) | "a gate that has never been shown to fail is not evidence" — the v1.0.0 lesson made a first-class artifact | **[INF] highly general** |
| **Statement pins by inhabitation** (`Checks.lean`: `example : <verbatim spec Prop> := theorem`) + **spec hash freeze** | catches a weakened/restated theorem at build time, independently of its proof | **[INF] general** to any "the theorem still says what it claims" need |
| **Machine-generated summary from the compiler** (`#check`/`#print axioms` → `ADEQUACY_SUMMARY.md`, byte-compared) | the human-facing statement of results cannot drift from what compiled | **[INF] general** |
| **Byte-identity to a released tag as a gate** | lets a research branch extend an artifact while proving the released core is untouched | **[INF] general** |

---

## Section 6 — AI Performance Analysis

All Lean — definitions, statements, proofs — was AI-authored; there are no human-written proofs.
**[RE]** So the question is *where human direction changed the outcome.* Classified per the mission
taxonomy, from repository evidence only.

**Where AI succeeded without significant intervention** **[RE unless noted]**
- Discharging the mathematics once a target and architecture were fixed: A10, number/string/
  structural soundness, the completeness leaves and the 13-case mutual induction — all reached
  `{propext, Classical.choice, Quot.sound}`, zero `sorry`. **[MP]**
- Self-diagnosis and re-architecture under a constraint: when functional induction (31 premises)
  stalled, the AI itself pivoted to length induction (`BLOCKER.md`). **[RE]**
- Building the harness/reproducibility layer (gates, manifests, generators, one-command reproduce)
  and validating it by mutation. **[RE/ED]**

**Where human guidance materially changed the outcome** (each = one category)
- **Theorem selection** — the human mission set "A10, C2, C4" and *"do not weaken the theorem."*
  The AI justified C2∧C4 over C1, but the target and the no-weakening discipline were imposed.
  **[RE]**
- **Specification** — SPEC.md was frozen and approved (dates, §S6 number decisions) before proof;
  the deliberate divergences D-STR-1/2, NUM-EXACT, D-FMT are human-approved design choices. **[RE]**
- **Proof architecture** — the *hard rule set* (no `sorry`/`admit`/`native_decide`/custom axiom/
  Mathlib; oracle unmodified) forced the AI to reject the return-type-witness shortcut it had
  itself planned (`INDEPENDENCE_RISK.md` Risks 1–2). Without that rule the easy, independence-
  breaking proof would likely have shipped. **[INF from RE]**
- **Semantic clarification** — the human confirmed §S6 ambiguity resolutions (A1–A10); A10 was
  flagged as the go/no-go before proof. **[RE]**
- **Audit** — the human directed an adversarial pre-release audit, which surfaced that the proof
  was uncommitted and ungated (`PRE_RELEASE_AUDIT.md`). **[RE]**
- **Engineering** — the human directed the reproducibility/freeze phases that turned a working-tree
  proof into a gated artifact. **[RE]**
- **Wording** — the human repeatedly imposed claim discipline ("adequacy relative to the frozen
  grammar," not "verified JSON parser"; replace "routine" with "structurally understood but
  unestablished until mechanised"). **[RE]**

**Honest read [INF]:** the AI was strong at *executing* proofs and at *building and even
self-correcting* tooling, but the decisions that protected the result's *meaning* — theorem
choice, independence, and claim scope — were human-imposed constraints the AI would plausibly have
traded away for a faster proof (evidenced by its own planned-then-rejected shortcut).

---

## Section 7 — Negative Results (failures and rejections — these are findings)

- **Rejected architecture: grammar witness in the parser's return type.** The planned Phase-4
  device; rejected because it inverts the independence arrow and makes soundness a projection
  (`INDEPENDENCE_RISK.md` Risk 2). **[RE]**
- **Rejected shortcut: define grammar numbers as `normNum`.** Would make `scanNumber_sound` `rfl` in
  its interesting component; rejected, and the honest obligation `normNum_denote` proved instead
  (Risk 1). **[RE/MP]**
- **Abandoned proof route: `parseStrBody.induct` (31 premises).** Unworkable + needs Mathlib
  `tauto`; replaced by length induction (`BLOCKER.md`). **[RE]**
- **Wrong reuse assumption: `roundtrip_value`'s assembly lemmas.** Believed reusable for C4; found
  canonical-specific (no interior whitespace); generalized versions required (Risk 5). **[RE]**
- **Dropped target: C3 (maximal munch).** Removed from scope at planning; needs a negative
  statement (no longer grammatical prefix exists). **[RE]**
- **Harness/instrument failures (all fail-open, none mathematical):** the v1.0.0 six (axiom gate,
  `lake build`/`sorry`, circular docs, drifting figures, unpinned corpus, `--quick` dirtying) + two
  found *by* the mutation suite (stale `.olean`, backtick `sorry`) + the `spec_ref.py` recursion
  fail-open + the audit's uncommitted/ungated finding + the dead theorem-count gate. **[RE]**
  The recurring shape — *the weak link was always the verification harness, never the proof* — is
  the project's most repeated result. **[INF from RE]**

---

## Section 8 — Remaining Unknowns

**Proved false / definitively excluded**
- Nothing was proved *false*; no theorem target was found unprovable. A10, the one identified
  falsifiability risk, held. **[MP]**

**Unproved (stated, not established)**
- **C3 — maximal munch.** Not proved; C4's `SafeTail` side condition is load-bearing precisely
  because C4 does not pin the longest grammatical prefix. **[OQ / RE]**
- **C5 — rejection completeness as a direct theorem.** Not built, though it *follows from C2*
  (contrapositive of C1). **[INF]**
- **Stronger semantic correspondence.** Number *values* are anchored to our exact-decimal design,
  not to the oracle (which uses IEEE doubles); D-STR-1/2 are anchored only to our decision. Whether
  a value-level external anchor is achievable is open. **[OQ]**
- **The compiled binary (GAP-EXTRACT).** All theorems are about the Lean function; the
  extraction/runtime are unverified. Idempotence over 20,318 inputs is evidence, not proof. **[OQ]**

**Future work (out of scope by instruction — recorded, not proposed)**
- Whether the grammar-as-relation + oracle-anchored-independence method transfers to other parsers
  is untested here (single subject: cJSON). **[OQ]**

---

## Section 9 — Threats to Validity (strongest honest criticism)

- **External validity / single subject.** One parser, one grammar, one author-team. The
  methodological claims (§5) are *inferences* from n=1; none is empirically demonstrated to
  generalise. **[INF]**
- **Specification choices are the artifact's foundation and are ours.** Adequacy is *relative to
  `Grammar.lean`*. SPEC.md, the parser, and the grammar share an author; the only external check is
  the oracle, which covers accept/reject but not number values or the two intentional divergences.
  A reader must read C2 as "implements the language SPEC describes," not "implements JSON." **[RE]**
- **Dependence on frozen semantics.** The whole result is pinned to a specific cJSON commit, a
  specific depth limit (1000), and specific divergence decisions. Change any and the theorems must
  be re-established; the grammar hash-freeze enforces this but does not justify the choices. **[RE]**
- **Parser family.** cJSON is a lenient, prefix-accepting, non-UTF-8-validating C parser. The
  "soundness is vacuous without completeness" insight is sharpest *because* of that leniency; for a
  strict parser the balance of what matters would differ. **[INF]**
- **Reproducibility assumptions.** Reproduction assumes Lean `v4.32.0` behaves identically across
  machines (the summary generator normalises pretty-printing to mitigate this) and that the pinned
  corpus and oracle commit remain fetchable. **[RE]**
- **AI-assisted proof limitations.** The prover produced correct proofs but, by its own logged
  history, planned an independence-breaking shortcut and would have taken it absent the human hard
  rules. The result's *meaning* depended on human constraints the AI did not self-impose. **[INF
  from RE]**
- **"No counterexample" ≠ "no counterexample exists."** 0 violations over 55,589 inputs bounds, but
  does not eliminate, the space; completeness beyond the proved fragment rests on the proof, and the
  proof rests on the frozen spec. **[ED/INF]**

---

## Section 10 — Reusable Contributions (if cJSON vanished tomorrow)

Ranked by likely long-term value. All **[INF]** (generality is inferred from n=1).

1. **"A gate that has never been shown to fail is not evidence"** — mutation-tested verification
   gates as a first-class deliverable. The project's entire failure history is harness fail-open;
   this is the direct antidote and the most transferable idea.
2. **Independence anchored to a third-party oracle and *measured*** — turning "our spec is not a
   paraphrase of our parser" into a number (99.977%), and *localising* the residual circularity
   rather than denying it.
3. **Adequacy = soundness ∧ completeness for lenient parsers** — the recognition that trailing-
   garbage acceptance makes soundness vacuous alone, so the pair is the real theorem.
4. **Independence-preserving proof discipline** — grammar-as-relation, views-only, refusing to
   carry the conclusion in the parser's type; plus the *ledger of rejected shortcuts* that makes
   the discipline auditable.
5. **Statement pins + spec hash freeze + compiler-generated summaries** — cheap, build-time
   defences against a theorem silently changing meaning or a report drifting from what compiled.
6. **Byte-identity-to-a-tag as a gate** — letting a research branch extend a released artifact
   while proving the released core is untouched.

---

## Section 11 — Lessons Learned (grounded, ≤20)

1. In this project every failure was in the harness, never the mathematics — budget verification
   effort accordingly. **[RE]**
2. A verification gate you have never watched fail is not evidence; mutate the artifact and require
   the gate to fail. **[RE/ED]**
3. `lake build` passing means *type-checked*, not *`sorry`-free*; the axiom gate (`sorryAx`) is the
   real check. **[RE]**
4. Axiom checks read `.olean`s — rebuild first or a mutated proof reads the previous build's
   axioms. **[RE]**
5. Match tool output exactly: Lean renders `` `sorry` `` with backticks; a quote-based grep never
   fired. **[RE]**
6. For a prefix-accepting parser, prove completeness too — soundness alone is satisfiable by a
   `null`-returning parser. **[MP/INF]**
7. Pick the theorem before the proof: C1 was too weak; the audit-proof target is C2 ∧ C4. **[RE]**
8. Identify the ill-posedness gate first: A10 (uniqueness) had to hold before C2 even made sense.
   **[MP/RE]**
9. Keep the specification a *relation to meaning*, not a second recogniser, or soundness becomes a
   differential test between your own implementations. **[RE]**
10. Anchor independence to an artifact you did not write, and measure it; don't argue it. **[ED]**
11. The return-type-witness trick that eases totality/canonicity *inverts the arrow* for
    soundness-against-a-spec — do not carry the conclusion in the parser's type. **[RE]**
12. Log rejected shortcuts with reasons; the negative decisions are the load-bearing ones a reviewer
    can't otherwise see. **[RE]**
13. "Reusable lemma" is a hypothesis: `roundtrip_value`'s assembly lemmas were canonical-specific and
    silently narrower than needed — audit reuse against the *general* case. **[RE]**
14. When a generated induction principle explodes (31 premises), a hand-chosen induction (length) can
    be smaller and Mathlib-free. **[RE]**
15. `simp_all` destroys equation-compiler unreachability hypotheses; discharge unreachable branches
    before it. **[RE]**
16. A proof that only exists in the working tree is not a result — commit and gate it; the audit
    caught adequacy uncommitted and CI-invisible. **[RE]**
17. Gates coupled to a broad file glob rot when the tree grows: the theorem-count gate silently died
    when the spec chain landed. Scope gates to what they attest. **[RE]**
18. Generate human-facing result summaries *from the compiler* (`#check`/`#print axioms`) and
    byte-compare, so claims can't drift from proofs. **[RE]**
19. State the residual circularity explicitly: value semantics anchored to your own design is still a
    design choice, not an external fact. **[RE]**
20. Estimate proof effort from an analogous prior proof: the 2,000–2,500-line prediction landed at
    2,509. **[RE]**

---

*End of synthesis. Read-only; no repository file other than this one was created or modified.*
