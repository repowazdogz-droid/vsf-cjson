# CHANGELOG

## v1.0.0 — release

**GAP-1 closed.** The structural canonicity lifting is now proven, and with it the headline
theorem, unconditionally:

```lean
theorem parseDoc_idempotent : parseDoc s = some v → parseDoc (serialize v) = some v
```

### How
Not by the 26-premise `parseValue.induct` principle (attempted, abandoned in v0.x), but by
strengthening the parser's **return type** — the same device that already gave fuel-free
totality:

```lean
abbrev Res (α : Type) (P : α → Prop) (s : List UInt8) : Type :=
  Option { p : α × List UInt8 // p.2.length < s.length ∧ P p.1 }

def parseValue (depth : Nat) (s : List UInt8) :
    Res JSON (fun v => JSON.Canonical v ∧ jdepth v ≤ nestingLimit - depth) s
```

The obligation is discharged at ~8 construction sites; `parseDoc_canonical` and
`parseDoc_depth` are projections. Both invariants are `Prop`s and are **erased at runtime**.

### Behaviour: unchanged
Verified, not assumed. The entire measurement suite was re-run after the change and reproduces
**byte-for-byte**: JSONTestSuite 297/318 and 317/318; fuzz 116,476/120,000; idempotence 0
violations.

### Build-integrity bug found and fixed
`Cjson.lean` imported only `Basic`/`Parser`/`Printer`, so **`lake build` was not building the
proof modules at all** — a reviewer running it would have checked zero theorems and seen a green
light. Stale `.olean` files were masking four broken rewrites. The proof modules are now in the
default target (so `lake build` *fails* if any theorem breaks), and `verify.sh` builds from a
clean `.lake/`.

This was the fourth instrument failure of the project and the most dangerous kind: it
manufactured **false confidence** rather than a false alarm.

### Publication artifact
Added `README.md`, `CLAIMS.md` (PROVEN / MEASURED / OBSERVED / NOT PROVEN), `RESULTS.md`,
`GAPS.md`, `REPRODUCE.md`, `PAPER.md`, `figures/` (generated from the result JSON), and
`verify.sh` (regenerates and re-checks every claim; fails if any recorded number moved).

### Still open
* **GAP-2** — soundness against the SPEC grammar. **No theorem here constrains which inputs the
  parser accepts**, and that is most of what SPEC.md says. Highest-value next step.
* **GAP-EXTRACT** — the compiled binary is not the verified object.
* **GAP-3** — no exponent bound (the one finding against our own port).

## v0.x — pre-release
Phases 0–4: oracle vendored, SPEC written and oracle-verified, Lean port, differential testing,
proofs of totality / round-trip / number-canonicity. GAP-1 and GAP-2 shipped open and honest.
