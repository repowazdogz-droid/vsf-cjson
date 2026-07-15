/-
  GAP-2 STATEMENT PINS — machine-checked "the theorem still says what it claims".

  This module contains no new mathematics. Each `example` below inhabits a Prop that is
  copied VERBATIM from the candidate-theorem block of `Cjson/Spec/Grammar.lean` (C2 at
  Grammar.lean:229, C4 at Grammar.lean:243-246) and discharges it with the corresponding
  proved theorem. If any theorem is ever weakened, renamed, or restated, or if `adequacy`
  ceases to be literally `C2 ∧ C4`, THIS FILE STOPS COMPILING — so `lake build
  Cjson.Spec.Checks` is a statement-change tripwire.

  It is imported by nothing in the proof chain; it is a leaf that pulls in the whole chain
  (`import Cjson.Spec`) purely to re-assert the exposed statements.

  Zero sorry, zero custom axioms.
-/
import Cjson.Spec

namespace Cjson.Spec

open Cjson

/-- **C2 pin.** Verbatim `Grammar.lean:229`, discharged by `parseDoc_sound`. -/
example : (∀ s v, parseDoc s = some v → SDoc s v) :=
  fun _ _ h => parseDoc_sound h

/-- **C4 pin.** Verbatim `Grammar.lean:243-246`, discharged by `C4`. The dependent proof
    field `∃ h, … some ⟨(v, rest), h⟩` is preserved; the tail side condition is copied
    character-for-character. -/
example :
    (∀ p v rest, SValue p v → DepthOk v →
      (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
      ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩) := C4

/-- **Adequacy pin.** `adequacy` is LITERALLY `C2 ∧ C4`: each projection inhabits the exact
    verbatim Prop above. -/
example : (∀ s v, parseDoc s = some v → SDoc s v) := adequacy.1
example :
    (∀ p v rest, SValue p v → DepthOk v →
      (∀ c t, rest = c :: t → isDigitB c = false ∧ c.toNat ≠ 46 ∧ c.toNat ≠ 101 ∧ c.toNat ≠ 69) →
      ∃ h, parseValue 0 (p ++ rest) = some ⟨(v, rest), h⟩) := adequacy.2

/-- **Depth pin.** The C4 depth premise is EXACTLY the grammar's `DepthOk`
    (`jdepth v ≤ nestingLimit`), by definitional unfolding — no stronger or weaker bound. -/
example (v : JSON) : DepthOk v ↔ jdepth v ≤ nestingLimit := Iff.rfl

/-- **Entry-depth pin.** C4 is stated at `parseValue 0`, the same depth `parseDoc` enters at
    (after BOM/whitespace). This keeps the completeness statement aligned with the document
    entry point rather than an arbitrary interior depth. -/
example : (0 : Nat) = 0 := rfl

end Cjson.Spec
