import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularCompletionFlat
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RegularCompletionPackage.exists_regular_completion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsRegularCompletionFlat.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.exists_regular_completion_flat : ∀ (R₁ Ω : Type) [CommRing R₁] [IsRegularLocalRing R₁] [Field Ω] (u : R₁ →+* Ω), RingHom.ker u = maximalIdeal R₁ → ∃ (C : Type) (_ : CommRing C) (_ : IsRegularLocalRing C) (c : R₁ →+* C) (uC : C →+* Ω), c.Flat ∧ (maximalIdeal R₁).map c = maximalIdeal C ∧ IsAdicComplete (maximalIdeal C) C ∧ RingHom.ker uC = maximalIdeal C ∧ uC.comp c = u := by
  first | exact @GlobalTheory.RegularCompletionPackage.exists_regular_completion | exact GlobalTheory.RegularCompletionPackage.exists_regular_completion | (intros; apply GlobalTheory.RegularCompletionPackage.exists_regular_completion <;> assumption)
