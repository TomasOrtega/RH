import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock

open MeasureTheory Matrix

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ghom_factors_through_det` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGlCharacterFactorsThroughDetOfTwoNeZero.lean&line=123#L123)
-/
theorem _root_.GlobalTheory.T.glCharacter_factors_through_det_of_two_ne_zero : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  first | exact @GlobalTheory.ghom_factors_through_det | exact GlobalTheory.ghom_factors_through_det | (intros; apply GlobalTheory.ghom_factors_through_det <;> assumption)
