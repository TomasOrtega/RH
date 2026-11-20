import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteAndNcardMinpolyCoeffHeightLe
import Mathlib

open NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFiniteAndNcardMinpolyCoeffHeightLe.lean&line=194#L194)
-/
theorem _root_.GlobalTheory.T.finite_and_ncard_minpoly_coeff_height_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (C : ℝ) (k : ℕ), ∀ B : ℝ, 1 ≤ B → {x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.Finite ∧ (({x : E | ∀ j, Height.mulHeight₁ ((minpoly F x).coeff j) ≤ B}.ncard : ℕ) : ℝ) ≤ C * B ^ k := by
  first | exact @GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | exact GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le | (intros; apply GlobalTheory.MinpolyHeightCount.finite_and_ncard_minpoly_height_le <;> assumption)
