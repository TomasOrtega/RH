import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsMulHeightMinpolyCoeffLeRelativeHeight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsMulHeightMinpolyCoeffLeRelativeHeight.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_mulHeight_minpoly_coeff_le_relativeHeight : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], ∃ (c : ℝ) (a : ℕ), ∀ (x : E) (j : ℕ), Height.mulHeight₁ ((minpoly F x).coeff j) ≤ c * (GlobalTheory.RatCount.htE F x : ℝ) ^ a := by
  first | exact @GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | exact GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le | (intros; apply GlobalTheory.RatCount.CoefHt.exists_mulHeight_coeff_minpoly_le <;> assumption)
