import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierCoefficientHolomorphicInBase
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChSingle
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.FamilyFourier
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFourierCoefficientHolomorphicInBase.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.fourier_coefficient_holomorphic_in_base : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set E} (h : Pt E g → ℂ), IsOpen U → DifferentiableOn ℂ h (cov U g) → ∀ n : Fin g → ℤ, DifferentiableOn ℂ (coef h n) U := by
  first | exact @GlobalTheory.differentiableOn_coef_of_holomorphic | exact GlobalTheory.differentiableOn_coef_of_holomorphic | (intros; apply GlobalTheory.differentiableOn_coef_of_holomorphic <;> assumption)
