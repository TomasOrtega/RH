import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralHeckeMellinGaussIntegrandEqProdGamma
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.CompletedLStripBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormWt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GammaIntegralExpSubstitutionRealLineStatement
open NumberField MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeMellinProd.mellin_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralHeckeMellinGaussIntegrandEqProdGamma.lean&line=77#L77)
-/
theorem _root_.GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by
  first | exact @GlobalTheory.HeckeMellinProd.mellin_prod | exact GlobalTheory.HeckeMellinProd.mellin_prod | (intros; apply GlobalTheory.HeckeMellinProd.mellin_prod <;> assumption)
