import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianRadialLawProbabilityLogIntegrableMean
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SphereMeanDrop.radProb_log_mean` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianRadialLawProbabilityLogIntegrableMean.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.gaussianRadialLawProbability_log_integrable_mean : ∀ (n : ℕ), 0 < n → IsProbabilityMeasure (radProb n) ∧ Integrable (fun r : Ioi (0:ℝ) => Real.log r) (radProb n) ∧ ∫ r, Real.log (r : ℝ) ∂(radProb n) = radK (2 * n - 1) / radJ (2 * n - 1) := by
  first | exact @GlobalTheory.SphereMeanDrop.radProb_log_mean | exact GlobalTheory.SphereMeanDrop.radProb_log_mean | (intros; apply GlobalTheory.SphereMeanDrop.radProb_log_mean <;> assumption)
