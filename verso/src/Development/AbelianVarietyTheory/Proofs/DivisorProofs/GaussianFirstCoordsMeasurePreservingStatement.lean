import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianFirstCoordsMeasurePreserving
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFirstCoords
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import ReciprocityTheory.SemistableReduction.SJCoreA
open MeasureTheory Set MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory.SphereMeanDrop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGaussianFirstCoordsMeasurePreserving.lean&line=122#L122)
-/
theorem _root_.GlobalTheory.T.gaussian_first_coords_measure_preserving : ∀ (N n : ℕ) (h : N ≤ n), MeasurePreserving (firstCoords h) (gaussProb n) (gaussProb N) := by
  first | exact @GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | exact GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb | (intros; apply GlobalTheory.GaussMarginal.measurePreserving_firstCoords_gaussProb <;> assumption)
