import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.GaussianMatrixMeasurePosFinite
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsScaleStable
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FGaussianMatrixMeasurePosFinite.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.gaussian_matrix_measure_pos_finite : ∀ m n : ℕ, 0 < gaussM m n Set.univ ∧ gaussM m n Set.univ < ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | exact GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top | (intros; apply GlobalTheory.CompanionTheory.Ar.Short.Crofton.gaussM_univ_pos_lt_top <;> assumption)
