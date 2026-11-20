import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BallAverageFibreCount
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSigmaCompactConeInter
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FibreCountRotationInvariantStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MeasurableFibreCountOverStatement
set_option maxSynthPendingDepth 1
open GroundTheory.Heights₂.Heights MeasureTheory MvPolynomial Matrix GlobalTheory.CompanionTheory.Ar.Short.Crofton
open scoped ENNReal

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FBallAverageFibreCount.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.ball_average_fibre_count : ∀ (n e : ℕ) (S : Set (EuclideanSpace ℂ (Fin n))), IsScaleStable S → IsSigmaCompact S →
  ∀ T : ℝ≥0∞ → ℝ≥0∞, Measurable T →
    ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π *
        ∫⁻ w in (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1), T (cntOver S π w) =
      volume (Metric.ball (0 : EuclideanSpace ℂ (Fin (e + 1))) 1) *
        ∫⁻ π : Fin (e + 1) → Fin n → ℂ, matGauss π * T (cntOver S π (firstCoordVec (e + 1))) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | exact GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count | (intros; apply GlobalTheory.CompanionTheory.Relay.ball_average_fibre_count <;> assumption)
