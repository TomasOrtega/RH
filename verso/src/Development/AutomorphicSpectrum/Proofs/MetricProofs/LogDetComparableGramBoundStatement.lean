import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogDetComparableGramBound
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.InFlagDomainOne
open Matrix GlobalTheory.CompanionTheory.Ar.PB
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogDetComparableGramBound.lean&line=38#L38)
-/
theorem _root_.GlobalTheory.T.gram_log_unitary_triangular_invariance : ∀ (N : ℕ) (hd : Fin N → ℝ) (k : ℕ) (g u b : Matrix (Fin N) (Fin N) ℂ), (gramOf hd u = diagonal (fun i => ((hd i : ℝ) : ℂ)) → gramLog hd k (u * g) = gramLog hd k g) ∧ (b.BlockTriangular id → IsUnit b.det → (gramHead hd k g).det ≠ 0 → gramLog hd k (g * b) = gramLog hd k g + ∑ a : Fin N, if (a : ℕ) < k then Real.log ‖b a a‖ else 0) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | exact GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.gramLog_inv <;> assumption)
