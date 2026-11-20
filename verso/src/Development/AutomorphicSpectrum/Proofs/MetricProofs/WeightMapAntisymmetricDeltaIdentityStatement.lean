import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.WeightMapAntisymmetricDeltaIdentity
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.PairRelationOfScaledRatio
import GroundTheory.HeightsAndTheta.Heights.Antisymmetric.Statements
open MvPolynomial GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FWeightMapAntisymmetricDeltaIdentity.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.vandermonde_product_weight_positive : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (Q : MvPolynomial (Ψ × Fin N) ℝ) (v : ℝ), (∀ c : Ψ × Fin N → ℝ, eval c Q = v * ∏ τ : Ψ, ∏ i : Fin N, ∏ l ∈ Finset.Ioi i, ∑ m ∈ Finset.Ico i l, c (τ, m)) → toWt Q = C v * antisymDelta Ψ N ∧ 0 < eval (rhoWt Ψ N) (antisymDelta Ψ N) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | exact GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.toWt_eq_C_mul_antisymDelta <;> assumption)
