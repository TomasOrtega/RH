import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumHeightChangeModel
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FPowerSumHeightChangeModel.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.power_sum_height_change_model : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) (R : SecondRoots M) (II : IntersectionSystem), IsIntersectionSystem II → ∀ (S : Finset Nat.Primes) (j : ℕ) (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), R.IsChange S → R.LocalAtPlaces j S φ → ∀ t : ℝ, 0 < t → ∀ (τ : Ψ) (k : ℕ), 1 ≤ k → k ≤ N → ∀ Q : RP Ψ N, Q.IsHomogeneous (dimFl Ψ N + 1 - k) → M.arFun II t (toA (pk τ k * Q)) = R.model.arFun II t (toA (pk τ k * Q)) + ∑ p ∈ S, Real.log (p : ℕ) * M.geoFun (toA (bracket j (φ p) p k τ * Q)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change | exact GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.power_sum_height_model_change <;> assumption)
