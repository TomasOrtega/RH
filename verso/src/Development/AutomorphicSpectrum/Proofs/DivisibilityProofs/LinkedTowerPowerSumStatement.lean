import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LinkedTowerPowerSum
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FLinkedTowerPowerSum.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.linked_tower_power_sum : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (T : RootTower Ψ N) (II : IntersectionSystem), IsIntersectionSystem II → T.Proportional → ∀ φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ), LinkedTower T II φ → T.Prop6 II fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower | exact GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.power_sum_term_linked_tower <;> assumption)
