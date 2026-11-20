import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LimitHeightConstantShift
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FLimitHeightConstantShift.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.limit_height_constant_shift : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M M' : RootModel Ψ N) (II : IntersectionSystem), M.Converges II → M'.Converges II → ∀ (F : RPA Ψ N) (c : ℝ), (∀ t : ℝ, 0 < t → M.arFun II t F = M'.arFun II t F + c) → M.PP II F = M'.PP II F + c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | exact GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PP_eq_add_of_arFun_eq_add <;> assumption)
