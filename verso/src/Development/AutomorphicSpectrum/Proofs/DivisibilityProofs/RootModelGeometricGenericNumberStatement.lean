import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelGeometricGenericNumber
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FRootModelGeometricGenericNumber.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.root_model_geometric_generic_number : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsIntersectionSystem II → ∀ (F : RP Ψ N), F.IsHomogeneous (dimFl Ψ N) → M.geoFun (toA F) = genNum ℚ (extTo ℚ M.P) M.xdeg F [] / (M.δ : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq | exact GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.GeoModel.geoFun_toA_eq <;> assumption)
