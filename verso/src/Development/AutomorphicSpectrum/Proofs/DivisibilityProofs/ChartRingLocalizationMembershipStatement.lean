import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ChartRingLocalizationMembership
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Cartier
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsCompactUnitaryPointsAtPlaceFstMemCompact
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FChartRingLocalizationMembership.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.chart_ring_localization_membership : ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (y : (Σ k, ι k) → Ω) (A : Type) [CommRing A] [Algebra A Ω], HasConstants ℤ A y → ∀ (m : Ideal A) [m.IsPrime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (c : ∀ k, ι k), segreVec y c ≠ 0 → ∀ t : Ω, t ∈ chartRing O (segreVec y) c ↔ ∃ s : A, s ∉ m ∧ algebraMap A Ω s * t ∈ chartRing ℤ (segreVec y) c := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | exact GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.mem_chartRing_atPrime_iff <;> assumption)
