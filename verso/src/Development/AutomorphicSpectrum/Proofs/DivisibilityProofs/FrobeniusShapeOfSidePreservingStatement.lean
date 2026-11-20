import Mathlib
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FrobeniusShapeOfSidePreserving
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
Apply `GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FDivisibilityProofs%2FFrobeniusShapeOfSidePreserving.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.frobenius_shape_of_side_preserving : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (φ : ℕ → Equiv.Perm (Ψ ⊕ Ψ)), (∀ p, (∀ σ, (φ p σ).isLeft = σ.isLeft) ∨ ∀ σ, (φ p σ).isLeft = σ.isRight) → FrobShape fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ : Ψ ⊕ Ψ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side | exact GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.frobShape_of_side <;> assumption)
