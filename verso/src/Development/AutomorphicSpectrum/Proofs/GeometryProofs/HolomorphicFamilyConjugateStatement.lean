import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HolomorphicFamilyConjugate
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUniqueLeftBasisCoordsAdicCompletion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.NineStatements GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GlobalTheory.CompanionTheory.Ar.Cusp.FamEx
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHolomorphicFamilyConjugate.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.holomorphic_family_conjugate : ∀ (X : Scheme.{0}) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsHolTo B y → IsHolTo (star ⁻¹' B) (fun b => spMap (starRingEnd ℂ) ≫ y (star b)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | exact GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FamEx.isHolTo_conj <;> assumption)
