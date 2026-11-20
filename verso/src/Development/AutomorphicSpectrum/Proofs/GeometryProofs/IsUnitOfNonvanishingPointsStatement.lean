import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfNonvanishingPoints
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenPtSpecializesOfSpecializes
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.UnLocal
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.UnitAtDivOfIsGenAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.PullbackSections
open GlobalTheory.CompanionTheory.Ar.Flat.GagaC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsUnitOfNonvanishingPoints.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.is_unit_of_nonvanishing_points : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (U : X.Opens) (a : Γ(X, U)), LocallyOfFiniteType s → (∀ x : Sp ℂ ⟶ X, x ≫ s = 𝟙 _ → centre x ∈ U → valAt' x U a ≠ 0) → IsUnit a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint | exact GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.GagaC.isUnit_of_forall_complexPoint <;> assumption)
