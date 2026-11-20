import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TangentVectorLiftsOpenImmersion
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FTangentVectorLiftsOpenImmersion.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.tangent_vector_lifts_open_immersion : ∀ (A T : Scheme.{0}) (φ : A ⟶ T) [IsOpenImmersion φ] (g : ℕ) (W : (Fin g → ℂ) → (Sp ℂ ⟶ A)) (y : Fin g → ℂ) (v : Sp (DualNumber ℂ) ⟶ T), IsDerivAt0 (fun x => W x ≫ φ) y v → ∃ v' : Sp (DualNumber ℂ) ⟶ A, v' ≫ φ = v ∧ IsDerivAt0 W y v' := by
  first | exact @GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion | exact GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion | (intros; apply GlobalTheory.CompanionTheory.Ggeo.DOpen.isDerivAt0_lift_of_isOpenImmersion <;> assumption)
