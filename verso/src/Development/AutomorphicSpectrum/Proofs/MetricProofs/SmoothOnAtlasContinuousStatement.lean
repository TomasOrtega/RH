import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnAtlasContinuous
import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PositionPot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FSmoothOnAtlasContinuous.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.smooth_on_atlas_continuous : ∀ (e : ℕ) (X : Type) [TopologicalSpace X] (A : ReciprocityTheory.AnForm.M.FinHolAtlas e X) (f : X → ℝ), A.Smooth f → Continuous f := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | exact GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth | (intros; apply GlobalTheory.CompanionTheory.Ar.AtlasSmooth.continuous_of_atlas_smooth <;> assumption)
