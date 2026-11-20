import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.CmFieldSmallIntegralBasis
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FCmFieldSmallIntegralBasis.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.cm_field_small_integral_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ a : Fin (Module.finrank ℚ E) → 𝓞 E, LinearIndependent ℚ (fun i => (a i : E)) ∧ ∀ i (σ : E →+* ℂ), ‖σ (a i)‖ ≤ Module.finrank ℚ E * hostRd E := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le | exact GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.exists_full_family_conjugates_le <;> assumption)
