import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsGroupDictionary
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FExistsGroupDictionary.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.T.exists_group_dictionary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (H : Host E) (F : UnivFam E Ψ j j' n g Λ), Nonempty (GroupDict F) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.groupDict_nonempty <;> assumption)
