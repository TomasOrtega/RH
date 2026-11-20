import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HaarPushforwardEqBallDensity
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FHaarPushforwardEqBallDensity.lean&line=470#L470)
-/
theorem _root_.GlobalTheory.T.haar_pushforward_eq_ball_density : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (Δ : GroupDict F) (μ : Measure (archUnitary Δ.h (Pi.basisFun E (Fin (j + j'))))) [μ.IsHaarMeasure], ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map Δ.π = c • (volume.restrict (ballDom F.q)).withDensity fun t => ENNReal.ofReal (ballDens F.q t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | exact GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.DictMeas.haar_projects <;> assumption)
