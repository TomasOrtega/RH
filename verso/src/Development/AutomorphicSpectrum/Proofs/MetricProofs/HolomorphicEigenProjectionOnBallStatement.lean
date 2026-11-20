import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicEigenProjectionOnBall
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PPartRealSmul
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FHolomorphicEigenProjectionOnBall.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.holomorphic_eigen_projection_on_ball : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ) (C : LatEmb F) (τ : Ψ) (y : Fin (j + j') → ℂ), DifferentiableOn ℂ (fun t => C.pPart (F.R t) τ y) (ballDom F.q) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_differentiableOn | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_differentiableOn | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.Chart.pPart_differentiableOn <;> assumption)
