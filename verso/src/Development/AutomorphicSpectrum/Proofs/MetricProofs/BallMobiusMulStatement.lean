import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.BallMobiusMul
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FBallMobiusMul.lean&line=124#L124)
-/
theorem _root_.GlobalTheory.T.ball_mobius_mul : ∀ (Ψ : Type) [Fintype Ψ] (j j' n : ℕ) (q : Ψ × Fin j × Fin j' ≃ Fin n) (u v : Ψ → Matrix (Sg j j') (Sg j j') ℂ), (∀ τ, IsSgU (u τ)) → (∀ τ, IsSgU (v τ)) → ∀ t ∈ ballDom q, moebBall q (fun τ => u τ * v τ) t = moebBall q u (moebBall q v t) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | exact GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.Dict.MoebAct.moebBall_mul <;> assumption)
